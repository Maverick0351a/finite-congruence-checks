"""Read-only native runner probe; fail closed before inference.

This version deliberately has NO turn/start implementation. The installed
app-server has no exhaustive pre-inference tool manifest/exclusive allowlist.
Synthetic broker/usage tests run separately. Never load benchmark packets here.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import queue
import re
import subprocess
import threading
import time
import tomllib

from semantic_broker import TOOLS

DISABLED = ("shell_tool", "unified_exec", "apps", "plugins", "remote_plugin",
            "hooks", "memories", "external_agent_memory_import", "multi_agent",
            "multi_agent_v2", "agent_message_board", "code_mode", "code_mode_host")
ALLOWED_RPC = {"initialize", "account/read", "config/read", "configRequirements/read",
               "model/list", "thread/start", "mcpServerStatus/list", "hooks/list", "skills/list"}


def sha(raw): return hashlib.sha256(raw).hexdigest()


def required_field(obj, key, kind):
    """Absent telemetry is not evidence of an empty inventory or fresh context."""
    if not isinstance(obj, dict) or key not in obj or type(obj[key]) is not kind:
        raise ValueError(f"missing or invalid native field: {key}")
    return obj[key]


def prior_turn_count(thread):
    return len(required_field(thread, "turns", list))


def mcp_page_inventory(page):
    data = required_field(page, "data", list)
    if "nextCursor" not in page or (page["nextCursor"] is not None and type(page["nextCursor"]) is not str):
        raise ValueError("missing or invalid native field: nextCursor")
    servers = [{"name": required_field(server, "name", str),
                "tool_count": len(required_field(server, "tools", dict)),
                "runtime_status": server.get("runtimeStatus"),
                "discovery_error_present": "toolsError" in server and server["toolsError"] is not None,
                "discovery_error_sha256": sha(str(server["toolsError"]).encode()) if server.get("toolsError") is not None else None,
                "catalog_status": "returned" if "toolsError" in server and server["toolsError"] is None else "unverified"}
               for server in data]
    return servers, page["nextCursor"]


def mcp_absence_status(servers):
    if any(s["tool_count"] for s in servers): return "failed"
    if any(s["catalog_status"] != "returned" or s["runtime_status"] != "connected" for s in servers):
        return "unverified"
    return "passed"


def settings(config_path):
    if not config_path.exists(): return {}, None
    raw = config_path.read_bytes()
    parsed = tomllib.loads(raw.decode("utf-8"))
    # Keep only names needed to disable configured MCP servers. Never copy auth,
    # URLs, commands, environment values, or plugin configuration into the log.
    return {"mcp_names": list(parsed.get("mcp_servers",{}))}, sha(raw)


class Client:
    def __init__(self, command, cwd):
        env=dict(os.environ)
        for key in ("CODEX_THREAD_ID", "CODEX_SESSION_ID", "CODEX_TOOL_CALL_ID",
                    "CODEX_APP_TOOLS_PIPE_PATH", "CODEX_INTERNAL_ORIGINATOR_OVERRIDE",
                    "OPENAI_API_KEY", "OPENAI_BASE_URL"):
            env.pop(key,None)
        self.process=subprocess.Popen(command,stdin=subprocess.PIPE,stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,text=True,encoding="utf-8",cwd=cwd,env=env)
        self.queue=queue.Queue(); self.events=[]; self.rpc=[]; self.stderr=[]; self.serial=0
        self.started=time.monotonic()
        def read_stdout():
            for line in self.process.stdout:
                try: self.queue.put(json.loads(line))
                except json.JSONDecodeError: self.queue.put({"malformed_output_sha256":sha(line.encode())})
            self.queue.put({"eof":True})
        def read_stderr():
            for line in self.process.stderr:
                # Digest diagnostic lines; do not publish potentially credentialed logs.
                item={"bytes":len(line.encode()),"sha256":sha(line.encode())}
                if line.lower().startswith(("error", "unknown feature", "failed")):
                    safe=re.sub(r"(?i)(bearer\s+|sk-[a-z0-9_-]*|(?:token|secret|api_key)\s*[=:]\s*)\S+", "[redacted]",line.strip())
                    item["diagnostic"]=safe[:1200]
                self.stderr.append(item)
        self.workers=[threading.Thread(target=read_stdout,daemon=True),threading.Thread(target=read_stderr,daemon=True)]
        for worker in self.workers: worker.start()

    def send(self, obj):
        self.process.stdin.write(json.dumps(obj)+"\n"); self.process.stdin.flush()

    def call(self, method, params, timeout=20):
        if method not in ALLOWED_RPC: raise ValueError("RPC not in non-inference allowlist")
        self.serial+=1; ident=self.serial
        self.rpc.append({"method":method,"id":ident})
        self.send({"id":ident,"method":method,"params":params})
        end=min(time.monotonic()+timeout,self.started+150)
        while time.monotonic()<end:
            try: message=self.queue.get(timeout=max(0.001,end-time.monotonic()))
            except queue.Empty: break
            if message.get("id")==ident and "method" not in message:
                if "error" in message:
                    # Error strings may embed environment paths/config values; retain
                    # their digest and error code without echoing arbitrary content.
                    self.rpc[-1].update(status="error",code=message["error"].get("code"),error_sha256=sha(json.dumps(message["error"]).encode()))
                    raise RuntimeError(f"{method} returned error code {message['error'].get('code')}")
                self.rpc[-1]["status"]="ok"
                return message.get("result")
            if "method" in message and "id" in message:
                self.send({"id":message["id"],"error":{"code":-32601,"message":"No server-initiated capability is authorized during preflight"}})
                self.events.append({"method":message["method"],"status":"denied_server_request"})
            elif "method" in message:
                self.events.append({"method":message["method"]})
            elif message.get("eof"):
                raise RuntimeError("app-server closed stdout")
            else:
                self.events.append({"unexpected_message_sha256":sha(json.dumps(message).encode())})
        raise RuntimeError(f"{method} timed out")

    def close(self):
        if self.process.poll() is None: self.process.terminate()
        try: self.process.wait(timeout=5)
        except subprocess.TimeoutExpired: self.process.kill(); self.process.wait(timeout=5)
        for worker in self.workers: worker.join(timeout=2)


def probe(executable, output):
    output.mkdir(parents=True,exist_ok=False)
    empty=output/"empty-working-directory"; empty.mkdir()
    config_path=Path(os.environ.get("CODEX_HOME",Path.home()/".codex"))/"config.toml"
    names,before=settings(config_path)
    version=subprocess.check_output([executable,"--version"],text=True).strip()
    auth=subprocess.run([executable,"login","status"],capture_output=True,text=True,timeout=20)
    if auth.returncode or "Logged in using ChatGPT" not in auth.stdout+auth.stderr:
        raise RuntimeError("existing ChatGPT login required; no credential setup or API fallback")
    command=[executable,"app-server","--stdio"]
    for feature in DISABLED: command += ["--disable",feature]
    overrides={"web_search":"disabled","project_doc_max_bytes":0,"model_provider":"openai",
               "model_reasoning_effort":"medium","developer_instructions":"",
               "forced_login_method":"chatgpt"}
    for key,value in overrides.items(): command += ["-c",key+"="+json.dumps(value)]
    for name in names.get("mcp_names",[]): command += ["-c","mcp_servers."+json.dumps(name)+".enabled=false"]
    report={"kind":"non_inference_native_dummy_setup_preflight","started_utc":datetime.now(timezone.utc).isoformat(),
            "client_version":version,"command_sha256":sha(json.dumps(command).encode()),
            "requested_disabled_features":list(DISABLED),"requested_overrides":overrides,
            "configured_mcp_server_count":len(names.get("mcp_names",[])),
            "new_credentials":False,"paid_api_calls":0,"benchmark_answering_sessions":0,
            "dummy_inference_turns":0,"native_token_usage":None,
            "usage_note":"No turn/start is implemented or sent. Native token usage is unavailable, not a measured zero. Offline fixtures are not model usage.",
            "checks":{}}
    start=time.monotonic(); client=None
    try:
        client=Client(command,str(empty.resolve()))
        client.call("initialize",{"clientInfo":{"name":"semantic_dummy_preflight","version":"0.1"},"capabilities":{"experimentalApi":True}})
        client.send({"method":"initialized","params":{}})
        account=client.call("account/read",{"refreshToken":False})
        report["auth_type"]=(account.get("account") or {}).get("type")
        if report["auth_type"]!="chatgpt": raise RuntimeError("native auth is not ChatGPT")
        report["checks"]["existing_chatgpt_auth"]="passed"
        config=client.call("config/read",{"cwd":str(empty.resolve()),"includeLayers":True})
        effective=config.get("config",{})
        report["effective_config"]={key:effective.get(key) for key in overrides if key!="developer_instructions"}
        report["effective_developer_instruction_characters"]=len(effective.get("developer_instructions") or "")
        report["effective_disabled_features"]={key:effective.get("features",{}).get(key) for key in DISABLED}
        report["config_layer_count"]=len(config.get("layers") or [])
        # Full configuration is inspected only in memory; publish no secret-bearing layer.
        requirements=client.call("configRequirements/read",{})
        report["managed_requirements_present"]=bool(requirements.get("requirements"))
        models=client.call("model/list",{"limit":100})
        available=models.get("data",[])
        model=next((m.get("model") or m.get("id") for m in available if m.get("isDefault")),None)
        if not model: raise RuntimeError("no explicit default model identity returned")
        report["requested_model"]=model
        thread=client.call("thread/start",{"cwd":str(empty.resolve()),"model":model,"modelProvider":"openai",
            "allowProviderModelFallback":False,"ephemeral":True,"environments":[],"runtimeWorkspaceRoots":[],
            "sandbox":"read-only","approvalPolicy":"never","baseInstructions":"Synthetic runner preflight. Use only the supplied reference tools.",
            "developerInstructions":"This thread contains no benchmark task. No model turn is authorized by this setup probe.",
            "dynamicTools":TOOLS,"config":{"project_doc_max_bytes":0,"model_reasoning_effort":"medium"}})
        obj=thread["thread"]; tid=obj["id"]
        report["thread_id"]=tid
        report["thread_setup"]={key:thread.get(key) for key in ("model","modelProvider","approvalPolicy","sandbox","reasoningEffort")}
        report["thread_keys"]=sorted(obj)
        report["prior_turns"]=prior_turn_count(obj)
        report["instruction_sources"]=thread.get("instructionSources",obj.get("instructionSources"))
        report["environments"]=thread.get("environments",obj.get("environments"))
        report["checks"]["fresh_thread_no_prior_turns"]="passed" if report["prior_turns"]==0 else "failed"
        servers=[]; cursor=None; seen_cursors=set()
        while True:
            params={"threadId":tid,"detail":"full","limit":100}
            if cursor: params["cursor"]=cursor
            page=client.call("mcpServerStatus/list",params)
            page_servers,cursor=mcp_page_inventory(page)
            servers.extend(page_servers)
            if cursor is None: break
            if cursor in seen_cursors: raise ValueError("repeated MCP inventory cursor")
            seen_cursors.add(cursor)
        report["mcp_inventory"]=servers
        report["checks"]["mcp_tools_absent"]=mcp_absence_status(servers)
        report["checks"]["exclusive_native_tool_allowlist"]="unverified"
        report["blocking_reason"]="No exhaustive tool/prompt manifest or exclusive dynamic-tool gate is exposed by this installed app-server. Effective config and an empty MCP list do not prove absence of native tools or inherited instructions. Stop before inference."
    except Exception as error:
        report["probe_error"]={"type":type(error).__name__,"message":str(error)}
        report["checks"]["native_setup"]="failed"
    finally:
        if client:
            client.close()
            report["rpc_calls"]=client.rpc; report["notifications"]=client.events
            report["stderr_line_digests"]=client.stderr
        _,after=settings(config_path)
        report["saved_config_unchanged"]=before==after
        report["elapsed_seconds"]=round(time.monotonic()-start,3)
        report["status"]="blocked_before_inference"
        report["finished_utc"]=datetime.now(timezone.utc).isoformat()
        (output/"report.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8",newline="\n")
    return report


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--codex",required=True)
    parser.add_argument("--out",type=Path,required=True)
    parser.add_argument("--approved-session-restrictions",action="store_true")
    args=parser.parse_args()
    if not args.approved_session_restrictions: parser.error("user approval for temporary process restrictions required")
    result=probe(args.codex,args.out)
    print(json.dumps({k:result.get(k) for k in ("status","checks","probe_error","blocking_reason","elapsed_seconds","dummy_inference_turns","native_token_usage")},indent=2))
