"""Record scripted dummy broker activity without starting an answering model."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import time

from semantic_broker import Broker, LimitReached
from semantic_packets import documentation


def exercise():
    facts = [{"id":"lamp-a", "elapsed_seconds":7, "color":"amber", "scope":"one recorded trial"},
             {"id":"lamp-b", "elapsed_seconds":7, "color":"violet", "scope":"one recorded trial"}]
    inventory = [{"id":f["id"], "title":"Lamp observation " + f["id"],
                  "search_text":json.dumps(f), "source":{"fixture":f["id"]}} for f in facts]
    presentations = {"documentation":{f["id"]:documentation(f)[0] for f in facts},
                     "atlas":{f["id"]:json.dumps(f) for f in facts}}
    sessions = []
    for condition, texts in presentations.items():
        start = time.perf_counter()
        broker = Broker(inventory, texts, seconds=180, clock=time.perf_counter)
        broker.call("search", {"query":"lamp"})
        for ref in ("lamp-a", "lamp-b"):
            broker.call("read", {"reference":ref, "page":0})
        for ref in ("key.json", "other-arm/atlas.json", "prior-answer.txt", "../outside", "https://example.org"):
            result = broker.call("read", {"reference":ref, "page":0})
            if result != {"error":"unknown reference"}:
                raise AssertionError("forbidden reference was not denied")
        try:
            broker.call("read", {"reference":"lamp-a", "page":0})
        except LimitReached:
            pass
        else:
            raise AssertionError("ninth call was not blocked")
        sessions.append({"condition":condition, "kind":"scripted_broker_exercise_no_model",
                         "attempted_calls":broker.calls, "returned_responses":8, "denied_responses":5,
                         "limit_blocked_calls":1, "returned_reference_and_metadata_bytes":broker.bytes,
                         "transport_bytes":sum(e.get("transport_bytes",0) for e in broker.log),
                         "elapsed_seconds":round(time.perf_counter()-start,6),
                         "clock":"time.perf_counter",
                         "native_model_token_usage":None, "log":broker.log})
    return {"kind":"offline_scripted_dummy_preflight", "recorded_utc":datetime.now(timezone.utc).isoformat(),
            "sessions":sessions, "dummy_model_turns":0, "benchmark_answering_sessions":0,
            "native_model_token_usage":None,
            "limits":"Python broker exercise only; does not test model behavior, native context isolation, token telemetry, or asynchronous interruption."}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    report = exercise()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("x", encoding="utf-8", newline="\n") as target:
        json.dump(report, target, indent=2); target.write("\n")
    print(json.dumps([{k:v for k,v in s.items() if k!="log"} for s in report["sessions"]], indent=2))
