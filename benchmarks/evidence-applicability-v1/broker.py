"""In-memory allowlisted reference broker and strict native-usage accumulator."""
from __future__ import annotations

import json
import math
import re
import time
from collections import Counter


class LimitReached(RuntimeError):
    pass


def wire(value):
    return json.dumps(value, ensure_ascii=False, separators=(",", ":"))


def pages(text, maximum=11000):
    """Split at UTF-8 boundaries; every returned codepoint occurs exactly once."""
    if maximum < 4:
        raise ValueError("page ceiling must fit a UTF-8 codepoint")
    result, current, size = [], [], 0
    for char in text:
        count = len(char.encode("utf-8"))
        if size + count > maximum:
            result.append("".join(current)); current = []; size = 0
        current.append(char); size += count
    result.append("".join(current))
    return result


class Broker:
    """Own one presentation; never expose the other presentation or a filesystem.

    Capabilities are reference IDs, not paths. Every attempted invocation counts.
    Once a limit is reached the controller must stop the model turn, not retry.
    """
    def __init__(self, inventory, texts, *, max_calls=8, max_bytes=48000,
                 seconds=300, clock=time.monotonic):
        if set(texts) != {u["id"] for u in inventory}:
            raise ValueError("inventory and presentation do not match")
        self.inventory = inventory
        self.sources = {u["id"]:u.get("source") for u in inventory}
        self.texts = dict(texts)
        self.max_calls, self.max_bytes, self.seconds = max_calls, max_bytes, seconds
        self.clock, self.started = clock, clock()
        self.calls, self.bytes, self.log = 0, 0, []
        self.index = {u["id"]:set(re.findall(r"[a-z0-9]+",u["search_text"].lower())) for u in inventory}
        self.titles = {u["id"]:set(re.findall(r"[a-z0-9]+",u["title"].lower())) for u in inventory}
        self.df = Counter(term for tokens in self.index.values() for term in tokens)

    def call(self, tool, arguments):
        self.calls += 1
        event = {"number":self.calls,"tool":tool,"arguments":arguments,
                 "elapsed_seconds":round(self.clock()-self.started,6)}
        self.log.append(event)
        if self.calls > self.max_calls or self.clock()-self.started >= self.seconds:
            event.update(status="limit",returned_bytes=0)
            raise LimitReached("call or time limit")
        try:
            if not isinstance(arguments,dict):
                raise ValueError("arguments must be an object")
            if tool == "search":
                if set(arguments) != {"query"} or not isinstance(arguments["query"],str) or len(arguments["query"]) > 500:
                    raise ValueError("search requires only query, a string of at most 500 characters")
                tokens = set(re.findall(r"[a-z0-9]+",arguments["query"].lower()))
                scores = {ref:sum(math.log(1+len(self.inventory)/self.df[t]) for t in sorted(tokens & terms))
                          for ref,terms in self.index.items()}
                # Shared ranking: title overlap, logical records before raw rows,
                # then IDF body score and stable ID. No task-specific boosts.
                matches = sorted((u for u in self.inventory if scores[u["id"]]>0),key=lambda u:(
                    -len(tokens & self.titles[u["id"]]), u.get("granularity")=="row",
                    -scores[u["id"]],u["id"]))[:5]
                response={"results":[{"reference":u["id"],"title":u["title"]} for u in matches]}
                ceiling=4000
            elif tool == "read":
                if set(arguments) != {"reference","page"}:
                    raise ValueError("read requires only reference and page")
                ref,page=arguments["reference"],arguments["page"]
                if not isinstance(ref,str) or ref not in self.texts:
                    raise ValueError("unknown reference")
                if type(page) is not int or page < 0:
                    raise ValueError("page must be a nonnegative integer")
                chunks=pages(self.texts[ref])
                if page >= len(chunks):
                    raise ValueError("page outside reference")
                response={"reference":ref,"page":page,"pages":len(chunks),
                          "next_page":page+1 if page+1<len(chunks) else None,"text":chunks[page]}
                if self.sources[ref] is not None:
                    response["source"] = self.sources[ref]
                # Count UTF-8 reference text plus provenance/control metadata.
                # JSON escaping of the text is measured separately as transport bytes.
                ceiling=12000
            else:
                raise ValueError("unknown tool")
            status="ok"
        except ValueError as error:
            response={"error":str(error)}; status="denied"; ceiling=4000
        encoded=wire(response)
        count=(len(response["text"].encode("utf-8")) + len(wire({k:v for k,v in response.items() if k!="text"}).encode("utf-8"))
               if "text" in response else len(encoded.encode("utf-8")))
        if count > ceiling or self.bytes+count > self.max_bytes:
            event.update(status="limit",returned_bytes=0)
            raise LimitReached("returned text byte limit")
        self.bytes += count
        event.update(status=status,returned_bytes=count,transport_bytes=len(encoded.encode("utf-8")),response=response)
        return response


class Usage:
    FIELDS=("inputTokens","cachedInputTokens","outputTokens","reasoningOutputTokens","totalTokens")
    def __init__(self, thread_id, turn_id, soft_limit):
        self.thread_id,self.turn_id,self.soft_limit=thread_id,turn_id,soft_limit
        self.updates=[]

    def add(self, params):
        if params.get("threadId") != self.thread_id or params.get("turnId") != self.turn_id:
            raise ValueError("foreign usage event")
        total=params.get("tokenUsage",{}).get("total")
        if not isinstance(total,dict) or any(type(total.get(k)) is not int or total[k]<0 for k in self.FIELDS):
            raise ValueError("missing or malformed usage")
        if total["totalTokens"] != total["inputTokens"]+total["outputTokens"]:
            raise ValueError("usage total disagrees with input plus output")
        if total["cachedInputTokens"]>total["inputTokens"] or total["reasoningOutputTokens"]>total["outputTokens"]:
            raise ValueError("usage subsets exceed totals")
        if self.updates and any(total[k]<self.updates[-1][k] for k in self.FIELDS):
            raise ValueError("usage decreased")
        self.updates.append(dict(total))
        return total["totalTokens"] >= self.soft_limit

    def result(self):
        # Cumulative notifications must not be summed. None never means zero.
        return self.updates[-1] if self.updates else None


TOOLS=[
 {"type":"function","name":"search","description":"Search the permitted reference collection. Returns at most five neutral reference IDs and titles.",
  "inputSchema":{"type":"object","properties":{"query":{"type":"string"}},"required":["query"],"additionalProperties":False}},
 {"type":"function","name":"read","description":"Read one page of a permitted reference. Page numbers begin at zero. Unknown references are denied.",
  "inputSchema":{"type":"object","properties":{"reference":{"type":"string"},"page":{"type":"integer","minimum":0}},"required":["reference","page"],"additionalProperties":False}},
]
