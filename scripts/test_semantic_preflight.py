"""Offline adversarial controls. These tests make no model/network calls."""
import copy
import json
from pathlib import Path
import unittest

from semantic_broker import Broker, LimitReached, Usage, pages
from semantic_packets import documentation, factor_trace, expand_trace, build, blob, REGISTRIES
from preflight_semantic_runner import prior_turn_count, mcp_page_inventory, mcp_absence_status


def dummy():
    facts=[{"id":"lamp-a","elapsed_seconds":7,"color":"amber","scope":"one recorded trial"},
           {"id":"lamp-b","elapsed_seconds":7,"color":"violet","scope":"one recorded trial"}]
    inventory=[{"id":f["id"],"title":"Lamp observation "+f["id"],"search_text":json.dumps(f)} for f in facts]
    atlas={f["id"]:json.dumps(f) for f in facts}
    docs={f["id"]:documentation(f)[0] for f in facts}
    return inventory,docs,atlas


class BrokerTests(unittest.TestCase):
    def setUp(self):
        self.inventory,self.docs,self.atlas=dummy()

    def broker(self,**kwargs):
        return Broker(self.inventory,self.docs,**kwargs)

    def test_search_has_identical_order_and_no_content_hints(self):
        for query in ("lamp","amber","trial","violet","not-found"):
            a=self.broker().call("search",{"query":query})
            b=Broker(self.inventory,self.atlas).call("search",{"query":query})
            self.assertEqual(a,b)
            self.assertTrue(all(set(x)=={"reference","title"} for x in a["results"]))

    def test_forbidden_reference_classes(self):
        # Each test gets a fresh broker so a prior exhaustion cannot mask leakage.
        for ref in ("key.json","scorer.py","other-arm/atlas.json","prior-answer.txt",
                    "C:/Windows/win.ini","/etc/passwd","../key.json","..%2Fkey.json",
                    "https://example.org/key","file:///key","guessed-secret","lamp-a/../key"):
            with self.subTest(ref=ref):
                b=self.broker(); result=b.call("read",{"reference":ref,"page":0})
                self.assertEqual(result,{"error":"unknown reference"})
                self.assertEqual(b.calls,1); self.assertGreater(b.bytes,0)

    def test_only_exact_arguments_allowed(self):
        cases=[("read",{"reference":"lamp-a","page":0,"arm":"atlas"}),
               ("read",{"reference":"lamp-a","page":True}),
               ("read",{"reference":"lamp-a","page":-1}),
               ("read",{"reference":"lamp-a","page":99}),
               ("read",{"reference":["lamp-a"],"page":0}),
               ("search",{"query":"x","path":"../"}), ("exec",{"cmd":"read key"})]
        for tool,args in cases:
            with self.subTest(tool=tool,args=args): self.assertIn("error",self.broker().call(tool,args))

    def test_failed_calls_count_and_ninth_call_stops(self):
        b=self.broker()
        for _ in range(8): b.call("read",{"reference":"bad","page":0})
        with self.assertRaises(LimitReached): b.call("read",{"reference":"lamp-a","page":0})
        self.assertEqual(b.log[-1]["returned_bytes"],0)

    def test_utf8_paging_round_trip(self):
        text="é🚦abc\n"*5000
        chunks=pages(text)
        self.assertEqual("".join(chunks),text)
        self.assertTrue(all(len(c.encode())<=11000 for c in chunks))
        b=Broker([{"id":"long","title":"Long","search_text":"long"}],{"long":text},max_calls=20,max_bytes=100000)
        self.assertEqual("".join(b.call("read",{"reference":"long","page":i})["text"] for i in range(len(chunks))),text)

    def test_byte_limit_is_enforced_before_return(self):
        b=self.broker(max_bytes=1)
        with self.assertRaises(LimitReached): b.call("read",{"reference":"lamp-a","page":0})
        self.assertEqual(b.bytes,0)

    def test_wall_limit_is_enforced(self):
        now=[0]; b=self.broker(seconds=1,clock=lambda:now[0]); now[0]=1
        with self.assertRaises(LimitReached): b.call("search",{"query":"lamp"})

    def test_new_broker_has_no_prior_context_or_other_view(self):
        b=self.broker(); b.call("read",{"reference":"lamp-a","page":0})
        fresh=Broker(self.inventory,self.atlas)
        self.assertEqual((fresh.calls,fresh.bytes,fresh.log),(0,0,[]))
        self.assertEqual(fresh.texts,self.atlas)
        self.assertNotEqual(fresh.texts,self.docs)


class UsageTests(unittest.TestCase):
    @staticmethod
    def event(total=200,**changes):
        value={"threadId":"t","turnId":"u","tokenUsage":{"total":{
          "inputTokens":total-50,"cachedInputTokens":20,"outputTokens":50,
          "reasoningOutputTokens":10,"totalTokens":total}}}
        value.update(changes); return value

    def test_no_telemetry_is_unknown(self): self.assertIsNone(Usage("t","u",300).result())

    def test_cumulative_not_summed_and_subsets_not_added(self):
        usage=Usage("t","u",300)
        self.assertFalse(usage.add(self.event(200)))
        self.assertTrue(usage.add(self.event(320)))
        self.assertTrue(usage.add(self.event(320)))
        self.assertEqual(usage.result()["totalTokens"],320)

    def test_corrupted_and_foreign_usage_rejected(self):
        cases=[self.event(threadId="other"),self.event(turnId="other")]
        for field in Usage.FIELDS:
            value=self.event(); del value["tokenUsage"]["total"][field]; cases.append(value)
        value=self.event(); value["tokenUsage"]["total"]["totalTokens"]=999; cases.append(value)
        value=self.event(); value["tokenUsage"]["total"]["cachedInputTokens"]=999; cases.append(value)
        for case in cases:
            with self.assertRaises(ValueError): Usage("t","u",300).add(case)

    def test_decreasing_usage_rejected(self):
        usage=Usage("t","u",300); usage.add(self.event(220))
        with self.assertRaises(ValueError): usage.add(self.event(200))


class NativeTelemetryTests(unittest.TestCase):
    def test_failed_or_incomplete_discovery_is_not_absence(self):
        for changes in ({"toolsError":"discovery failed"}, {"runtimeStatus":None},
                        {"runtimeStatus":"failed"}, {"runtimeStatus":"starting"}):
            server={"name":"x", "tools":{}, "runtimeStatus":"connected", "toolsError":None}
            server.update(changes)
            records,_=mcp_page_inventory({"data":[server], "nextCursor":None})
            self.assertEqual(mcp_absence_status(records),"unverified")
        records,_=mcp_page_inventory({"data":[{"name":"x","tools":{}}], "nextCursor":None})
        self.assertEqual(mcp_absence_status(records),"unverified")
        records,_=mcp_page_inventory({"data":[{"name":"x","tools":{},"runtimeStatus":"connected","toolsError":None}], "nextCursor":None})
        self.assertEqual(mcp_absence_status(records),"passed")
        self.assertEqual(mcp_absence_status([]),"passed")

    def test_missing_turn_inventory_is_never_empty(self):
        for value in ({}, {"turns":None}, {"turns":{}}, None):
            with self.assertRaises(ValueError): prior_turn_count(value)
        self.assertEqual(prior_turn_count({"turns":[]}),0)
        self.assertEqual(prior_turn_count({"turns":[{"id":"prior"}]}),1)

    def test_missing_mcp_fields_are_never_empty(self):
        cases=[{}, {"data":[],"nextCursor":False}, {"data":[]},
               {"data":[{"name":"x"}],"nextCursor":None},
               {"data":[{"name":"x","tools":None}],"nextCursor":None},
               {"data":[{"name":"x","tools":[]}],"nextCursor":None}]
        for value in cases:
            with self.assertRaises(ValueError): mcp_page_inventory(value)
        self.assertEqual(mcp_page_inventory({"data":[],"nextCursor":None}),([],None))
        servers,cursor=mcp_page_inventory({"data":[{"name":"x","tools":{"t":{}}}],"nextCursor":"next"})
        self.assertEqual(servers[0]["tool_count"],1); self.assertEqual(cursor,"next")


class PacketTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls): cls.units,cls.maps,cls.inputs=build()

    def test_inventory_excludes_answers_tasks_protocol(self):
        self.assertEqual(len(self.units),5912)
        self.assertEqual(len(self.inputs),28)
        for path in self.inputs:
            self.assertFalse(any(s in path for s in ("tm-retrieval","benchmarks/","docs/","preparation","tasks.json")))

    def test_raw_bytes_equal_and_fact_map_spans_present(self):
        for unit in self.units:
            mapping=self.maps[unit["id"]]
            if unit["shared_raw"]:
                self.assertEqual(unit["atlas"],unit["documentation"])
                self.assertTrue(mapping.get("expanded_equals_source",True))
            else:
                payload=json.loads(unit["atlas"])
                docs,spans=documentation(payload)
                self.assertEqual(docs,unit["documentation"])
                self.assertEqual(spans,mapping["documentation_spans"])
                self.assertTrue(all(0<=s["span"][0]<=s["span"][1]<=len(docs) for s in spans))

    def test_provenance_expansion_negative_control(self):
        unit=next(u for u in self.units if u["id"]=="tm-pair-0-left")
        factored=json.loads(unit["atlas"])["record"]
        original=expand_trace(factored)
        self.assertEqual(expand_trace(factor_trace(original)),original)
        changed=copy.deepcopy(factored); changed["trace_sources"]["rows"][0]["trace"]["line"]+=1
        self.assertNotEqual(expand_trace(changed),original)

    def test_source_identity_keys_survive_documentation(self):
        data={"source_sha256":{"scripts/audit_operation_minima.py":"abc", "MiXeD_File.py":"def"},
              "empty":[],"nothing":None,"zero":0,"flag":False}
        text,_=documentation(data)
        for key in data["source_sha256"]: self.assertIn(key,text)
        self.assertIn("Empty list",text); self.assertIn("null",text)
        self.assertIn("false",text)

    def test_pair_registry_reconstruction_and_input_identity(self):
        by_id={u['id']:u for u in self.units}
        originals=json.loads(blob(REGISTRIES[2]))['pairs']
        self.assertEqual(originals,json.loads(blob(REGISTRIES[3]))['pairs'])
        for i,expected in enumerate(originals):
            ref='tm-pair-'+str(i)
            value=json.loads(by_id[ref]['atlas'])['record']
            for side in ('left','right'):
                target=value.pop(side+'_reference')
                prefix=json.loads(by_id[target]['atlas'])
                self.assertEqual(prefix['input'],expected['input'])
                value[side]=expand_trace(prefix['record'])
            self.assertEqual(value,expected)

    def test_generic_pair_discovery_in_both_arms(self):
        inventory=[{k:v for k,v in u.items() if k not in ('atlas','documentation')} for u in self.units]
        for arm in ('documentation','atlas'):
            broker=Broker(inventory,{u['id']:u[arm] for u in self.units})
            for i,name in enumerate(('tiny stay','bb2','bb3','bb4')):
                results=broker.call('search',{'query':'machine pair '+name})['results']
                self.assertEqual(results[0]['reference'],'tm-pair-'+str(i))


if __name__=="__main__": unittest.main()
