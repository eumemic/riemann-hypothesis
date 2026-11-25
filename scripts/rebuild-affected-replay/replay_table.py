"""Print a table from replay result files (JSON objects, concatenated). usage: replay_table.py FILE"""
import collections, json, sys
raw = open(sys.argv[1]).read()
rows = [json.loads(c) for c in raw.replace("}{", "}\n{").splitlines() if c.startswith("{")]
rows.sort(key=lambda r: int(r["batch"][1:]))
tot = [0, 0, 0, 0, 0]
print(f"{'batch':6}{'lake':>7}{'edited':>8}{'compiled':>9}{'reused':>8}{'changed':>8}{'misses':>7}{'cosm':>6}  ratio")
for r in rows:
    s = r["stats"]; cos = sum(v for k, v in s.items() if k.startswith("reused:"))
    print(f"{r['batch']:6}{r['recompiled_by_lake']:7}{r['edited_or_new']:8}{s['compiled']:9}{s['reused']:8}{s['compiled, output really changed']:8}{len(r['misses']):7}{cos:6}  {r['recompiled_by_lake']/s['compiled']:.1f}x")
    tot[0] += r["recompiled_by_lake"]; tot[1] += r["edited_or_new"]; tot[2] += s["compiled"]; tot[3] += s["reused"]; tot[4] += len(r["misses"])
print("total", tot, f"{tot[0]/tot[2]:.1f}x")
c = collections.Counter()
for r in rows:
    for k, v in r["stats"].items():
        if k.startswith("compiled: "): c[k[10:]] += v
for k, v in c.most_common(): print(f"{v:8} {k}")
for r in rows:
    for m in r["misses"]: print("MISS", r["batch"], m)
