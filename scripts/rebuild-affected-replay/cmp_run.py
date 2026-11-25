"""Compare what the script did in a real run on a batch with what the replay of that batch says it does.
usage: cmp_run.py HIST K RUN_JSONL      (RUN_JSONL: `.lake/rebuild-affected/run.jsonl` after the run)"""
import collections, json, os, sys
hist, k, run = sys.argv[1], int(sys.argv[2]), sys.argv[3]
real = {}
with open(run) as f:
    for line in f:
        r = json.loads(line); real[r["m"]] = None if r["reuse"] else r["why"]
model = {}
with open(os.path.join(hist, f"replay-b{k + 1}-visible-deep.compiled.tsv")) as f:
    for line in f:
        parts = line.rstrip("\n").split("\t"); model[parts[0]] = parts[1]
compiled_real = {m for m, why in real.items() if why}
print(f"real run: {len(real)} modules, {len(compiled_real)} compiled; replay: {len(model)} compiled")
only_real, only_model = compiled_real - model.keys(), model.keys() - compiled_real
print(f"compiled only in the real run: {len(only_real)}; only in the replay: {len(only_model)}")
for name, mods, why in (("real", only_real, real), ("replay", only_model, model)):
    c = collections.Counter(why[m] for m in mods)
    for reason, n in c.most_common(6): print(f"   only {name}: {n:5} {reason}   e.g. {next(m for m in mods if why[m] == reason)}")
