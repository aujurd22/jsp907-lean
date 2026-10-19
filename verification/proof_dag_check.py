"""Use the 'domain tokenizer + canonical AST + verifier loop + multi-representation'
recipe on the live proof of Theorem 4.1 (JSP-000907).

1. Canonical AST: PROOF_DAG.json (nodes = statements, edges = dependencies).
2. Structural checks on the DAG (acyclic, every dependency defined, goal reachable).
3. Verifier loop: each node that has an executable check is run against the
   explicit construction for m = 1,2,3.
4. Multi-representation consistency: the same node rendered as (a) canonical JSON,
   (b) English, (c) Lean signature; tokenised with a math-domain BPE trained on
   Mathlib statements, compared with a general tokenizer.
"""
import json, os, sys, itertools
sys.path.insert(0, os.path.join(os.path.dirname(__file__)))
from verify_section4b import build, k4_free, colourable, degeneracy, all_cycles_through, chords_of

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DAG = json.load(open(os.path.join(ROOT, "PROOF_DAG.json"), encoding="utf-8"))
NODES = {n["id"]: n for n in DAG["nodes"]}
EDGES = DAG["edges"]


def structural_checks():
    ids = set(NODES)
    problems = []
    for a, b in EDGES:
        if a not in ids: problems.append(f"edge {a}->{b}: unknown source")
        if b not in ids: problems.append(f"edge {a}->{b}: unknown target")
    # acyclicity
    adj = {i: [] for i in ids}
    for a, b in EDGES:
        adj[a].append(b)
    color = {}
    def dfs(u):
        color[u] = 1
        for v in adj[u]:
            if color.get(v) == 1: return False
            if color.get(v) is None and not dfs(v): return False
        color[u] = 2
        return True
    for i in ids:
        if color.get(i) is None and not dfs(i):
            problems.append("cycle detected in dependency graph")
    # reachability from goal backward
    radj = {i: [] for i in ids}
    for a, b in EDGES:
        radj[b].append(a)
    seen = set()
    stack = [DAG["goal"]]
    while stack:
        u = stack.pop()
        if u in seen: continue
        seen.add(u)
        stack.extend(radj[u])
    unreachable = (ids - seen) - {n for n in ids if n not in NODES or NODES[n]["kind"] == "corollary"}
    return problems, unreachable


def verifier_loop():
    results = {}
    for m in (1, 2, 3):
        n, adj, verts, edges = build(m)
        res = {}
        res["DEF"] = (n == 20 * m + 31, f"|V|={n}")
        res["L4.2"] = (k4_free(n, adj), "K4-free")
        res["P4.5"] = (not colourable(n, adj, 3), "not 3-colourable")
        res["P4.5b"] = (colourable(n, adj, 4), "4-colourable")
        bad = [e for e in edges if degeneracy(n, adj, skip=e) > 2]
        res["P4.6"] = (len(bad) == 0, f"{len(bad)} bad edges")
        v = n - 1
        cyc = all_cycles_through(n, adj, v)
        mx = max((chords_of(c, adj) for c in cyc), default=0)
        res["P4.10"] = (mx <= 10, f"{len(cyc)} cycles, max chords={mx}")
        results[m] = res
    return results


def token_stats():
    from tokenizers import Tokenizer, models, trainers, pre_tokenizers
    reps = json.load(open(os.path.join(ROOT, "..", "_ml_reps.json"), encoding="utf-8"))
    tk = Tokenizer(models.BPE(unk_token=None))
    tk.pre_tokenizer = pre_tokenizers.ByteLevel(add_prefix_space=False)
    tr = trainers.BpeTrainer(vocab_size=8000, special_tokens=[], show_progress=False)
    tk.train_from_iterator(reps["R0"][:30000], trainer=tr)
    from transformers import AutoTokenizer
    gpt2 = AutoTokenizer.from_pretrained("gpt2", local_files_only=True)
    out = {}
    for rep_name, render in (("english", lambda n: n["statement"]),
                             ("lean", lambda n: n["lean"]),
                             ("canonical_json", lambda n: json.dumps([n["id"], n["kind"], n["statement"], n["lean"]]))):
        texts = [render(NODES[i]) for i in NODES]
        math_tok = sum(len(tk.encode(t).ids) for t in texts)
        g_tok = sum(len(gpt2(t, add_special_tokens=False)["input_ids"]) for t in texts)
        out[rep_name] = (math_tok, g_tok)
    return out


def main():
    print("== 1. canonical AST structural checks ==")
    problems, unreachable = structural_checks()
    print("   nodes:", len(NODES), "edges:", len(EDGES))
    print("   problems:", problems if problems else "none")
    print("   unreachable from goal:", sorted(unreachable) if unreachable else "none")
    print("\n== 2. verifier loop (m=1,2,3) ==")
    results = verifier_loop()
    for m, res in results.items():
        print(f"   m={m}: " + "  ".join(f"{k}={'PASS' if v[0] else 'FAIL'}({v[1]})" for k, v in res.items()))
    print("\n== 3. multi-representation token cost (all nodes) ==")
    for k, (mt, gt) in token_stats().items():
        print(f"   {k:16s} math-BPE={mt:5d}  gpt2={gt:5d}")
    ok = not problems and not unreachable and all(all(v[0] for v in r.values()) for r in results.values())
    print("\nOVERALL:", "PASS" if ok else "FAIL")


if __name__ == "__main__":
    main()

