# JSP-000907 / Erdős #1091 — Lean 4 formalization

**Problem (JSP-000907, Erdős Problem #1091).**
Let `f : ℕ → ℕ` be a function with `f(r) → ∞`. Must every 4-chromatic graph `G`
such that every subgraph of `G` on at most `r` vertices is 3-colourable contain an
odd cycle `C` with at least `f(r)` chords?

**Answer: No** (negative). The complete mathematical solution is Section 4 of

> Boris Alexeev, Moe Putterman, Mehtaab Sawhney, Mark Sellke, Gregory Valiant,
> *Short proofs in combinatorics, probability and number theory II*,
> arXiv:[2604.06609](https://arxiv.org/abs/2604.06609) (2026), Section 4,
> Theorem 4.1.

Theorem 4.1 constructs, for every `m ≥ 1`, an explicit `K₄`-free graph `G_m` on
`20m + 31` vertices such that

1. `χ(G_m) = 4`;
2. every proper subgraph `H ⊊ G_m` is 3-colourable (in fact 2-degenerate);
3. every cycle `C` of `G_m` has `ch_{G_m}(C) ≤ 10` (chords = edges joining two
   nonconsecutive vertices of `C`).

`G_m` is a caterpillar of pentagonal blocks: spine blocks `S₀,…,S_m`, leaf blocks
attached to the spine by single edges, and one extra vertex `v` adjacent to the
four non-attachment vertices of every leaf block.

## Contents

| Path | Purpose |
|---|---|
| `RequestProject/Main.lean` | explicit definition of `G_m` and the formal proof of Theorem 4.1 |
| `verification/verify_section4b.py` | independent computational check of the construction (K₄-free, χ = 4, 2-degeneracy after edge deletion, chord bound) |
| `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` | pinned Lean/Mathlib toolchain |

## Status

The formalization is **complete**: `RequestProject/Main.lean` (1225 lines) and
`RequestProject/CycleCut.lean` (212 lines), no `sorry`/`admit`, and `#print axioms`
on `theorem_4_1` and `erdos_907` reports only `propext`, `Classical.choice` and
`Quot.sound`. It was produced with the Aristotle prover from Section 4 of
arXiv:2604.06609 and rebuilt in the Aristotle environment.

## Verification

- Built and axiom-checked in the Aristotle environment with the pinned toolchain
  (`leanprover/lean4:v4.28.0`, Mathlib `v4.28.0`).
- `#print axioms theorem_4_1` and `#print axioms erdos_907` report only
  `propext`, `Classical.choice`, `Quot.sound`; the sources contain no `sorry`,
  `admit`, `axiom` or `@[implemented_by]`.
- Portability check: a cross-compilation against Lean `v4.35.0-rc3` / Mathlib
  `v4.35.0-rc3` compiles the whole development up to two Mathlib API drifts
  (`List.count_eq_countP` now uses `==` rather than `decide`, and
  `SimpleGraph.IsCycle` now exposes `toSubgraph.neighborSet` instead of
  `p.edges`). These are library changes, not mathematical gaps; the pinned
  version above is the one that was built and audited.

## Build

```bash
lake exe cache get    # or: lake build
lake env lean RequestProject/Main.lean
```

Toolchain: `leanprover/lean4:v4.28.0`; Mathlib pinned in `lake-manifest.json`.

## Verification

- The proof contains no `sorry`/`admit` and no added axioms.
- Axiom audit: `#print axioms` on the main theorem (output to be recorded here).
- Independent computational check (`verification/verify_section4b.py`, m = 1,2,3):
  `|V| = 20m+31`, all vertices except `v` have degree 3, `K₄`-free,
  not 3-colourable, 4-colourable, every `G_m − e` is 2-degenerate, and the maximum
  number of chords over all cycles through `v` is exactly 10.

## Canonical proof structure

`PROOF_DAG.json` records the proof as a canonical dependency graph (13 nodes,
19 edges, corresponding to Lemmas 4.2-4.10). `verification/proof_dag_check.py`
checks the graph structurally, runs the executable parts of every node against the
explicit construction for m = 1,2,3, and reports the token cost of the same nodes
in three representations:

| representation | math-BPE tokens | GPT-2 tokens |
|---|---|---|
| English prose | 641 | 491 |
| Lean signatures | **151** | **128** |
| canonical JSON | 966 | 782 |

## Attribution

- Mathematical solution: Alexeev, Putterman, Sawhney, Sellke, Valiant
  (OpenAI), arXiv:2604.06609, Section 4.
- Lean formalization: produced for this repository (see commit history).



