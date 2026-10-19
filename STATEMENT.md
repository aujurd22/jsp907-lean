# Statement correspondence — JSP-000907 / Erdős #1091

## Original problem (Erdős Problem #1091, https://www.erdosproblems.com/1091)

For a graph `G` and a cycle `C ⊆ G`, let `ch_G(C)` be the number of edges of `G`
joining two nonconsecutive vertices of `C` (the *chords* of `C`).

The problem asks whether there is a function `f(r) → ∞` such that every
4-chromatic graph `G`, all of whose subgraphs on at most `r` vertices are
3-colourable, contains an odd cycle `C` with `ch_G(C) ≥ f(r)`.

Reference: P. Erdős, *Some recent problems and results in graph theory,
combinatorics and number theory*, Proceedings of the Seventh Southeastern
Conference on Combinatorics, Graph Theory and Computing (1976), 3–14.
See also erdosproblems.com/1091 (accessed 2026-10-19).

## Mathematical solution

arXiv:2604.06609, Section 4 (Theorem 4.1), by Alexeev–Putterman–Sawhney–Sellke–Valiant
(OpenAI), public April 2026. The solution is negative: Theorem 4.1 gives an explicit
infinite family of counterexamples.

## Lean formalization

The Lean statement to be proved is Theorem 4.1, i.e. for every `m ≥ 1` the
explicitly constructed graph `G m` satisfies:

1. `Fintype.card (V (G m)) = 20 * m + 31`;
2. `G m` is `K₄`-free;
3. `G m` is not 3-colourable and is 4-colourable;
4. every proper subgraph of `G m` is 2-degenerate (hence 3-colourable);
5. every cycle `C` of `G m` has at most 10 chords.

and the corollary that no unbounded `f` with the stated property exists.

### Correspondence notes

- **Counterexample form.** The original question is a universal statement over
  graphs; its refutation is exactly the existence, for every `r`, of a graph that
  is 4-chromatic, has all `≤ r`-vertex subgraphs 3-colourable, and has every odd
  cycle with `< f(r)` chords. Theorem 4.1 supplies this for every `m` (taking the
  graph `G_m`, whose proper subgraphs are even 2-degenerate, and whose cycles all
  have at most 10 chords).
- **"Proper subgraph"** is formalized as `H ≤ G` and `H ≠ G` on the same vertex
  type (subgraph, not necessarily induced). The paper's Proposition 4.6 proves the
  stronger statement that deleting any edge yields a 2-degenerate graph, which we
  formalize.
- **Cycles and chords.** A cycle is a `SimpleGraph.Walk` that is a cycle in the
  standard Mathlib sense; `ch_G(C)` counts edges of `G` between two vertices of
  `C` that are not consecutive on `C`.
- **Colourings.** `G.Colorable k` is Mathlib's `k`-colourability, i.e. a proper
  colouring with `k` colours.

### Verification of scope

- The paper's Theorem 4.1 is stated for `K₄`-free graphs; being `K₄`-free and
  4-chromatic is the exact setting of Erdős's question (Voss's theorem covers the
  `K₄`-free case).
- The construction is reproduced vertex-by-vertex and edge-by-edge from Section 4.2
  of the paper; `verification/verify_section4b.py` independently builds `G_m` for
  `m = 1,2,3` and checks all numeric claims.
