import Mathlib
import RequestProject.CycleCut

/-!
# Target: Erdős Problem #907 / JSP-000907

Paper: "Short proofs in combinatorics, probability and number theory II"
(Alexeev, Putterman, Sawhney, Sellke, Valiant; arXiv:2604.06609), Section 4.

Theorem 4.1. For every integer m ≥ 1 there exists an explicit K4-free graph G_m
on 20m + 31 vertices such that
  (1) χ(G_m) = 4;
  (2) every proper subgraph H ⊊ G_m is 3-colorable (in fact 2-degenerate);
  (3) every cycle C in G_m satisfies ch_{G_m}(C) ≤ 10,
where ch_G(C) = number of edges of G joining two nonconsecutive vertices of C.

Consequently the answer to Erdős's question is NO: there is no function
f : ℕ → ℕ with f(r) → ∞ such that every 4-chromatic graph G, all of whose
subgraphs on at most r vertices are 3-colorable, contains an odd cycle C with
ch_G(C) ≥ f(r).

The explicit construction (caterpillar of pentagonal blocks) and the full proof
are in `section4.md` at the project root.

## Formalization

* Vertex labels `a, b, c, d, e` (and `A, …, E`) are encoded as `0, 1, 2, 3, 4 : Fin 5`, in
  cyclic order around each pentagon.
* `Block m` is the type of the `4m + 6` pentagon blocks: the spine blocks `S_0, …, S_m` and the
  leaf blocks `L_{i,x}` (indexed by `LeafIdx m`, the pairs `(i, x)` allowed by Section 4.2).
* `Vert m` is the vertex type of `G_m`: the extra vertex `v` (called `hub`) and the vertices
  `B[p]` (`node B p`) of the blocks.
* `extNbr B p` is the unique inter-block neighbour of `B[p]` (or `none` when `B[p]` is a
  non-attachment vertex of a leaf block, which is then joined to `v`).
* `Gm m` is the graph `G_m`.  All results are proved for every `m : ℕ`; for `m = 0` the
  construction degenerates to a single spine pentagon carrying five leaf blocks, and every
  statement remains true.
* Chords: `chords G C` is the finite set of edges of `G` with both ends on the closed walk `C`
  that are not edges of `C`; for a cycle these are exactly the edges joining nonconsecutive
  vertices of `C`.
* 2-degeneracy: `TwoDegenerate H` says every nonempty vertex set `S` contains a vertex with at
  most two `H`-neighbours in `S`.

Main results: `card_vert`, `K4_free`, `not_colorable_three`, `colorable_four`,
`chromaticNumber_eq_four`, `twoDegenerate_of_lt`, `colorable_three_of_lt`, `chords_card_le_ten`,
the bundled `theorem_4_1`, and the corollary `erdos_907`.
-/

open SimpleGraph Finset

namespace Erdos907

/-- `IsLeafSlot m i x`: the spine block `S_i` carries a leaf block `L_{i,x}` attached at its
vertex labelled `x`.  These are `x ∈ {b, d, e}` for every `i`, together with `x = a` for `i = 0`
and `x = c` for `i = m` (labels `a,b,c,d,e` are `0,1,2,3,4`). -/
def IsLeafSlot (m : ℕ) (i : Fin (m + 1)) (x : Fin 5) : Prop :=
  (x ≠ 0 ∧ x ≠ 2) ∨ (x = 0 ∧ i = 0) ∨ (x = 2 ∧ i = Fin.last m)

instance (m : ℕ) (i : Fin (m + 1)) (x : Fin 5) : Decidable (IsLeafSlot m i x) := by
  unfold IsLeafSlot; infer_instance

/-- Indices `(i, x)` of the leaf blocks `L_{i,x}`. -/
abbrev LeafIdx (m : ℕ) := {p : Fin (m + 1) × Fin 5 // IsLeafSlot m p.1 p.2}

/-- The pentagon blocks of `G_m`: spine blocks `S_i` and leaf blocks `L_{i,x}`. -/
inductive Block (m : ℕ) where
  | spine (i : Fin (m + 1))
  | leaf (l : LeafIdx m)
  deriving DecidableEq, Fintype

/-- The vertices of `G_m`: the extra vertex `v` (`hub`) and the vertex `B[p]` (`node B p`) with
label `p` of each pentagon block `B`. -/
inductive Vert (m : ℕ) where
  | hub
  | node (b : Block m) (p : Fin 5)
  deriving DecidableEq, Fintype

/-- The inter-block neighbour of `B[p]`:
* `S_i[a] ~ S_{i-1}[c]` for `i > 0` and `S_0[a] ~ L_{0,a}[A]`;
* `S_i[c] ~ S_{i+1}[a]` for `i < m` and `S_m[c] ~ L_{m,c}[C]`;
* `S_i[x] ~ L_{i,x}[X]` for `x ∈ {b, d, e}`;
* `L_{i,x}[X] ~ S_i[x]`, while `L_{i,x}[Y]` (`Y ≠ X`) has none (it is joined to `v`). -/
def extNbr {m : ℕ} : Block m → Fin 5 → Option (Block m × Fin 5)
  | .spine i, p =>
    if hp : p = 0 then
      if hi : i.val = 0 then some (.leaf ⟨(i, 0), Or.inr (Or.inl ⟨rfl, Fin.ext hi⟩)⟩, 0)
      else some (.spine ⟨i.val - 1, by omega⟩, 2)
    else if hp2 : p = 2 then
      if hi : i.val = m then some (.leaf ⟨(i, 2), Or.inr (Or.inr ⟨rfl, Fin.ext hi⟩)⟩, 2)
      else some (.spine ⟨i.val + 1, by omega⟩, 0)
    else some (.leaf ⟨(i, p), Or.inl ⟨hp, hp2⟩⟩, p)
  | .leaf l, p => if p = l.1.2 then some (.spine l.1.1, p) else none

/-- Adjacency of `G_m`: consecutive vertices of the same pentagon, inter-block edges, and the
edges from `v` to the non-attachment vertices of the leaf blocks. -/
def adj {m : ℕ} : Vert m → Vert m → Prop
  | .hub, .hub => False
  | .hub, .node b p => extNbr b p = none
  | .node b p, .hub => extNbr b p = none
  | .node b p, .node b' p' => (b = b' ∧ (p' = p + 1 ∨ p = p' + 1)) ∨ extNbr b p = some (b', p')

instance {m : ℕ} : DecidableRel (adj (m := m)) := by
  intro a b; cases a <;> cases b <;> unfold adj <;> infer_instance

lemma extNbr_symm {m : ℕ} {b b' : Block m} {p p' : Fin 5}
    (h : extNbr b p = some (b', p')) : extNbr b' p' = some (b, p) := by
  cases b with
  | spine i =>
    simp only [extNbr] at h
    split_ifs at h with h1 h2 h3 h4 <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨rfl, rfl⟩ := h <;> subst_vars
    · simp [extNbr]
    · have : i.val - 1 ≠ m := by omega
      simp [extNbr, this, Fin.ext_iff]; omega
    · simp [extNbr]
    · simp only [extNbr]
      simp
    · simp [extNbr]
  | leaf l =>
    simp only [extNbr] at h
    split_ifs at h with h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨⟨i, x⟩, hl⟩ := l
    simp only at h1 ⊢
    subst h1
    rcases hl with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [extNbr, h1, h2]
    · simp only at h1 h2; subst h1 h2; simp [extNbr]
    · simp only at h1 h2; subst h1 h2; simp [extNbr]

/-- The spine index of a block. -/
def Block.idx {m : ℕ} : Block m → ℕ
  | .spine i => i.val
  | .leaf l => l.1.1.val

lemma extNbr_spine_cases {m : ℕ} {i : Fin (m + 1)} {b' : Block m} {p p' : Fin 5}
    (h : extNbr (.spine i) p = some (b', p')) :
    (∃ j : Fin (m + 1), b' = .spine j ∧
      ((p = 2 ∧ p' = 0 ∧ j.val = i.val + 1) ∨ (p = 0 ∧ p' = 2 ∧ i.val = j.val + 1))) ∨
    (∃ l : LeafIdx m, b' = .leaf l ∧ l.1 = (i, p) ∧ p' = p) := by
  simp only [extNbr] at h
  split_ifs at h with h1 h2 h3 h4 <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;> subst_vars
  · right; exact ⟨_, rfl, rfl, rfl⟩
  · left; exact ⟨_, rfl, Or.inr ⟨rfl, rfl, by simp; omega⟩⟩
  · right; exact ⟨_, rfl, rfl, rfl⟩
  · left; exact ⟨_, rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
  · right; exact ⟨_, rfl, rfl, rfl⟩

lemma extNbr_leaf_eq {m : ℕ} {l : LeafIdx m} {p : Fin 5} :
    extNbr (.leaf l) p = if p = l.1.2 then some (.spine l.1.1, p) else none := rfl

/-- Case analysis of the external (inter-block) neighbour. -/
lemma extNbr_some_cases {m : ℕ} {b b' : Block m} {p p' : Fin 5}
    (h : extNbr b p = some (b', p')) :
    (∃ i j : Fin (m + 1), b = .spine i ∧ b' = .spine j ∧
      ((p = 2 ∧ p' = 0 ∧ j.val = i.val + 1) ∨ (p = 0 ∧ p' = 2 ∧ i.val = j.val + 1))) ∨
    (∃ i l, b = .spine i ∧ b' = .leaf l ∧ l.1 = (i, p) ∧ p' = p) ∨
    (∃ l i, b = .leaf l ∧ b' = .spine i ∧ l.1 = (i, p) ∧ p' = p) := by
  cases b with
  | spine i =>
    rcases extNbr_spine_cases h with ⟨j, rfl, hj⟩ | ⟨l, rfl, hl, rfl⟩
    · left; exact ⟨i, j, rfl, rfl, hj⟩
    · right; left; exact ⟨i, l, rfl, rfl, hl, rfl⟩
  | leaf l =>
    rw [extNbr_leaf_eq] at h
    split_ifs at h with h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    right; right; exact ⟨l, _, rfl, rfl, by rw [h1], rfl⟩

lemma extNbr_ne_self {m : ℕ} {b : Block m} {p q : Fin 5} : extNbr b p ≠ some (b, q) := by
  intro h
  rcases extNbr_some_cases h with ⟨i, j, h1, h2, h3⟩ | ⟨i, l, h1, h2, -⟩ | ⟨l, i, h1, h2, -⟩
  · rw [h1] at h2; cases h2; omega
  · rw [h1] at h2; cases h2
  · rw [h1] at h2; cases h2

lemma extNbr_spine_ne_none {m : ℕ} (i : Fin (m + 1)) (p : Fin 5) :
    extNbr (.spine i) p ≠ none := by
  simp only [extNbr]; split_ifs <;> simp

lemma fin5_add_one_ne (p : Fin 5) : p + 1 ≠ p := by revert p; decide
lemma fin5_rim_iff (p q : Fin 5) : (q = p + 1 ∨ p = q + 1) ↔ (q = p + 1 ∨ q = p + 4) := by
  revert p q; decide

/-- **The graph `G_m`.**  Two vertices `B[p]`, `B'[p']` in pentagon blocks are adjacent iff
they are consecutive on the same pentagon or joined by the inter-block edge given by `extNbr`;
the hub `v` is adjacent to `B[p]` iff `B[p]` has no inter-block neighbour, i.e. iff `B` is a leaf
block `L_{i,x}` and `p ≠ x`. -/
def Gm (m : ℕ) : SimpleGraph (Vert m) where
  Adj := adj
  symm := by
    intro a b h
    cases a <;> cases b <;> simp only [adj] at h ⊢
    · exact h
    · exact h
    rcases h with ⟨rfl, h⟩ | h
    · exact Or.inl ⟨rfl, h.symm⟩
    · exact Or.inr (extNbr_symm h)
  loopless := by
    refine ⟨fun a h => ?_⟩
    cases a with
    | hub => exact h
    | node b p =>
      simp only [adj] at h
      rcases h with ⟨-, h | h⟩ | h
      · exact fin5_add_one_ne p h.symm
      · exact fin5_add_one_ne p h.symm
      · exact extNbr_ne_self h

instance (m : ℕ) : DecidableRel (Gm m).Adj := fun a b => inferInstanceAs (Decidable (adj a b))

/-! ### Basic adjacency facts -/

/-- The inter-block neighbour of `B[p]` as a vertex (the hub `v` if there is none). -/
def extV {m : ℕ} (b : Block m) (p : Fin 5) : Vert m :=
  match extNbr b p with
  | none => .hub
  | some q => .node q.1 q.2

section adjacency

variable {m : ℕ}

lemma adj_node_node {b b' : Block m} {p p' : Fin 5} :
    (Gm m).Adj (.node b p) (.node b' p') ↔
      (b = b' ∧ (p' = p + 1 ∨ p = p' + 1)) ∨ extNbr b p = some (b', p') := Iff.rfl

lemma adj_hub_node {b : Block m} {p : Fin 5} :
    (Gm m).Adj .hub (.node b p) ↔ extNbr b p = none := Iff.rfl

lemma adj_node_hub {b : Block m} {p : Fin 5} :
    (Gm m).Adj (.node b p) .hub ↔ extNbr b p = none := Iff.rfl

lemma not_adj_hub_hub : ¬ (Gm m).Adj .hub .hub := fun h => h

lemma adj_node_iff (b : Block m) (p : Fin 5) (y : Vert m) :
    (Gm m).Adj (.node b p) y ↔ y = .node b (p + 1) ∨ y = .node b (p + 4) ∨ y = extV b p := by
  cases y with
  | hub =>
    rw [adj_node_hub]; simp only [extV]
    cases h : extNbr b p <;> simp
  | node b' p' =>
    rw [adj_node_node, fin5_rim_iff]; simp only [extV]
    cases h : extNbr b p with
    | none =>
      simp only [reduceCtorEq, or_false, Vert.node.injEq]
      constructor
      · rintro ⟨rfl, hp | hp⟩ <;> simp [hp]
      · rintro (⟨rfl, hp⟩ | ⟨rfl, hp⟩) <;> simp [hp]
    | some q =>
      obtain ⟨b'', p''⟩ := q
      simp only [Option.some.injEq, Prod.mk.injEq, Vert.node.injEq]
      constructor
      · rintro (⟨rfl, hp | hp⟩ | ⟨rfl, rfl⟩) <;> simp_all
      · rintro (⟨rfl, hp⟩ | ⟨rfl, hp⟩ | ⟨rfl, rfl⟩) <;> simp_all

/-- The (at most three) neighbours of `B[p]`. -/
def nbrT (b : Block m) (p : Fin 5) : Finset (Vert m) :=
  {.node b (p + 1), .node b (p + 4), extV b p}

lemma nbrT_card (b : Block m) (p : Fin 5) : (nbrT b p).card ≤ 3 := card_le_three

lemma mem_nbrT_of_adj {b : Block m} {p : Fin 5} {y : Vert m} (h : (Gm m).Adj (.node b p) y) :
    y ∈ nbrT b p := by
  rw [adj_node_iff] at h
  simp only [nbrT, mem_insert, mem_singleton]
  exact h

lemma adj_rim (b : Block m) (p q : Fin 5) (h : q = p + 1) : (Gm m).Adj (.node b p) (.node b q) :=
  Or.inl ⟨rfl, Or.inl h⟩

lemma adj_rim' (b : Block m) (p : Fin 5) : (Gm m).Adj (.node b p) (.node b (p + 1)) :=
  adj_rim b p _ rfl

lemma adj_rim_extV (b : Block m) (p : Fin 5) : (Gm m).Adj (.node b p) (extV b p) := by
  rw [adj_node_iff]; simp

lemma adj_attach (l : LeafIdx m) :
    (Gm m).Adj (.node (.spine l.1.1) l.1.2) (.node (.leaf l) l.1.2) := by
  apply (Gm m).symm
  exact Or.inr (by simp [extNbr_leaf_eq])

lemma adj_spine (i j : Fin (m + 1)) (h : j.val = i.val + 1) :
    (Gm m).Adj (.node (.spine i) 2) (.node (.spine j) 0) := by
  refine Or.inr ?_
  have : i.val ≠ m := by have := j.isLt; omega
  simp only [extNbr]
  simp only [Fin.isValue, Fin.reduceEq, ↓reduceDIte, this, Option.some.injEq, Prod.mk.injEq,
    Block.spine.injEq, and_true]
  ext; simp [h]

lemma adj_hub_leaf (l : LeafIdx m) (p : Fin 5) (hp : p ≠ l.1.2) :
    (Gm m).Adj .hub (.node (.leaf l) p) := by
  rw [adj_hub_node, extNbr_leaf_eq]; simp [hp]

lemma hub_adj_iff (y : Vert m) :
    (Gm m).Adj .hub y ↔ ∃ l p, y = .node (.leaf l) p ∧ p ≠ l.1.2 := by
  constructor
  · intro h
    cases y with
    | hub => exact absurd h not_adj_hub_hub
    | node b p =>
      rw [adj_hub_node] at h
      cases b with
      | spine i => exact absurd h (extNbr_spine_ne_none i p)
      | leaf l =>
        rw [extNbr_leaf_eq] at h
        split_ifs at h with h1
        exact ⟨l, p, rfl, h1⟩
  · rintro ⟨l, p, rfl, hp⟩
    exact adj_hub_leaf l p hp

end adjacency

/-! ### Vertex count -/

def vertEquiv (m : ℕ) : Vert m ≃ Option (Block m × Fin 5) where
  toFun
    | .hub => none
    | .node b p => some (b, p)
  invFun
    | none => .hub
    | some (b, p) => .node b p
  left_inv := by intro x; cases x <;> rfl
  right_inv := by intro x; rcases x with _ | ⟨b, p⟩ <;> rfl

def blockEquiv (m : ℕ) : Block m ≃ Fin (m + 1) ⊕ LeafIdx m where
  toFun
    | .spine i => .inl i
    | .leaf l => .inr l
  invFun
    | .inl i => .spine i
    | .inr l => .leaf l
  left_inv := by intro x; cases x <;> rfl
  right_inv := by intro x; rcases x with i | l <;> rfl

lemma card_leafIdx (m : ℕ) : Fintype.card (LeafIdx m) = 3 * m + 5 := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type_right, Fin.sum_univ_five]
  simp [IsLeafSlot, Finset.sum_ite_eq']
  ring

/-- **Theorem 4.1, vertex count.** `G_m` has `20 m + 31` vertices. -/
theorem card_vert (m : ℕ) : Fintype.card (Vert m) = 20 * m + 31 := by
  rw [Fintype.card_congr (vertEquiv m), Fintype.card_option, Fintype.card_prod,
    Fintype.card_congr (blockEquiv m), Fintype.card_sum, card_leafIdx]
  simp; ring

/-! ### `G_m` is not 3-colorable (Lemmas 4.3, 4.4, Proposition 4.5) -/

lemma fin3_path_forcing : ∀ (α x a1 a2 a3 a4 : Fin 3), a1 ≠ α → a2 ≠ α → a3 ≠ α → a4 ≠ α →
    a1 ≠ a2 → a2 ≠ a3 → a3 ≠ a4 → x ≠ a1 → x ≠ a4 → x = α := by
  intro α x a1 a2 a3 a4; omega

lemma fin3_spine_forcing : ∀ (α a b c d e : Fin 3), a ≠ α → b ≠ α → d ≠ α → e ≠ α →
    a ≠ b → b ≠ c → c ≠ d → d ≠ e → e ≠ a → c = α := by
  intro α a b c d e; omega

lemma fin5_add_ne (q k : Fin 5) (hk : k ≠ 0) : q + k ≠ q := by revert q k; decide
lemma fin5_add_two (q : Fin 5) : q + 2 = q + 1 + 1 := by revert q; decide
lemma fin5_add_three (q : Fin 5) : q + 3 = q + 2 + 1 := by revert q; decide
lemma fin5_add_four (q : Fin 5) : q + 4 = q + 3 + 1 := by revert q; decide
lemma fin5_add_five (q : Fin 5) : q = q + 4 + 1 := by revert q; decide

section coloring

variable {m : ℕ}

/-- Pentagon forcing: if `B[q+1], …, B[q+4]` avoid the colour `α`, then `B[q]` has colour `α`. -/
lemma pent_force (c : (Gm m).Coloring (Fin 3)) (α : Fin 3) (b : Block m) (q : Fin 5)
    (h1 : c (.node b (q + 1)) ≠ α) (h2 : c (.node b (q + 2)) ≠ α)
    (h3 : c (.node b (q + 3)) ≠ α) (h4 : c (.node b (q + 4)) ≠ α) : c (.node b q) = α :=
  fin3_path_forcing α _ _ _ _ _ h1 h2 h3 h4
    (c.valid (adj_rim b _ _ (fin5_add_two q))) (c.valid (adj_rim b _ _ (fin5_add_three q)))
    (c.valid (adj_rim b _ _ (fin5_add_four q))) (c.valid (adj_rim b _ _ rfl))
    (c.valid (adj_rim b _ _ (fin5_add_five q))).symm

/-- **Lemma 4.3 (leaf forcing).** The attachment vertex of every leaf block has the colour
of the hub. -/
lemma leaf_force (c : (Gm m).Coloring (Fin 3)) (l : LeafIdx m) :
    c (.node (.leaf l) l.1.2) = c .hub := by
  apply pent_force c _ _ _ <;>
  exact (c.valid (adj_hub_leaf l _ (fin5_add_ne _ _ (by decide)))).symm

lemma spine_attach_ne (c : (Gm m).Coloring (Fin 3)) (i : Fin (m + 1)) (x : Fin 5)
    (h : IsLeafSlot m i x) : c (.node (.spine i) x) ≠ c .hub := by
  have := c.valid (adj_attach ⟨(i, x), h⟩)
  rwa [leaf_force] at this

/-- **Proposition 4.5.** `G_m` is not 3-colorable. -/
theorem not_colorable_three (m : ℕ) : ¬ (Gm m).Colorable 3 := by
  rintro ⟨c⟩
  have hb : ∀ i : Fin (m + 1), c (.node (.spine i) 1) ≠ c .hub :=
    fun i => spine_attach_ne c i 1 (Or.inl ⟨by decide, by decide⟩)
  have hd : ∀ i : Fin (m + 1), c (.node (.spine i) 3) ≠ c .hub :=
    fun i => spine_attach_ne c i 3 (Or.inl ⟨by decide, by decide⟩)
  have he : ∀ i : Fin (m + 1), c (.node (.spine i) 4) ≠ c .hub :=
    fun i => spine_attach_ne c i 4 (Or.inl ⟨by decide, by decide⟩)
  -- Lemma 4.4 (1),(2) and the induction of Proposition 4.5: every `S_k[a]` avoids `α`.
  have ha : ∀ k : ℕ, (hk : k ≤ m) → c (.node (.spine ⟨k, by omega⟩) 0) ≠ c .hub := by
    intro k
    induction k with
    | zero => intro _; exact spine_attach_ne c _ _ (Or.inr (Or.inl ⟨rfl, rfl⟩))
    | succ k ih =>
      intro hk
      have hc : c (.node (.spine ⟨k, by omega⟩) 2) = c .hub :=
        fin3_spine_forcing _ _ _ _ _ _ (ih (by omega)) (hb _) (hd _) (he _)
          (c.valid (adj_rim _ _ _ (by decide))) (c.valid (adj_rim _ _ _ (by decide)))
          (c.valid (adj_rim _ _ _ (by decide))) (c.valid (adj_rim _ _ _ (by decide)))
          (c.valid (adj_rim _ _ _ (by decide)))
      intro h
      apply c.valid (adj_spine ⟨k, by omega⟩ ⟨k + 1, by omega⟩ rfl)
      rw [hc, h]
  -- Lemma 4.4 (3) at the terminal block `S_m`.
  have hlast := pent_force c (c .hub) (.spine (Fin.last m)) 0 (hb _)
    (spine_attach_ne c _ 2 (Or.inr (Or.inr ⟨rfl, rfl⟩))) (hd _) (he _)
  exact ha m le_rfl hlast

/-! ### `G_m` is 4-colorable -/

def spineCol : Fin 5 → Fin 4 := ![0, 1, 2, 0, 1]
def leafCol : Fin 5 → Fin 4 := ![1, 2, 0, 1, 2]

lemma spineCol_rim : ∀ p : Fin 5, spineCol p ≠ spineCol (p + 1) := by decide
lemma leafCol_rim : ∀ p : Fin 5, leafCol p ≠ leafCol (p + 1) := by decide
lemma spineCol_ne_leafCol : ∀ p : Fin 5, spineCol p ≠ leafCol p := by decide
lemma spineCol_ne_three : ∀ p : Fin 5, spineCol p ≠ 3 := by decide
lemma leafCol_ne_three : ∀ p : Fin 5, leafCol p ≠ 3 := by decide

/-- An explicit proper 4-colouring of `G_m`. -/
def col4 : Vert m → Fin 4
  | .hub => 3
  | .node (.spine _) p => spineCol p
  | .node (.leaf _) p => leafCol p

/-- `G_m` is 4-colorable. -/
theorem colorable_four (m : ℕ) : (Gm m).Colorable 4 := by
  refine ⟨Coloring.mk col4 ?_⟩
  intro x y h
  cases x with
  | hub =>
    cases y with
    | hub => exact absurd h not_adj_hub_hub
    | node b p =>
      cases b
      · exact (spineCol_ne_three p).symm
      · exact (leafCol_ne_three p).symm
  | node b p =>
    cases y with
    | hub =>
      cases b
      · exact spineCol_ne_three p
      · exact leafCol_ne_three p
    | node b' p' =>
      rcases h with ⟨rfl, rfl | rfl⟩ | h
      · cases b
        · exact spineCol_rim p
        · exact leafCol_rim p
      · cases b
        · exact (spineCol_rim p').symm
        · exact (leafCol_rim p').symm
      · rcases extNbr_some_cases h with
          ⟨i, j, rfl, rfl, ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩⟩ | ⟨i, l, rfl, rfl, -, rfl⟩ |
            ⟨l, i, rfl, rfl, -, rfl⟩
        · simp only [col4]; decide
        · simp only [col4]; decide
        · exact spineCol_ne_leafCol _
        · exact (spineCol_ne_leafCol _).symm

/-- **Theorem 4.1 (1).** The chromatic number of `G_m` is `4`. -/
theorem chromaticNumber_eq_four (m : ℕ) : (Gm m).chromaticNumber = 4 := by
  have := (chromaticNumber_eq_iff_colorable_not_colorable (G := Gm m) (n := 3)).2
    ⟨colorable_four m, not_colorable_three m⟩
  exact this

end coloring

/-! ### `G_m` is `K_4`-free (Lemma 4.2) -/

section kfour

variable {m : ℕ}

lemma extV_ne_node_self (b : Block m) (p q : Fin 5) : extV b p ≠ .node b q := by
  unfold extV
  cases h : extNbr b p with
  | none => simp
  | some r =>
    obtain ⟨b', p'⟩ := r
    simp only [ne_eq, Vert.node.injEq, not_and]
    rintro rfl
    exact absurd h extNbr_ne_self

lemma extV_inj {b : Block m} {p q : Fin 5} (h : extV b p = extV b q) (hh : extV b p ≠ .hub) :
    p = q := by
  unfold extV at h hh
  cases h1 : extNbr b p with
  | none => simp [h1] at hh
  | some r =>
    cases h2 : extNbr b q with
    | none => simp [h1, h2] at h
    | some r' =>
      obtain ⟨b1, p1⟩ := r
      obtain ⟨b2, p2⟩ := r'
      simp only [h1, h2, Vert.node.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have e1 := extNbr_symm h1
      have e2 := extNbr_symm h2
      rw [e1] at e2
      simp only [Option.some.injEq, Prod.mk.injEq] at e2
      exact e2.2

lemma fin5_rim_rim : ∀ p : Fin 5, ¬ (p + 4 = p + 1 + 1 ∨ p + 1 = p + 4 + 1) := by decide

lemma no_tri_rim_rim (b : Block m) (p : Fin 5) :
    ¬ (Gm m).Adj (.node b (p + 1)) (.node b (p + 4)) := by
  rintro (⟨-, h⟩ | h)
  · exact fin5_rim_rim p h
  · exact extNbr_ne_self h

lemma no_tri_rim_ext {b : Block m} {p q : Fin 5} (hq : q ≠ p) (hh : extV b p ≠ .hub)
    (h : (Gm m).Adj (.node b q) (extV b p)) : False := by
  rw [adj_node_iff] at h
  rcases h with h | h | h
  · exact extV_ne_node_self b p _ h
  · exact extV_ne_node_self b p _ h
  · exact hq (extV_inj h hh).symm

/-- The graph `G_m \ {v}` is triangle-free. -/
lemma no_triangle_off_hub {x y z : Vert m} (hx : x ≠ .hub) (hy : y ≠ .hub) (hz : z ≠ .hub)
    (hxy : (Gm m).Adj x y) (hxz : (Gm m).Adj x z) (hyz : (Gm m).Adj y z) : False := by
  cases x with
  | hub => exact hx rfl
  | node b p =>
    have hne : y ≠ z := (Gm m).ne_of_adj hyz
    have h4 : p + 4 ≠ p := fin5_add_ne _ _ (by decide)
    have h1 : p + 1 ≠ p := fin5_add_ne _ _ (by decide)
    rw [adj_node_iff] at hxy hxz
    rcases hxy with rfl | rfl | rfl <;> rcases hxz with rfl | rfl | rfl
    · exact hne rfl
    · exact no_tri_rim_rim b p hyz
    · exact no_tri_rim_ext h1 hz hyz
    · exact no_tri_rim_rim b p ((Gm m).symm hyz)
    · exact hne rfl
    · exact no_tri_rim_ext h4 hz hyz
    · exact no_tri_rim_ext h1 hy ((Gm m).symm hyz)
    · exact no_tri_rim_ext h4 hy ((Gm m).symm hyz)
    · exact hne rfl

/-- **Lemma 4.2.** `G_m` contains no 4-clique. -/
theorem K4_free (m : ℕ) :
    ∀ S : Finset (Vert m), S.card = 4 → ¬ (Gm m).IsClique (S : Set (Vert m)) := by
  intro S hS hcl
  have h3 : 3 ≤ (S.erase .hub).card := by
    have := Finset.pred_card_le_card_erase (s := S) (a := .hub); omega
  obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq h3
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.1 hTc
  have hx := hT (by simp : x ∈ ({x, y, z} : Finset _))
  have hy := hT (by simp : y ∈ ({x, y, z} : Finset _))
  have hz := hT (by simp : z ∈ ({x, y, z} : Finset _))
  rw [Finset.mem_erase] at hx hy hz
  exact no_triangle_off_hub hx.1 hy.1 hz.1 (hcl hx.2 hy.2 hxy) (hcl hx.2 hz.2 hxz)
    (hcl hy.2 hz.2 hyz)

/-- Equivalently, `G_m` is `K_4`-free in Mathlib's sense. -/
theorem cliqueFree_four (m : ℕ) : (Gm m).CliqueFree 4 := by
  intro S hS
  exact K4_free m S hS.2 hS.1

end kfour

/-! ### Proper subgraphs are 2-degenerate (Proposition 4.6) -/

open Classical in
/-- A (finite) graph is *2-degenerate* if every nonempty set of vertices contains a vertex
having at most two neighbours inside the set. -/
def TwoDegenerate {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) : Prop :=
  ∀ S : Finset V, S.Nonempty → ∃ v ∈ S, (H.neighborFinset v ∩ S).card ≤ 2

/-- Every 2-degenerate graph is 3-colorable (greedy colouring in reverse peeling order). -/
theorem TwoDegenerate.colorable_three {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V}
    (hH : TwoDegenerate H) : H.Colorable 3 := by
  classical
  suffices h : ∀ n, ∀ S : Finset V, S.card = n →
      ∃ c : V → Fin 3, ∀ x ∈ S, ∀ y ∈ S, H.Adj x y → c x ≠ c y by
    obtain ⟨c, hc⟩ := h _ univ rfl
    exact ⟨Coloring.mk c (fun {x y} hxy => hc x (mem_univ _) y (mem_univ _) hxy)⟩
  intro n
  induction n with
  | zero =>
    intro S hS
    rw [card_eq_zero] at hS
    subst hS
    exact ⟨fun _ => 0, by simp⟩
  | succ n ih =>
    intro S hS
    obtain ⟨v, hv, hdeg⟩ := hH S (card_pos.1 (by omega))
    obtain ⟨c, hc⟩ := ih (S.erase v) (by rw [card_erase_of_mem hv]; omega)
    obtain ⟨k, hk⟩ : ∃ k : Fin 3, k ∉ (H.neighborFinset v ∩ S).image c := by
      by_contra hcon
      push_neg at hcon
      have h1 : (univ : Finset (Fin 3)) ⊆ (H.neighborFinset v ∩ S).image c := fun k _ => hcon k
      have h2 := card_le_card h1
      have h3 := card_image_le (s := H.neighborFinset v ∩ S) (f := c)
      simp only [card_univ, Fintype.card_fin] at h2
      omega
    refine ⟨Function.update c v k, ?_⟩
    intro x hx y hy hxy
    by_cases hxv : x = v <;> by_cases hyv : y = v
    · subst hxv hyv; exact absurd hxy (H.loopless.irrefl _)
    · subst hxv
      rw [Function.update_self, Function.update_of_ne hyv]
      intro h
      apply hk
      rw [mem_image]
      exact ⟨y, by simp [hxy, hy], h.symm⟩
    · subst hyv
      rw [Function.update_self, Function.update_of_ne hxv]
      intro h
      apply hk
      rw [mem_image]
      exact ⟨x, by simp [H.symm hxy, hx], h⟩
    · rw [Function.update_of_ne hxv, Function.update_of_ne hyv]
      exact hc x (mem_erase.2 ⟨hxv, hx⟩) y (mem_erase.2 ⟨hyv, hy⟩) hxy

section degenerate

variable {m : ℕ}

lemma fin5_cover : ∀ p q : Fin 5,
    q = p ∨ q = p + 1 ∨ q = p + 1 + 1 ∨ q = p + 1 + 1 + 1 ∨ q = p + 1 + 1 + 1 + 1 := by decide

/-- Closedness of a vertex set under adjacency inside `G_m \ {v}`. -/
def OffHubClosed (T : Set (Vert m)) : Prop :=
  ∀ x ∈ T, ∀ y, x ≠ .hub → y ≠ .hub → (Gm m).Adj x y → y ∈ T

lemma block_closed {T : Set (Vert m)} (hT : OffHubClosed T) {b : Block m} {p : Fin 5}
    (h : .node b p ∈ T) (q : Fin 5) : .node b q ∈ T := by
  have step : ∀ r : Fin 5, Vert.node b r ∈ T → Vert.node b (r + 1) ∈ T :=
    fun r hr => hT _ hr _ (by simp) (by simp) (adj_rim' _ _)
  have h1 := step _ h
  have h2 := step _ h1
  have h3 := step _ h2
  have h4 := step _ h3
  rcases fin5_cover p q with rfl | rfl | rfl | rfl | rfl <;> assumption

lemma spine_of_leaf {T : Set (Vert m)} (hT : OffHubClosed T) {l : LeafIdx m} {p : Fin 5}
    (h : .node (.leaf l) p ∈ T) (q : Fin 5) : .node (.spine l.1.1) q ∈ T := by
  have h1 := block_closed hT h l.1.2
  exact block_closed hT (hT _ h1 _ (by simp) (by simp) ((Gm m).symm (adj_attach l))) q

lemma leaf_of_spine {T : Set (Vert m)} (hT : OffHubClosed T) (l : LeafIdx m) {p : Fin 5}
    (h : .node (.spine l.1.1) p ∈ T) (q : Fin 5) : .node (.leaf l) q ∈ T := by
  have h1 := block_closed hT h l.1.2
  exact block_closed hT (hT _ h1 _ (by simp) (by simp) (adj_attach l)) q

lemma spine_succ {T : Set (Vert m)} (hT : OffHubClosed T) (i j : Fin (m + 1))
    (hij : j.val = i.val + 1) : (Vert.node (.spine i) 0 ∈ T ↔ Vert.node (.spine j) 0 ∈ T) := by
  constructor
  · intro h
    exact block_closed hT (hT _ (block_closed hT h 2) _ (by simp) (by simp) (adj_spine i j hij)) 0
  · intro h
    exact block_closed hT
      (hT _ h _ (by simp) (by simp) ((Gm m).symm (adj_spine i j hij))) 0

/-- `G_m \ {v}` is connected: a nonempty vertex set closed under adjacency in `G_m \ {v}`
contains every vertex other than `v`. -/
lemma offHub_connected {T : Set (Vert m)} (hT : OffHubClosed T) {w : Vert m} (hw : w ∈ T)
    (hwh : w ≠ .hub) : ∀ y, y ≠ .hub → y ∈ T := by
  -- some spine block lies in `T`
  obtain ⟨i0, hi0⟩ : ∃ i0 : Fin (m + 1), Vert.node (.spine i0) 0 ∈ T := by
    cases w with
    | hub => exact absurd rfl hwh
    | node b p =>
      cases b with
      | spine i => exact ⟨i, block_closed hT hw 0⟩
      | leaf l => exact ⟨l.1.1, spine_of_leaf hT hw 0⟩
  -- go down to `S_0`
  have hdown : ∀ k : ℕ, (hk : k ≤ i0.val) →
      Vert.node (.spine ⟨i0.val - k, by omega⟩) 0 ∈ T := by
    intro k
    induction k with
    | zero => intro _; simpa using hi0
    | succ k ih =>
      intro hk
      exact (spine_succ hT ⟨i0.val - (k + 1), by omega⟩ ⟨i0.val - k, by omega⟩
        (by simp; omega)).2 (ih (by omega))
  have h0 := hdown i0.val le_rfl
  -- go up to every `S_k`
  have hup : ∀ k : ℕ, (hk : k ≤ m) → Vert.node (.spine ⟨k, by omega⟩) 0 ∈ T := by
    intro k
    induction k with
    | zero => intro _; simpa using h0
    | succ k ih =>
      intro hk
      exact (spine_succ hT ⟨k, by omega⟩ ⟨k + 1, by omega⟩ rfl).1 (ih (by omega))
  intro y hy
  cases y with
  | hub => exact absurd rfl hy
  | node b p =>
    cases b with
    | spine i => exact block_closed hT (hup i.val (by omega)) p
    | leaf l => exact leaf_of_spine hT l (hup l.1.1.val (by omega)) p

/-- A vertex adjacent to the hub (the vertex `L_{0,b}[A]`). -/
def someLeafIdx (m : ℕ) : LeafIdx m := ⟨(0, 1), Or.inl ⟨by simp, by simp⟩⟩

open Classical in
/-- **Proposition 4.6 / Theorem 4.1 (2).** Every proper subgraph of `G_m` (same vertex type)
is 2-degenerate. -/
theorem twoDegenerate_of_lt (m : ℕ) (H : SimpleGraph (Vert m)) (hle : H ≤ Gm m)
    (hne : H ≠ Gm m) : TwoDegenerate H := by
  intro S hS
  -- a vertex `x ≠ v` that misses one of its `G_m`-neighbours has `H`-degree at most `2` in `S`
  have key : ∀ x y, x ≠ .hub → (Gm m).Adj x y → (∀ z, H.Adj x z → z ∈ S → z ≠ y) →
      (H.neighborFinset x ∩ S).card ≤ 2 := by
    intro x y hx hxy hz
    cases x with
    | hub => exact absurd rfl hx
    | node b p =>
      calc (H.neighborFinset (.node b p) ∩ S).card ≤ ((nbrT b p).erase y).card := by
            apply card_le_card
            intro z hzS
            rw [mem_inter, mem_neighborFinset] at hzS
            exact mem_erase.2 ⟨hz z hzS.1 hzS.2, mem_nbrT_of_adj (hle hzS.1)⟩
        _ ≤ 2 := by
            rw [card_erase_of_mem (mem_nbrT_of_adj hxy)]
            have := nbrT_card b p
            omega
  by_cases h1 : ∃ u ∈ S, u ≠ .hub ∧ ∃ y, (Gm m).Adj u y ∧ y ∉ S
  · obtain ⟨u, hu, huh, y, huy, hyS⟩ := h1
    exact ⟨u, hu, key u y huh huy (fun z _ hzS hzy => by subst hzy; exact hyS hzS)⟩
  push_neg at h1
  by_cases h2 : ∃ w ∈ S, w ≠ .hub
  · obtain ⟨w, hw, hwh⟩ := h2
    have hall : ∀ y, y ≠ .hub → y ∈ S :=
      offHub_connected (T := (S : Set (Vert m))) (fun x hx y hxh _ hxy => h1 x hx hxh y hxy)
        hw hwh
    obtain ⟨x, y, hxy, hnxy⟩ : ∃ x y, (Gm m).Adj x y ∧ ¬ H.Adj x y := by
      by_contra hc
      push_neg at hc
      exact hne (le_antisymm hle (fun x y h => hc x y h))
    have hz : ∀ x y, ¬ H.Adj x y → ∀ z, H.Adj x z → z ∈ S → z ≠ y := by
      rintro x y hn z hz - rfl
      exact hn hz
    by_cases hx : x = .hub
    · subst hx
      have hy : y ≠ .hub := fun h => by subst h; exact not_adj_hub_hub hxy
      exact ⟨y, hall y hy, key y _ hy ((Gm m).symm hxy) (hz _ _ (fun h => hnxy (H.symm h)))⟩
    · exact ⟨x, hall x hx, key x y hx hxy (hz _ _ hnxy)⟩
  · push_neg at h2
    obtain ⟨v, hv⟩ := hS
    refine ⟨v, hv, ?_⟩
    have hvh : v = .hub := h2 v hv
    subst hvh
    have : H.neighborFinset Vert.hub ∩ S = ∅ := by
      ext z
      simp only [mem_inter, mem_neighborFinset, Finset.notMem_empty, iff_false, not_and]
      intro hz hzS
      have := h2 z hzS
      subst this
      exact H.loopless.irrefl _ hz
    rw [this]; simp

/-- **Theorem 4.1 (2).** Every proper subgraph of `G_m` is 3-colorable. -/
theorem colorable_three_of_lt (m : ℕ) (H : SimpleGraph (Vert m)) (hle : H ≤ Gm m)
    (hne : H ≠ Gm m) : H.Colorable 3 :=
  (twoDegenerate_of_lt m H hle hne).colorable_three

end degenerate

/-! ### Chords of cycles (Lemmas 4.7–4.9, Proposition 4.10) -/

/-- The chords of a closed walk `C` in `G`: the edges of `G` joining two vertices of `C` that
are not consecutive on `C`.  For a cycle, two vertices of `C` are consecutive exactly when they
are joined by an edge of `C`, so a chord is an edge of `G` with both ends on `C` which is not
one of the edges of `C`. -/
def chords {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {u : V}
    (C : G.Walk u u) : Finset (Sym2 V) :=
  C.support.toFinset.sym2.filter (fun e => e ∈ G.edgeSet ∧ e ∉ C.edges)

lemma mem_chords {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {u : V}
    {C : G.Walk u u} {e : Sym2 V} :
    e ∈ chords G C ↔ (∀ x ∈ e, x ∈ C.support) ∧ e ∈ G.edgeSet ∧ e ∉ C.edges := by
  simp [chords, Finset.mem_sym2_iff]

section chordsGm

variable {m : ℕ}

/-- The vertex set of the leaf block `L`. -/
def InLeaf (l : LeafIdx m) (w : Vert m) : Prop := ∃ q, w = .node (.leaf l) q

/-- The attachment edge `S_i[x] L_{i,x}[X]` of the leaf block `l`. -/
def attachEdge (l : LeafIdx m) : Sym2 (Vert m) :=
  s(.node (.spine l.1.1) l.1.2, .node (.leaf l) l.1.2)

lemma not_inLeaf_hub (l : LeafIdx m) : ¬ InLeaf l .hub := by
  rintro ⟨q, h⟩; cases h

/-- The only edge of `G_m \ {v}` leaving a leaf block is its attachment edge. -/
lemma leaf_cross {l : LeafIdx m} {a b : Vert m} (hab : (Gm m).Adj a b) (ha : InLeaf l a)
    (hb : ¬ InLeaf l b) (hbh : b ≠ .hub) : s(a, b) = attachEdge l := by
  obtain ⟨q, rfl⟩ := ha
  cases b with
  | hub => exact absurd rfl hbh
  | node c r =>
    rcases hab with ⟨rfl, -⟩ | h
    · exact absurd ⟨r, rfl⟩ hb
    · rw [extNbr_leaf_eq] at h
      split_ifs at h with h1
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst h1
      exact Sym2.eq_swap

/-- The spine index of a vertex is at most `i`. -/
def LeftOf (i : ℕ) (w : Vert m) : Prop := ∃ c r, w = .node c r ∧ c.idx ≤ i

lemma not_leftOf_hub (i : ℕ) : ¬ LeftOf (m := m) i .hub := by
  rintro ⟨c, r, h, -⟩; cases h

lemma leftOf_cross {i : ℕ} {a b : Vert m} (hab : (Gm m).Adj a b) (ha : LeftOf i a)
    (hb : ¬ LeftOf i b) (hbh : b ≠ .hub) (i' j' : Fin (m + 1)) (hi : i'.val = i)
    (hj : j'.val = i + 1) :
    s(a, b) = s(.node (.spine i') 2, .node (.spine j') 0) := by
  obtain ⟨c, r, rfl, hc⟩ := ha
  cases b with
  | hub => exact absurd rfl hbh
  | node c' r' =>
    have hc' : ¬ c'.idx ≤ i := fun h => hb ⟨c', r', rfl, h⟩
    rcases hab with ⟨rfl, -⟩ | h
    · exact absurd hc hc'
    · rcases extNbr_some_cases h with
        ⟨i1, j1, rfl, rfl, ⟨rfl, rfl, h1⟩ | ⟨rfl, rfl, h1⟩⟩ | ⟨i1, l, rfl, rfl, hl, rfl⟩ |
          ⟨l, i1, rfl, rfl, hl, rfl⟩
      · simp only [Block.idx] at hc hc'
        have e1 : i1 = i' := Fin.ext (by omega)
        have e2 : j1 = j' := Fin.ext (by omega)
        subst e1 e2; rfl
      · simp only [Block.idx] at hc hc'; omega
      · simp only [Block.idx, hl] at hc hc'; omega
      · simp only [Block.idx, hl] at hc hc'; omega

/-- A cut certificate for the inter-block edge `xy`: a vertex set not containing the hub which
separates `x` from `y` and whose only crossing edge avoiding the hub is `xy`. -/
def BridgeCut (x y : Vert m) (A : Vert m → Prop) : Prop :=
  ¬ A .hub ∧ A x ∧ ¬ A y ∧
    ∀ a b, a ≠ .hub → b ≠ .hub → (Gm m).Adj a b → A a → ¬ A b → s(a, b) = s(x, y)

lemma BridgeCut.flip {x y : Vert m} {A : Vert m → Prop} (h : BridgeCut y x A) (hx : x ≠ .hub) :
    BridgeCut x y (fun w => w ≠ .hub ∧ ¬ A w) := by
  obtain ⟨h0, hy, hx', hc⟩ := h
  refine ⟨by simp, ⟨hx, hx'⟩, by simp [hy], ?_⟩
  rintro a b ha hb hab ⟨-, hna⟩ hnb
  have hAb : A b := by by_contra hc'; exact hnb ⟨hb, hc'⟩
  rw [Sym2.eq_swap, hc b a hb ha ((Gm m).symm hab) hAb hna, Sym2.eq_swap]

/-- **Lemma 4.7 (cut edges).** Every inter-block edge admits a cut certificate. -/
lemma bridgeCut_exists {b b' : Block m} {p p' : Fin 5} (hbb : b ≠ b')
    (h : (Gm m).Adj (.node b p) (.node b' p')) :
    ∃ A, BridgeCut (.node b p) (.node b' p') A := by
  rcases h with ⟨rfl, -⟩ | h
  · exact absurd rfl hbb
  have leafCase : ∀ (l : LeafIdx m) (q : Fin 5) (y : Vert m), y ≠ .hub → ¬ InLeaf l y →
      (Gm m).Adj (.node (.leaf l) q) y → BridgeCut (.node (.leaf l) q) y (InLeaf l) := by
    intro l q y hy hny hadj
    refine ⟨not_inLeaf_hub l, ⟨q, rfl⟩, hny, ?_⟩
    intro a b ha hb hab hAa hAb
    rw [leaf_cross hab hAa hAb hb, leaf_cross hadj ⟨q, rfl⟩ hny hy]
  have spineCase : ∀ (i j : Fin (m + 1)), j.val = i.val + 1 →
      BridgeCut (.node (.spine i) 2) (.node (.spine j) 0) (LeftOf i.val) := by
    intro i j hij
    refine ⟨not_leftOf_hub _, ⟨_, _, rfl, le_rfl⟩, ?_, ?_⟩
    · rintro ⟨c, r, h, hc⟩
      cases h
      simp only [Block.idx] at hc
      omega
    · intro a b ha hb hab hAa hAb
      exact leftOf_cross hab hAa hAb hb i j rfl hij
  rcases extNbr_some_cases h with
    ⟨i, j, rfl, rfl, ⟨rfl, rfl, h1⟩ | ⟨rfl, rfl, h1⟩⟩ | ⟨i, l, rfl, rfl, hl, rfl⟩ |
      ⟨l, i, rfl, rfl, hl, rfl⟩
  · exact ⟨_, spineCase i j h1⟩
  · exact ⟨_, (spineCase j i h1).flip (by simp)⟩
  · refine ⟨_, (leafCase l p' (.node (.spine i) p') (by simp) ?_ ((Gm m).symm (Or.inr h))).flip (by simp)⟩
    rintro ⟨q, hq⟩; cases hq
  · refine ⟨_, leafCase l p' (.node (.spine i) p') (by simp) ?_ (Or.inr h)⟩
    rintro ⟨q, hq⟩; cases hq

lemma extV_spine_mid (i : Fin (m + 1)) (p : Fin 5) (h0 : p ≠ 0) (h2 : p ≠ 2) :
    extV (.spine i) p = .node (.leaf ⟨(i, p), Or.inl ⟨h0, h2⟩⟩) p := by
  simp [extV, extNbr, h0, h2]

lemma extV_leaf_ne (l : LeafIdx m) (p : Fin 5) (h : p ≠ l.1.2) : extV (.leaf l) p = .hub := by
  simp [extV, extNbr_leaf_eq, h]

lemma fin5_rim_spine : ∀ p p' : Fin 5, (p' = p + 1 ∨ p = p' + 1) →
    (p ≠ 0 ∧ p ≠ 2) ∨ (p' ≠ 0 ∧ p' ≠ 2) := by decide

lemma fin5_rim_ne : ∀ p p' : Fin 5, (p' = p + 1 ∨ p = p' + 1) → p ≠ p' := by decide

variable {u : Vert m} {C : (Gm m).Walk u u}

lemma dart_edge_mem (d : (Gm m).Dart) (hd : d ∈ C.darts) : d.edge ∈ C.edges :=
  List.mem_map_of_mem hd

/-- At a vertex `x ≠ v` of a cycle, if the edge `xy` is not used then every other edge at `x`
is used. -/
lemma cyc_other (hC : C.IsCycle) {b : Block m} {p : Fin 5} (hx : .node b p ∈ C.support)
    {y z : Vert m} (hy : (Gm m).Adj (.node b p) y) (hyC : s(.node b p, y) ∉ C.edges)
    (hz : (Gm m).Adj (.node b p) z) (hzy : z ≠ y) : s(.node b p, z) ∈ C.edges :=
  cycle_deg_three_other hC hx (nbrT b p) (nbrT_card b p) (fun _ h => mem_nbrT_of_adj h)
    (mem_nbrT_of_adj hy) hyC (mem_nbrT_of_adj hz) hzy

/-- **Leaf visits.** If a cycle meets a leaf block `L` and also a vertex outside `L`, then it
uses an edge from the hub into `L`. -/
lemma leaf_hub_edge (hC : C.IsCycle) (l : LeafIdx m) {x y : Vert m} (hx : x ∈ C.support)
    (hy : y ∈ C.support) (hxl : InLeaf l x) (hyl : ¬ InLeaf l y) :
    ∃ q, s(.hub, .node (.leaf l) q) ∈ C.edges := by
  classical
  by_contra hno
  push_neg at hno
  apply cycle_cut_one hC (InLeaf l) (attachEdge l) ?_ hx hy hxl hyl
  intro d hd hcross
  have hmem := dart_edge_mem d hd
  have hadj := d.adj
  have he : d.edge = s(d.fst, d.snd) := rfl
  by_cases h1 : InLeaf l d.fst
  · have h2 : ¬ InLeaf l d.snd := fun h => hcross ⟨fun _ => h, fun _ => h1⟩
    by_cases hs : d.snd = .hub
    · obtain ⟨q, hq⟩ := h1
      rw [he, hq, hs, Sym2.eq_swap] at hmem
      exact absurd hmem (hno q)
    · rw [he]; exact leaf_cross hadj h1 h2 hs
  · have h2 : InLeaf l d.snd := by
      by_contra h2; exact hcross ⟨fun h => absurd h h1, fun h => absurd h h2⟩
    by_cases hs : d.fst = .hub
    · obtain ⟨q, hq⟩ := h2
      rw [he, hq, hs] at hmem
      exact absurd hmem (hno q)
    · rw [he, Sym2.eq_swap]; exact leaf_cross ((Gm m).symm hadj) h2 h1 hs

/-- A chord at a vertex `x ≠ v` is unique (a vertex other than `v` has degree `3`). -/
lemma chord_unique (hC : C.IsCycle) {x : Vert m} (hx : x ≠ .hub) {e1 e2 : Sym2 (Vert m)}
    (h1 : e1 ∈ chords (Gm m) C) (h2 : e2 ∈ chords (Gm m) C) (hx1 : x ∈ e1) (hx2 : x ∈ e2) :
    e1 = e2 := by
  rw [mem_chords] at h1 h2
  obtain ⟨y1, rfl⟩ := Sym2.mem_iff_exists.1 hx1
  obtain ⟨y2, rfl⟩ := Sym2.mem_iff_exists.1 hx2
  cases x with
  | hub => exact absurd rfl hx
  | node b p =>
    by_contra hne
    have hne' : y2 ≠ y1 := by rintro rfl; exact hne rfl
    exact h2.2.2 (cyc_other hC (h1.1 _ (Sym2.mem_mk_left _ _)) h1.2.1 h1.2.2 h2.2.1 hne')

/-- **Lemma 4.7/Proposition 4.10, inter-block case.** No chord joins two different blocks. -/
lemma chord_same_block (hC : C.IsCycle) {b b' : Block m} {p p' : Fin 5}
    (h : s(.node b p, .node b' p') ∈ chords (Gm m) C) : b = b' := by
  classical
  by_contra hbb
  rw [mem_chords] at h
  obtain ⟨hsupp, hadj, hnot⟩ := h
  obtain ⟨A, hA0, hAx, hAy, hcut⟩ := bridgeCut_exists hbb hadj
  refine cycle_cut_hub hC .hub A hA0 ?_ (hsupp _ (Sym2.mem_mk_left _ _))
    (hsupp _ (Sym2.mem_mk_right _ _)) hAx hAy (by simp)
  intro d hd hf hs
  have hmem := dart_edge_mem d hd
  have he : d.edge = s(d.fst, d.snd) := rfl
  by_contra hc
  by_cases h1 : A d.fst
  · have h2 : ¬ A d.snd := fun h2 => hc ⟨fun _ => h2, fun _ => h1⟩
    rw [he, hcut _ _ hf hs d.adj h1 h2] at hmem
    exact hnot hmem
  · have h2 : A d.snd := by
      by_contra h2; exact hc ⟨fun h => absurd h h1, fun h => absurd h h2⟩
    rw [he, Sym2.eq_swap, hcut _ _ hs hf ((Gm m).symm d.adj) h2 h1] at hmem
    exact hnot hmem

/-- The neighbours of the hub along the cycle `C`. -/
def hubNbrs (C : (Gm m).Walk u u) : Finset (Vert m) :=
  univ.filter (fun w => s(.hub, w) ∈ C.edges)

lemma hubNbrs_card (hC : C.IsCycle) : (hubNbrs C).card ≤ 2 :=
  cycle_nbrs_card_le_two hC .hub

lemma mem_hubNbrs {w : Vert m} : w ∈ hubNbrs C ↔ s(.hub, w) ∈ C.edges := by
  simp [hubNbrs]

/-- **Lemma 4.8, pentagon chord in a leaf block.** An endpoint of such a chord which is not the
attachment vertex is a hub-neighbour along the cycle. -/
lemma leaf_rim_endpoint (hC : C.IsCycle) {l : LeafIdx m} {p p' : Fin 5}
    (hch : s(.node (.leaf l) p, .node (.leaf l) p') ∈ chords (Gm m) C) (hp : p ≠ l.1.2) :
    Vert.node (.leaf l) p ∈ hubNbrs C := by
  rw [mem_chords] at hch
  obtain ⟨hsupp, hadj, hnot⟩ := hch
  have := cyc_other hC (hsupp _ (Sym2.mem_mk_left _ _)) (((Gm m).mem_edgeSet.1 hadj)) hnot
    ((Gm m).symm (adj_hub_leaf l p hp)) (by simp)
  rw [mem_hubNbrs, Sym2.eq_swap]
  exact this

/-- **Lemma 4.9, pentagon chord in a spine block.** If an endpoint `S_i[x]` of such a chord
carries a leaf block, the cycle runs through that leaf block and hence uses a hub edge into
it. -/
lemma spine_rim_endpoint (hC : C.IsCycle) {i : Fin (m + 1)} {p p' : Fin 5}
    (hch : s(.node (.spine i) p, .node (.spine i) p') ∈ chords (Gm m) C) (h0 : p ≠ 0)
    (h2 : p ≠ 2) : ∃ q, Vert.node (.leaf ⟨(i, p), Or.inl ⟨h0, h2⟩⟩) q ∈ hubNbrs C := by
  rw [mem_chords] at hch
  obtain ⟨hsupp, hadj, hnot⟩ := hch
  have hx := hsupp _ (Sym2.mem_mk_left _ _)
  have hz := adj_rim_extV (.spine i) p
  rw [extV_spine_mid i p h0 h2] at hz
  have hE := cyc_other hC hx (((Gm m).mem_edgeSet.1 hadj)) hnot hz (by simp)
  have hzS := C.snd_mem_support_of_mem_edges hE
  obtain ⟨q, hq⟩ := leaf_hub_edge hC _ hzS hx ⟨p, rfl⟩ (by rintro ⟨q, hq⟩; cases hq)
  exact ⟨q, mem_hubNbrs.2 hq⟩

/-- Chords not through the hub: at most `2 · |N_C(v)| ≤ 4` of them (Lemmas 4.8 and 4.9). -/
lemma rim_chords_card (hC : C.IsCycle) :
    ((chords (Gm m) C).filter (fun e => Vert.hub ∉ e)).card ≤ 2 * (hubNbrs C).card := by
  classical
  have hcard : (hubNbrs C ×ˢ (univ : Finset Bool)).card = 2 * (hubNbrs C).card := by
    simp [card_product]; ring
  rw [← hcard]
  apply card_le_card_of_forall_subsingleton (fun e (wf : Vert m × Bool) =>
    if wf.2 then wf.1 ∈ e else
      ∃ l q, wf.1 = .node (.leaf l) q ∧ Vert.node (.spine l.1.1) l.1.2 ∈ e)
  · intro e he
    rw [mem_filter] at he
    obtain ⟨heC, hhub⟩ := he
    induction e using Sym2.ind with
    | _ x y =>
    cases x with
    | hub => simp at hhub
    | node b p =>
    cases y with
    | hub => simp at hhub
    | node b' p' =>
    have hbb := chord_same_block hC heC
    subst hbb
    have hrim : p' = p + 1 ∨ p = p' + 1 := by
      rcases (mem_chords.1 heC).2.1 with ⟨-, h⟩ | h
      · exact h
      · exact absurd h extNbr_ne_self
    cases b with
    | leaf l =>
      by_cases hp : p = l.1.2
      · have hp' : p' ≠ l.1.2 := fun h => fin5_rim_ne p p' hrim (hp.trans h.symm)
        rw [Sym2.eq_swap] at heC ⊢
        exact ⟨(_, true), mem_product.2 ⟨leaf_rim_endpoint hC heC hp', mem_univ _⟩,
          by simp⟩
      · exact ⟨(_, true), mem_product.2 ⟨leaf_rim_endpoint hC heC hp, mem_univ _⟩, by simp⟩
    | spine i =>
      rcases fin5_rim_spine p p' hrim with ⟨h0, h2⟩ | ⟨h0, h2⟩
      · obtain ⟨q, hq⟩ := spine_rim_endpoint hC heC h0 h2
        exact ⟨(_, false), mem_product.2 ⟨hq, mem_univ _⟩, ⟨_, q, rfl, by simp⟩⟩
      · rw [Sym2.eq_swap] at heC
        obtain ⟨q, hq⟩ := spine_rim_endpoint hC heC h0 h2
        exact ⟨(_, false), mem_product.2 ⟨hq, mem_univ _⟩, ⟨_, q, rfl, by simp⟩⟩
  · rintro ⟨w, f⟩ -
    intro e1 he1 e2 he2
    obtain ⟨he1, hr1⟩ := he1
    obtain ⟨he2, hr2⟩ := he2
    rw [mem_filter] at he1 he2
    cases f with
    | true =>
      simp only [if_true] at hr1 hr2
      have hw : w ≠ .hub := by rintro rfl; exact he1.2 hr1
      exact chord_unique hC hw he1.1 he2.1 hr1 hr2
    | false =>
      simp only [Bool.false_eq_true, if_false] at hr1 hr2
      obtain ⟨l1, q1, rfl, hx1⟩ := hr1
      obtain ⟨l2, q2, hw2, hx2⟩ := hr2
      simp only [Vert.node.injEq, Block.leaf.injEq] at hw2
      obtain ⟨rfl, -⟩ := hw2
      exact chord_unique hC (by simp) he1.1 he2.1 hx1 hx2

/-- Chords through the hub: at most `3 · |N_C(v)| ≤ 6` of them (Lemma 4.8). -/
lemma hub_chords_card (hC : C.IsCycle) :
    ((chords (Gm m) C).filter (fun e => Vert.hub ∈ e)).card ≤ 3 * (hubNbrs C).card := by
  classical
  set W := (univ : Finset (Vert m)).filter (fun w => s(.hub, w) ∈ chords (Gm m) C) with hW
  have h1 : ((chords (Gm m) C).filter (fun e => Vert.hub ∈ e)).card ≤ W.card := by
    calc _ ≤ (W.image (fun w => s(Vert.hub, w))).card := by
          apply card_le_card
          intro e he
          rw [mem_filter] at he
          obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 he.2
          exact mem_image.2 ⟨w, by simp [hW, he.1], rfl⟩
      _ ≤ W.card := card_image_le
  have hdisj : Disjoint W (hubNbrs C) := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    rw [hW, mem_filter] at hw
    exact (mem_chords.1 hw.2).2.2 (mem_hubNbrs.1 hw')
  let blk : Vert m → Finset (Vert m) := fun w' => univ.filter (fun z =>
    (Gm m).Adj .hub z ∧ ∃ l q q', z = .node (.leaf l) q ∧ w' = .node (.leaf l) q')
  have hblk : ∀ w', (blk w').card ≤ 4 := by
    intro w'
    by_cases h : ∃ l q', w' = .node (.leaf l) q'
    · obtain ⟨l, q', rfl⟩ := h
      calc (blk _).card ≤ ((univ.erase l.1.2).image (fun q => Vert.node (.leaf l) q)).card := by
            apply card_le_card
            intro z hz
            simp only [blk, mem_filter, mem_univ, true_and] at hz
            obtain ⟨hadj, l2, q, q'', rfl, hw⟩ := hz
            simp only [Vert.node.injEq, Block.leaf.injEq] at hw
            obtain ⟨rfl, -⟩ := hw
            rw [hub_adj_iff] at hadj
            obtain ⟨l3, q3, h3, hq3⟩ := hadj
            simp only [Vert.node.injEq, Block.leaf.injEq] at h3
            obtain ⟨rfl, rfl⟩ := h3
            exact mem_image.2 ⟨q, mem_erase.2 ⟨hq3, mem_univ _⟩, rfl⟩
        _ ≤ (univ.erase l.1.2).card := card_image_le
        _ = 4 := by simp
    · have : blk w' = ∅ := by
        ext z
        simp only [blk, mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
        rintro ⟨-, l, q, q', -, hw⟩
        exact h ⟨l, q', hw⟩
      rw [this]; simp
  have hsub : W ∪ hubNbrs C ⊆ (hubNbrs C).biUnion blk := by
    intro w hw
    rw [mem_union] at hw
    rw [mem_biUnion]
    rcases hw with hw | hw
    · rw [hW, mem_filter] at hw
      obtain ⟨hsupp, hadj, -⟩ := mem_chords.1 hw.2
      have hadj' : (Gm m).Adj .hub w := hadj
      obtain ⟨l, p, rfl, hp⟩ := (hub_adj_iff _).1 hadj'
      obtain ⟨q, hq⟩ := leaf_hub_edge hC l (hsupp _ (Sym2.mem_mk_right _ _))
        (hsupp _ (Sym2.mem_mk_left _ _)) ⟨p, rfl⟩ (not_inLeaf_hub l)
      exact ⟨_, mem_hubNbrs.2 hq, by
        simp only [blk, mem_filter, mem_univ, true_and]
        exact ⟨hadj', l, p, q, rfl, rfl⟩⟩
    · have hadj : (Gm m).Adj .hub w := C.adj_of_mem_edges (mem_hubNbrs.1 hw)
      obtain ⟨l, p, rfl, hp⟩ := (hub_adj_iff _).1 hadj
      exact ⟨_, hw, by
        simp only [blk, mem_filter, mem_univ, true_and]
        exact ⟨hadj, l, p, p, rfl, rfl⟩⟩
  have h2 := card_le_card hsub
  rw [card_union_of_disjoint hdisj] at h2
  have h3 := card_biUnion_le (s := hubNbrs C) (t := blk)
  have h4 : ∑ w' ∈ hubNbrs C, (blk w').card ≤ (hubNbrs C).card * 4 :=
    sum_le_card_nsmul _ _ _ (fun w' _ => hblk w')
  omega

end chordsGm

/-- **Proposition 4.10 / Theorem 4.1 (3).** Every cycle of `G_m` has at most `10` chords. -/
theorem chords_card_le_ten (m : ℕ) {u : Vert m} (C : (Gm m).Walk u u) (hC : C.IsCycle) :
    (chords (Gm m) C).card ≤ 10 := by
  have h := card_filter_add_card_filter_not (s := chords (Gm m) C)
    (fun e => Vert.hub ∈ e)
  have h1 := hub_chords_card hC
  have h2 := rim_chords_card hC
  have h3 := hubNbrs_card hC
  omega

/-! ### Theorem 4.1 and the answer to Erdős's question -/

lemma exists_adj (m : ℕ) (z : Vert m) : ∃ w, (Gm m).Adj z w := by
  cases z with
  | hub => exact ⟨_, adj_hub_leaf (someLeafIdx m) 0 (by simp [someLeafIdx])⟩
  | node b p => exact ⟨_, adj_rim' b p⟩

/-- Every induced subgraph of `G_m` on a set of vertices missing at least one vertex is
3-colorable. -/
theorem induce_colorable_three (m : ℕ) (S : Finset (Vert m)) (hS : S ≠ univ) :
    ((Gm m).induce (S : Set (Vert m))).Colorable 3 := by
  obtain ⟨z, hz⟩ : ∃ z, z ∉ S := by
    by_contra h; push_neg at h; exact hS (eq_univ_iff_forall.2 h)
  obtain ⟨w, hzw⟩ := exists_adj m z
  have hne : (Gm m).deleteIncidenceSet z ≠ Gm m := by
    intro h
    have : ((Gm m).deleteIncidenceSet z).Adj z w := by rw [h]; exact hzw
    rw [deleteIncidenceSet_adj] at this
    exact this.2.1 rfl
  obtain ⟨c⟩ := colorable_three_of_lt m _ (deleteIncidenceSet_le _ z) hne
  refine ⟨Coloring.mk (fun x => c x.1) ?_⟩
  intro x y hxy
  apply c.valid
  rw [deleteIncidenceSet_adj]
  refine ⟨hxy, ?_, ?_⟩
  · rintro h; exact hz (h ▸ x.2)
  · rintro h; exact hz (h ▸ y.2)

/-- **Theorem 4.1.** For every `m` the explicit graph `G_m` has `20 m + 31` vertices, is
`K_4`-free, is not 3-colorable but is 4-colorable (so `χ(G_m) = 4`), every proper subgraph is
2-degenerate and hence 3-colorable, and every cycle has at most `10` chords. -/
theorem theorem_4_1 (m : ℕ) :
    Fintype.card (Vert m) = 20 * m + 31 ∧
    (∀ S : Finset (Vert m), S.card = 4 → ¬ (Gm m).IsClique (S : Set (Vert m))) ∧
    ¬ (Gm m).Colorable 3 ∧ (Gm m).Colorable 4 ∧ (Gm m).chromaticNumber = 4 ∧
    (∀ H : SimpleGraph (Vert m), H ≤ Gm m → H ≠ Gm m → TwoDegenerate H ∧ H.Colorable 3) ∧
    (∀ (u : Vert m) (C : (Gm m).Walk u u), C.IsCycle → (chords (Gm m) C).card ≤ 10) :=
  ⟨card_vert m, K4_free m, not_colorable_three m, colorable_four m, chromaticNumber_eq_four m,
    fun H hle hne => ⟨twoDegenerate_of_lt m H hle hne, colorable_three_of_lt m H hle hne⟩,
    fun _ C hC => chords_card_le_ten m C hC⟩

/-- **Erdős Problem #907: the answer is no.**  There is no function `f : ℕ → ℕ` with
`f r → ∞` such that every (finite) 4-chromatic graph all of whose subgraphs on at most `r`
vertices are 3-colorable contains an odd cycle with at least `f r` chords.  (The graphs `G_r`
are counterexamples: in fact they contain no cycle at all with more than `10` chords.) -/
theorem erdos_907 : ¬ ∃ f : ℕ → ℕ, Filter.Tendsto f Filter.atTop Filter.atTop ∧
    ∀ (r : ℕ) (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.chromaticNumber = 4 →
      (∀ S : Finset V, S.card ≤ r → (G.induce (S : Set V)).Colorable 3) →
      ∃ (u : V) (C : G.Walk u u), C.IsCycle ∧ Odd C.length ∧ f r ≤ (chords G C).card := by
  rintro ⟨f, hf, hG⟩
  obtain ⟨r, hr⟩ := (hf.eventually_ge_atTop 11).exists
  obtain ⟨u, C, hC, -, hle⟩ := hG r (Vert r) (Gm r) (chromaticNumber_eq_four r) (by
    intro S hS
    apply induce_colorable_three
    intro h
    have := card_vert r
    rw [h, card_univ] at hS
    omega)
  have := chords_card_le_ten r C hC
  omega

end Erdos907
