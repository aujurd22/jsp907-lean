import Mathlib

/-!
# Generic facts about cycles in simple graphs

Parity of edge cuts along closed walks, and the local structure of a cycle at a vertex.
These are used for the chord bound in `RequestProject/Main.lean`.
-/

open SimpleGraph Finset

namespace Erdos907

variable {V : Type*} {G : SimpleGraph V}

/-- Number of darts of a walk crossing the cut `(A, Aᶜ)`. -/
def crossCount (A : V → Prop) [DecidablePred A] {u w : V} (p : G.Walk u w) : ℕ :=
  p.darts.countP (fun d => decide (¬(A d.fst ↔ A d.snd)))

lemma crossCount_even_iff (A : V → Prop) [DecidablePred A] :
    ∀ {u w : V} (p : G.Walk u w), Even (crossCount A p) ↔ (A u ↔ A w) := by
  intro u w p
  induction p with
  | nil => simp [crossCount]
  | @cons a b c h p ih =>
    simp only [crossCount, Walk.darts_cons, List.countP_cons] at ih ⊢
    by_cases ha : A a <;> by_cases hb : A b <;> simp [ha, hb, Nat.even_add_one, -Nat.not_even_iff_odd] at ih ⊢ <;> tauto

lemma crossCount_closed_even (A : V → Prop) [DecidablePred A] {u : V} (p : G.Walk u u) :
    Even (crossCount A p) := (crossCount_even_iff A p).2 Iff.rfl

lemma support_side_of_crossCount_eq_zero (A : V → Prop) [DecidablePred A] :
    ∀ {u w : V} (p : G.Walk u w), crossCount A p = 0 → ∀ x ∈ p.support, (A x ↔ A u) := by
  intro u w p
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    intro h0 x hx
    simp only [crossCount, Walk.darts_cons, List.countP_cons] at h0
    have h1 : List.countP (fun d => decide (¬(A d.fst ↔ A d.snd))) p.darts = 0 := by omega
    have h2 : (A a ↔ A b) := by
      by_contra hc
      simp [hc] at h0
    rw [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Iff.rfl
    · exact (ih h1 x hx).trans h2.symm

lemma crossCount_pos (A : V → Prop) [DecidablePred A] {u w : V} (p : G.Walk u w)
    {x y : V} (hx : x ∈ p.support) (hy : y ∈ p.support) (hAx : A x) (hAy : ¬A y) :
    0 < crossCount A p := by
  rcases Nat.eq_zero_or_pos (crossCount A p) with h | h
  · have := support_side_of_crossCount_eq_zero A p h
    exact absurd ((this y hy).2 ((this x hx).1 hAx)) hAy
  · exact h

/-- If the walk `p` is closed and meets both sides of a cut, it crosses it at least twice. -/
lemma two_le_crossCount (A : V → Prop) [DecidablePred A] {u : V} (p : G.Walk u u)
    {x y : V} (hx : x ∈ p.support) (hy : y ∈ p.support) (hAx : A x) (hAy : ¬A y) :
    2 ≤ crossCount A p := by
  have h1 := crossCount_pos A p hx hy hAx hAy
  obtain ⟨k, hk⟩ := crossCount_closed_even A p
  omega

lemma countP_or_le {α : Type*} (p q : α → Bool) (l : List α) :
    l.countP (fun x => p x || q x) ≤ l.countP p + l.countP q := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons]
    cases p a <;> cases q a <;> simp <;> omega

lemma countP_disj_le {α : Type*} (p q r : α → Bool) (l : List α)
    (hpq : ∀ x ∈ l, ¬(p x = true ∧ q x = true)) (hr : ∀ x ∈ l, p x = true ∨ q x = true → r x = true) :
    l.countP p + l.countP q ≤ l.countP r := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons]
    have h1 := ih (fun x hx => hpq x (List.mem_cons_of_mem _ hx))
      (fun x hx => hr x (List.mem_cons_of_mem _ hx))
    have h2 := hpq a (List.mem_cons_self)
    have h3 := hr a (List.mem_cons_self)
    cases hp : p a <;> cases hq : q a <;> cases hr' : r a <;> simp_all <;> omega

variable [DecidableEq V]

lemma cycle_countP_snd_le_one {u : V} {p : G.Walk u u} (hp : p.IsCycle) (h : V) :
    p.darts.countP (fun d => decide (d.snd = h)) ≤ 1 := by
  have hn := hp.support_nodup
  rw [List.nodup_iff_count_le_one] at hn
  have := hn h
  rw [← Walk.map_snd_darts, List.count_eq_countP, List.countP_map] at this
  convert this using 2

lemma cycle_hub_darts_le_two {u : V} {p : G.Walk u u} (hp : p.IsCycle) (h : V) :
    p.darts.countP (fun d => decide (d.fst = h) || decide (d.snd = h)) ≤ 2 := by
  have h1 := cycle_countP_snd_le_one hp h
  have h2 := cycle_countP_snd_le_one hp.reverse h
  rw [Walk.darts_reverse, List.countP_reverse, List.countP_map] at h2
  have h3 := countP_or_le (fun d : G.Dart => decide (d.fst = h)) (fun d => decide (d.snd = h))
    p.darts
  have : p.darts.countP (fun d : G.Dart => decide (d.fst = h)) =
      p.darts.countP ((fun d : G.Dart => decide (d.snd = h)) ∘ Dart.symm) := by
    congr 1
  omega

/-- Core cut lemma.  Let `h` be a vertex and `A` a set of vertices not containing `h` such
that the cycle `p` uses no edge avoiding `h` that crosses `A`.  Then `p` cannot contain both a
vertex of `A` and a vertex outside `A ∪ {h}`. -/
lemma cycle_cut_hub {u : V} {p : G.Walk u u} (hp : p.IsCycle) (h : V) (A : V → Prop)
    [DecidablePred A] (hA : ¬A h)
    (hno : ∀ d ∈ p.darts, d.fst ≠ h → d.snd ≠ h → (A d.fst ↔ A d.snd))
    {x y : V} (hx : x ∈ p.support) (hy : y ∈ p.support) (hAx : A x) (hAy : ¬A y)
    (hyh : y ≠ h) : False := by
  classical
  have c1 := two_le_crossCount A p hx hy hAx hAy
  have c2 := two_le_crossCount (fun z => A z ∨ z = h) p hx hy (Or.inl hAx)
    (by simp [hAy, hyh])
  have c3 := cycle_hub_darts_le_two hp h
  have c4 := countP_disj_le (fun d : G.Dart => decide (¬(A d.fst ↔ A d.snd)))
    (fun d : G.Dart => decide (¬((A d.fst ∨ d.fst = h) ↔ (A d.snd ∨ d.snd = h))))
    (fun d => decide (d.fst = h) || decide (d.snd = h)) p.darts ?_ ?_
  · unfold crossCount at c1 c2
    have : (fun d : G.Dart => decide (¬((fun z => A z ∨ z = h) d.fst ↔ (fun z => A z ∨ z = h) d.snd))) =
      (fun d : G.Dart => decide (¬((A d.fst ∨ d.fst = h) ↔ (A d.snd ∨ d.snd = h)))) := rfl
    rw [this] at c2
    convert_to _ ≤ _ at c2
    omega
  · intro d hd
    simp only [decide_eq_true_eq]
    rintro ⟨h1, h2⟩
    by_cases hf : d.fst = h
    · rw [hf] at h1 h2; tauto
    by_cases hs : d.snd = h
    · rw [hs] at h1 h2; tauto
    exact h1 (hno d hd hf hs)
  · intro d hd
    simp only [decide_eq_true_eq, Bool.or_eq_true]
    rintro (h1 | h1)
    · by_contra hc
      simp only [not_or] at hc
      exact h1 (hno d hd hc.1 hc.2)
    · by_contra hc
      simp only [not_or] at hc
      apply h1
      have := hno d hd hc.1 hc.2
      simp [hc.1, hc.2, this]

/-- If every dart of the cycle `p` crossing `A` lies on the single edge `e`, then `p` stays on
one side of `A`. -/
lemma cycle_cut_one {u : V} {p : G.Walk u u} (hp : p.IsCycle) (A : V → Prop)
    [DecidablePred A] (e : Sym2 V) (hcross : ∀ d ∈ p.darts, ¬(A d.fst ↔ A d.snd) → d.edge = e)
    {x y : V} (hx : x ∈ p.support) (hy : y ∈ p.support) (hAx : A x) (hAy : ¬A y) : False := by
  have c1 := two_le_crossCount A p hx hy hAx hAy
  have hnd := hp.edges_nodup
  rw [List.nodup_iff_count_le_one] at hnd
  have c2 := hnd e
  rw [Walk.edges, List.count_eq_countP, List.countP_map] at c2
  have c3 : crossCount A p ≤ p.darts.countP ((fun x => x == e) ∘ Dart.edge) := by
    unfold crossCount
    apply List.countP_mono_left
    intro d hd h1
    simp only [decide_eq_true_eq] at h1
    simp [hcross d hd h1]
  omega

omit [DecidableEq V] in
/-- The set of neighbours of `w` along a cycle has exactly two elements. -/
lemma cycle_nbrs_ncard {u : V} {p : G.Walk u u} (hp : p.IsCycle) {w : V} (hw : w ∈ p.support) :
    {x | s(w, x) ∈ p.edges}.ncard = 2 := by
  have := hp.ncard_neighborSet_toSubgraph_eq_two hw
  convert this using 2
  ext x
  simp [Subgraph.mem_neighborSet, ← Subgraph.mem_edgeSet]

lemma cycle_nbrs_card_le_two [Fintype V] {u : V} {p : G.Walk u u} (hp : p.IsCycle) (w : V) :
    (univ.filter (fun x => s(w, x) ∈ p.edges)).card ≤ 2 := by
  by_cases hw : w ∈ p.support
  · rw [← Set.ncard_coe_finset, ← cycle_nbrs_ncard hp hw]
    simp
  · have : univ.filter (fun x => s(w, x) ∈ p.edges) = ∅ := by
      ext x
      simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro hx
      exact hw (p.fst_mem_support_of_mem_edges hx)
    simp [this]

/-- If a vertex `w` of a cycle has all its neighbours in a set `T` of size at most `3`, and
the edge `wy` (with `y ∈ T`) is not used by the cycle, then the cycle uses `wz` for every other
`z ∈ T`. -/
lemma cycle_deg_three_other {u : V} {p : G.Walk u u} (hp : p.IsCycle) {w : V}
    (hw : w ∈ p.support) (T : Finset V) (hT : T.card ≤ 3) (hnb : ∀ x, G.Adj w x → x ∈ T)
    {y : V} (hyT : y ∈ T) (hy : s(w, y) ∉ p.edges) {z : V} (hzT : z ∈ T) (hzy : z ≠ y) :
    s(w, z) ∈ p.edges := by
  have h2 := cycle_nbrs_ncard hp hw
  have hsub : {x | s(w, x) ∈ p.edges} ⊆ ((T.erase y : Finset V) : Set V) := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    simp only [coe_erase, Set.mem_diff, mem_coe, Set.mem_singleton_iff]
    refine ⟨hnb x (p.adj_of_mem_edges hx), ?_⟩
    rintro rfl; exact hy hx
  have hc : (T.erase y).card ≤ 2 := by
    rw [card_erase_of_mem hyT]; omega
  have heq : {x | s(w, x) ∈ p.edges} = ((T.erase y : Finset V) : Set V) := by
    apply Set.eq_of_subset_of_ncard_le hsub
    · rw [Set.ncard_coe_finset]; omega
  have : z ∈ ((T.erase y : Finset V) : Set V) := by simp [hzT, hzy]
  rw [← heq] at this
  exact this

end Erdos907
