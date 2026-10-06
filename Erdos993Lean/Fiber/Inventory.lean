import Mathlib
import Erdos993Lean.Statement
import Erdos993Lean.Zhang.Konig
import Erdos993Lean.Zhang.CoefficientBounds
import Erdos993Lean.Zhang.Rows.Basic

/-!
# The fiber inventory `N[y, m]`

Source: the 29 Sep binomial-fiber return, Sections 2–4 and 6 (Lean lane FIBER-C).  Fix a finite
vertex set `s` of a graph `G` and an independent `A ⊆ s` of **maximum** cardinality
(`a = |A| = α(G[s])`); put `C = s \ A`, `c = |C|`.  For an independent `J ⊆ C`, `y(J) = |J|` and
`m(J) = |A \ N(J)|` (Zhang's `(Zhang.avail G A J).card`); `N[y, m]` is the number of independent
`J ⊆ C` with `y(J) = y`, `m(J) = m` (Zhang's `Zhang.tCount G s A y m`).  This file packages, for
this fixed `A`, the fiber-inventory facts both proof programs need:

* **F1** (count form of the atlas): `Zhang.indepPoly_decomposition`/`indepCount_decomposition`
  already give it; here it is restated as a coefficient count on the whole vertex set.
* **F2** (support and normalization): the support bound `m(J) ≤ a − |J|`, the empty fiber
  `t_{0,m} = [m = a]`, and the singleton row `Σ_m N[1, m] = c`.
* **F6** (the two counting rows): `c_2 = C(n, 2) − e(F)` and the forest edge bound `e(F) ≤ n − 1`,
  both restated with Mathlib's `SimpleGraph.edgeFinset`; the subset cap `N_h ≤ C(c, h)`.
* **F7** (the shadow inequality): for `D_q = {J independent ⊆ C : m(J) ≥ q}` (down-closed under
  deleting a vertex of `J`, since `avail` is antitone), `(h+1) N_{h+1}^{≥q} ≤ (c−h) N_h^{≥q}` for
  `h < c`.

Everything is either Zhang's own `Zhang.Decomposition`/`Zhang.CoefficientBounds`/
`Zhang.Rows.EdgeCount`/`Zhang.Rows.Basic` machinery, restated for the fixed `A`, or (F7) built on
`Zhang.Rows.sum_sum_erase_le`.

Grade: PROVED IN LEAN (complete proofs, standard axioms only).
-/

namespace Erdos993Lean
namespace Fiber

open Finset Zhang Zhang.Rows
open scoped Classical

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Preliminaries: maximum independent sets -/

omit [DecidableEq V] in
/-- `A` has maximum cardinality among the independent subsets of `s` (`∀ independent S ⊆ s,
S.card ≤ A.card`) iff `A.card = α(G[s])`, for `A` independent, `A ⊆ s`. -/
theorem isMax_iff_card_eq_alphaIn {s A : Finset V} (hA : IsIndepFinset G A) (hAs : A ⊆ s) :
    (∀ S ⊆ s, IsIndepFinset G S → S.card ≤ A.card) ↔ A.card = alphaIn G s := by
  constructor
  · intro hmax
    obtain ⟨T, hTs, hTi, hTc⟩ := exists_alphaIn G s
    have h1 := hmax T hTs hTi
    rw [hTc] at h1
    exact le_antisymm (le_alphaIn hAs hA) h1
  · intro heq S hSs hSi
    rw [heq]
    exact le_alphaIn hSs hSi

/-! ### F1: the count form of the atlas -/

section Fintype

variable [Fintype V]

/-- **(F1)**: for an independent `A` (maximality is not needed for this identity — it is the
standing hypothesis for F2–F7 below, but `indepCount_decomposition` does not use it),
`(G.indepSetFinset r).card = Σ_{J ⊆ C, J independent} C(m(J), r − |J|)`, `C = univ \ A`
(Zhang's `indepCount_decomposition`, specialized to `s = univ`). -/
theorem indepSetFinset_card_eq_sum_fiber {A : Finset V} (hA : IsIndepFinset G A) (r : ℕ) :
    (G.indepSetFinset r).card =
      ∑ J ∈ (Finset.univ \ A).powerset.filter (IsIndepFinset G),
        if J.card ≤ r then (avail G A J).card.choose (r - J.card) else 0 := by
  rw [← indepCount_univ]
  exact indepCount_decomposition hA (Finset.subset_univ A) r

end Fintype

/-! ### F2: support and normalization of `N[y, m]` -/

/-- **(F2, support)**: for a maximum independent `A ⊆ s` and an independent `J ⊆ s \ A`,
`m(J) ≤ a − |J|` (Zhang's `card_avail_add_card_le`, rewritten with `A.card` in place of
`alphaIn G s` via the maximality hypothesis). -/
theorem card_avail_le_card_sub_card {s A : Finset V} (hA : IsIndepFinset G A) (hAs : A ⊆ s)
    (hAmax : A.card = alphaIn G s) {J : Finset V} (hJ : J ⊆ s \ A) (hJi : IsIndepFinset G J) :
    (avail G A J).card ≤ A.card - J.card := by
  have h := card_avail_add_card_le hA hAs hJ hJi
  rw [← hAmax] at h
  omega

/-- **(F2, empty fiber)**: `N[0, m] = [m = a]` — the only independent `J ⊆ s \ A` of size `0` is
`∅`, and there `m(∅) = a` (Zhang's `tCount_zero`). -/
theorem fiber_zero (s A : Finset V) (m : ℕ) :
    tCount G s A 0 m = if m = A.card then 1 else 0 :=
  tCount_zero s A m

omit [DecidableEq V] in
/-- The witness behind `fiber_zero`: an independent `J ⊆ s \ A` of size `0` is `∅`, with
`m(∅) = a` (Zhang's `avail_card_eq_of_card_zero`). -/
theorem eq_empty_and_avail_card_of_card_eq_zero {A J : Finset V} (hJ : J.card = 0) :
    J = ∅ ∧ (avail G A J).card = A.card :=
  ⟨Finset.card_eq_zero.mp hJ, avail_card_eq_of_card_zero hJ⟩

/-- **(F2, singleton row)**: `Σ_m N[1, m] = c` — every singleton of `s \ A` is independent
(Zhang's `sum_tCount_one`). -/
theorem sum_fiber_one (s A : Finset V) :
    ∑ m ∈ range (A.card + 1), tCount G s A 1 m = (s \ A).card :=
  sum_tCount_one s A

/-! ### F6: the two counting rows -/

/-- **(F6, iii)**: the subset cap `N_h ≤ C(c, h)` for independent `J ⊆ C` of size `h`, where
`N_h = Σ_m N[h, m]` (Zhang's `sum_tCount_le_choose`). -/
theorem card_fiber_row_le_choose (s A : Finset V) (h : ℕ) :
    ∑ m ∈ range (A.card + 1), tCount G s A h m ≤ (s \ A).card.choose h :=
  sum_tCount_le_choose s A h

section EdgeBridge

omit [DecidableRel G.Adj] in
/-- Two distinct vertices form an independent pair iff they are not adjacent. -/
theorem isIndepFinset_pair_iff {a b : V} (hab : a ≠ b) :
    IsIndepFinset G {a, b} ↔ ¬ G.Adj a b := by
  constructor
  · intro h hadj
    exact h a (Finset.mem_insert_self _ _) b
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) hadj
  · intro hnadj x hx y hy hxy
    rw [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact G.irrefl hxy
    · exact hnadj hxy
    · exact hnadj hxy.symm
    · exact G.irrefl hxy

variable [Fintype V]

/-- **(F6, edge bridge)**: Mathlib's `edgeFinset` agrees with Zhang's induced-edge count `eIn`
on the whole vertex set (`eIn` counts non-independent `2`-subsets; both count the edges of
`G`). -/
theorem card_edgeFinset_eq_eIn_univ : G.edgeFinset.card = eIn G (Finset.univ : Finset V) := by
  apply Finset.card_bij (fun e (_ : e ∈ G.edgeFinset) => (e : Sym2 V).toFinset)
  · intro e he
    obtain ⟨a, b⟩ := e
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    rw [mem_edgesIn]
    refine ⟨Finset.subset_univ _, ?_, ?_⟩
    · rw [Sym2.toFinset_mk_eq]
      exact Finset.card_pair (G.ne_of_adj he)
    · rw [Sym2.toFinset_mk_eq, isIndepFinset_pair_iff (G.ne_of_adj he)]
      exact fun h => h he
  · intro e he e' he' heq
    obtain ⟨a, b⟩ := e
    obtain ⟨a', b'⟩ := e'
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he he'
    rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq] at heq
    have hab : a ≠ b := G.ne_of_adj he
    have hab' : a' ≠ b' := G.ne_of_adj he'
    have ha : a ∈ ({a', b'} : Finset V) := heq ▸ Finset.mem_insert_self a {b}
    rw [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · have hb : b ∈ ({a, b'} : Finset V) :=
        heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
      rw [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb
      · exact absurd hb.symm hab
      · rw [hb]
    · have hb : b ∈ ({a', a} : Finset V) :=
        heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
      rw [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb
      · rw [hb]; exact Sym2.eq_swap
      · exact absurd hb.symm hab
  · intro p hp
    rw [mem_edgesIn] at hp
    obtain ⟨-, hpc, hpni⟩ := hp
    obtain ⟨a, b, hab, hpeq⟩ := Finset.card_eq_two.mp hpc
    rw [hpeq] at hpni
    have hadj : G.Adj a b := by
      by_contra hnadj
      exact hpni ((isIndepFinset_pair_iff hab).mpr hnadj)
    refine ⟨Sym2.mk (a, b), ?_, ?_⟩
    · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact hadj
    · rw [Sym2.toFinset_mk_eq, hpeq]

/-- **(F6, i)**, whole-graph form: `T_2 + e(G) = C(v, 2)` restated with Mathlib's `edgeFinset`
(Zhang's `indepCount_two_add_eIn`, specialized to `s = univ` via the edge bridge). -/
theorem indepSetFinset_two_add_card_edgeFinset :
    (G.indepSetFinset 2).card + G.edgeFinset.card = (Fintype.card V).choose 2 := by
  rw [← indepCount_univ, card_edgeFinset_eq_eIn_univ, ← Finset.card_univ (α := V)]
  exact indepCount_two_add_eIn (Finset.univ : Finset V)

/-- **(F6, ii)**, whole-graph form: the forest edge bound restated via `edgeFinset` (Zhang's
`eIn_le_card_sub_one`). -/
theorem card_edgeFinset_le_card_sub_one (hG : G.IsAcyclic) :
    G.edgeFinset.card ≤ Fintype.card V - 1 := by
  rw [card_edgeFinset_eq_eIn_univ, ← Finset.card_univ (α := V)]
  exact eIn_le_card_sub_one hG Finset.univ

end EdgeBridge

/-- **(F6, i)** for the package's `FiniteForest`: `independenceCount F 2 + e(F) = C(n, 2)`,
`e(F) = F.graph.edgeFinset.card`. -/
theorem independenceCount_two_add_card_edgeFinset (F : FiniteForest) :
    independenceCount F 2 + F.graph.edgeFinset.card = F.n.choose 2 := by
  have h := indepSetFinset_two_add_card_edgeFinset (G := F.graph)
  rw [Fintype.card_fin] at h
  unfold independenceCount
  exact h

/-- **(F6, ii)** for the package's `FiniteForest`: `e(F) ≤ n − 1`. -/
theorem card_edgeFinset_le_sub_one (F : FiniteForest) :
    F.graph.edgeFinset.card ≤ F.n - 1 := by
  have h := card_edgeFinset_le_card_sub_one (G := F.graph) F.isForest
  rwa [Fintype.card_fin] at h

/-- **(F6, i)+(ii) corollary**: `C(n, 2) − (n − 1) ≤ independenceCount F 2` for `n ≥ 1`. -/
theorem choose_two_sub_le_independenceCount (F : FiniteForest) (_hn : 1 ≤ F.n) :
    F.n.choose 2 - (F.n - 1) ≤ independenceCount F 2 := by
  have h1 := independenceCount_two_add_card_edgeFinset F
  have h2 := card_edgeFinset_le_sub_one F
  omega

/-! ### F7: the shadow inequality -/

omit [DecidableEq V] in
/-- `avail` is antitone in `J`: shrinking `J` can only add available vertices. -/
theorem avail_antitone {A J J' : Finset V} (h : J' ⊆ J) : avail G A J ⊆ avail G A J' := by
  intro i hi
  rw [mem_avail] at hi ⊢
  exact ⟨hi.1, fun y hy => hi.2 y (h hy)⟩

omit [DecidableEq V] in
theorem card_avail_le_of_subset {A J J' : Finset V} (h : J' ⊆ J) :
    (avail G A J).card ≤ (avail G A J').card :=
  Finset.card_le_card (avail_antitone h)

variable (G) in
/-- **The shadow row** `N_h^{≥q}`: the independent `J ⊆ s \ A` of size `h` with `m(J) ≥ q`.
`D_q = {J : m(J) ≥ q}` is down-closed under deleting a vertex of `J`, since `avail` is
antitone. -/
def shadowRow (s A : Finset V) (h q : ℕ) : Finset (Finset V) :=
  (indepSets G (s \ A) h).filter (fun J => q ≤ (avail G A J).card)

/-- **(F7, the shadow inequality)**: `(h+1) N_{h+1}^{≥q} ≤ (c−h) N_h^{≥q}` for `h < c = |s \ A|`.
Double counting the pairs `(J, v)` with `J` independent of size `h+1` in `D_q` and `v ∈ J`: each
such `J` gives `h+1` pairs, and `J.erase v ∈ D_q` (by antitonicity) has size `h` and at most
`c − h` extensions back to a set of size `h + 1` (`Zhang.Rows.sum_sum_erase_le`). -/
theorem shadow_ineq {s A : Finset V} {h q : ℕ} (hh : h < (s \ A).card) :
    (h + 1) * (shadowRow G s A (h + 1) q).card ≤
      ((s \ A).card - h) * (shadowRow G s A h q).card := by
  have hmono : ∀ (J : Finset V) (v : V),
      (if q ≤ (avail G A J).card then (1 : ℚ) else 0) ≤
        (if q ≤ (avail G A (J.erase v)).card then (1 : ℚ) else 0) := by
    intro J v
    by_cases hJ : q ≤ (avail G A J).card
    · rw [if_pos hJ, if_pos (le_trans hJ (card_avail_le_of_subset (Finset.erase_subset v J)))]
    · rw [if_neg hJ]
      split_ifs <;> norm_num
  have hstep : ∀ J ∈ indepSets G (s \ A) (h + 1),
      ((h : ℚ) + 1) * (if q ≤ (avail G A J).card then (1 : ℚ) else 0) ≤
        ∑ v ∈ J, (if q ≤ (avail G A (J.erase v)).card then (1 : ℚ) else 0) := by
    intro J hJ
    obtain ⟨-, hJc, -⟩ := mem_indepSets.mp hJ
    calc ((h : ℚ) + 1) * (if q ≤ (avail G A J).card then (1 : ℚ) else 0)
        = ∑ _v ∈ J, (if q ≤ (avail G A J).card then (1 : ℚ) else 0) := by
          rw [Finset.sum_const, nsmul_eq_mul, hJc]
          push_cast
          ring
      _ ≤ ∑ v ∈ J, (if q ≤ (avail G A (J.erase v)).card then (1 : ℚ) else 0) :=
          Finset.sum_le_sum (fun v _ => hmono J v)
  have hsum1 : ((h : ℚ) + 1) * ∑ J ∈ indepSets G (s \ A) (h + 1),
      (if q ≤ (avail G A J).card then (1 : ℚ) else 0) ≤
      ∑ J ∈ indepSets G (s \ A) (h + 1), ∑ v ∈ J,
        (if q ≤ (avail G A (J.erase v)).card then (1 : ℚ) else 0) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hstep
  have herase := sum_sum_erase_le (G := G) (s \ A) h
    (fun K => if q ≤ (avail G A K).card then (1 : ℚ) else 0)
    (fun K _ => by dsimp only; split_ifs <;> norm_num)
  have hchain : ((h : ℚ) + 1) * ∑ J ∈ indepSets G (s \ A) (h + 1),
      (if q ≤ (avail G A J).card then (1 : ℚ) else 0) ≤
      (((s \ A).card : ℚ) - h) * ∑ K ∈ indepSets G (s \ A) h,
        (if q ≤ (avail G A K).card then (1 : ℚ) else 0) := le_trans hsum1 herase
  have heq1 : ∑ J ∈ indepSets G (s \ A) (h + 1), (if q ≤ (avail G A J).card then (1 : ℚ) else 0) =
      ((shadowRow G s A (h + 1) q).card : ℚ) := by
    unfold shadowRow
    rw [Finset.sum_boole]
  have heq2 : ∑ K ∈ indepSets G (s \ A) h, (if q ≤ (avail G A K).card then (1 : ℚ) else 0) =
      ((shadowRow G s A h q).card : ℚ) := by
    unfold shadowRow
    rw [Finset.sum_boole]
  rw [heq1, heq2] at hchain
  have hcast : (((s \ A).card : ℚ) - (h : ℚ)) = (((s \ A).card - h : ℕ) : ℚ) := by
    rw [Nat.cast_sub hh.le]
  rw [hcast] at hchain
  exact_mod_cast hchain

end Fiber
end Erdos993Lean
