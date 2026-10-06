import Erdos993Lean.Analytic.V22.Compute.Grid
import Erdos993Lean.Analytic.V22.ExprSound

/-! A passing rational partition certifies every point of the exact closed
range. This module proves coverage separately from numeric enclosure. -/

namespace Erdos993Lean.Analytic.V22.Compute
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute

noncomputable def realSpanEnv (x : ℝ) (i : Nat) : ℝ := if i = 0 then x else 0

theorem spanI_mem {s : Span} {x : ℝ} (hx : (s.1 : ℝ) ≤ x ∧ x ≤ (s.2 : ℝ)) :
    (spanI s).Mem x :=
  ⟨(mem_ofRat s.1).1.trans hx.1, hx.2.trans (mem_ofRat s.2).2⟩

theorem spanEnv_mem {s : Span} {x : ℝ} (hx : (s.1 : ℝ) ≤ x ∧ x ≤ (s.2 : ℝ)) :
    ∀ i, (spanEnv s i).Mem (realSpanEnv x i) := by
  intro i
  by_cases hi : i = 0
  · simpa [spanEnv, realSpanEnv, hi] using spanI_mem hx
  · simpa [spanEnv, realSpanEnv, hi] using mem_ofRat (0 : Rat)

/-- A checked contiguous list covers the whole requested closed interval. -/
theorem partitionFrom_covers {pieces : List Span} {start stop : Rat}
    (h : partitionFrom start stop pieces = true) {x : ℝ}
    (hx : (start : ℝ) ≤ x ∧ x ≤ (stop : ℝ)) :
    ∃ s ∈ pieces, (s.1 : ℝ) ≤ x ∧ x ≤ (s.2 : ℝ) := by
  induction pieces generalizing start with
  | nil => simp [partitionFrom] at h
  | cons a rest ih =>
    cases rest with
    | nil =>
      simp only [partitionFrom, Bool.and_eq_true, decide_eq_true_eq] at h
      refine ⟨a, by simp, ?_⟩
      simpa only [h.1.1, h.2] using hx
    | cons b rest =>
      change (decide (a.1 = start ∧ a.1 ≤ a.2) &&
        partitionFrom a.2 stop (b :: rest)) = true at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      by_cases hxa : x ≤ (a.2 : ℝ)
      · refine ⟨a, by simp, ?_, hxa⟩
        simpa only [h.1.1] using hx.1
      · obtain ⟨s, hs, hxs⟩ := ih h.2 ⟨le_of_not_ge hxa, hx.2⟩
        exact ⟨s, List.mem_cons_of_mem a hs, hxs⟩

theorem positiveOn_sound {e : Expr} {pieces : List Span} {start stop : Rat}
    (hcover : partitionFrom start stop pieces = true)
    (hpass : positiveOn e pieces = true) {x : ℝ}
    (hx : (start : ℝ) ≤ x ∧ x ≤ (stop : ℝ)) : 0 < e.evalR (realSpanEnv x) := by
  obtain ⟨s, hs, hxs⟩ := partitionFrom_covers hcover hx
  have hp : e.positiveOK (spanEnv s) = true := (List.all_eq_true.mp hpass) s hs
  exact e.positiveOK_sound (spanEnv_mem hxs) hp

theorem nonnegativeOn_sound {e : Expr} {pieces : List Span} {start stop : Rat}
    (hcover : partitionFrom start stop pieces = true)
    (hpass : nonnegativeOn e pieces = true) {x : ℝ}
    (hx : (start : ℝ) ≤ x ∧ x ≤ (stop : ℝ)) : 0 ≤ e.evalR (realSpanEnv x) := by
  obtain ⟨s, hs, hxs⟩ := partitionFrom_covers hcover hx
  have hp : e.nonnegativeOK (spanEnv s) = true := (List.all_eq_true.mp hpass) s hs
  exact e.nonnegativeOK_sound (spanEnv_mem hxs) hp

theorem upperOn_sound {e : Expr} {pieces : List Span} {start stop q : Rat}
    (hcover : partitionFrom start stop pieces = true)
    (hpass : upperOn e q pieces = true) {x : ℝ}
    (hx : (start : ℝ) ≤ x ∧ x ≤ (stop : ℝ)) : e.evalR (realSpanEnv x) ≤ (q : ℝ) := by
  obtain ⟨s, hs, hxs⟩ := partitionFrom_covers hcover hx
  have hp : e.upperOK (spanEnv s) q = true := (List.all_eq_true.mp hpass) s hs
  exact e.upperOK_sound q (spanEnv_mem hxs) hp

end Erdos993Lean.Analytic.V22.Compute
