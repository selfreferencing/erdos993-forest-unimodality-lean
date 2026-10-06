import Erdos993Lean.Analytic.V22.Compute.WindowCellChecks
import Erdos993Lean.Analytic.V22.GridSound
import Erdos993Lean.Analytic.V22.WindowCellExprsSound

/-! Exact box coverage and the complete guarded consumer of Lemma 7.20.
No candidate evaluation or numerical pass is asserted in this module. -/

namespace Erdos993Lean.Analytic.V22.Compute.WindowCellChecks

open Erdos993Lean.Analytic.TailCert WindowCellExprs
noncomputable section

def realBoxEnv (t r : ℝ) (i : Nat) : ℝ :=
  if i = 0 then t else if i = 1 then r else 0

theorem boxEnv_mem {ts rs : Span} {t r : ℝ}
    (ht : (ts.1 : ℝ) ≤ t ∧ t ≤ (ts.2 : ℝ))
    (hr : (rs.1 : ℝ) ≤ r ∧ r ≤ (rs.2 : ℝ)) :
    ∀ i, (boxEnv ts rs i).Mem (realBoxEnv t r i) := by
  intro i
  by_cases h0 : i = 0
  · simpa [boxEnv, realBoxEnv, h0] using spanI_mem ht
  · by_cases h1 : i = 1
    · simpa [boxEnv, realBoxEnv, h0, h1] using spanI_mem hr
    · simpa [boxEnv, realBoxEnv, h0, h1] using mem_ofRat (0 : Rat)

theorem recipe_le {c : V22Class} {cell : V22Cell} {box : Box} {ts : Span} {t r : ℝ}
    (ht : (ts.1 : ℝ) ≤ t ∧ t ≤ (ts.2 : ℝ))
    (hr : (box.rSpan.1 : ℝ) ≤ r ∧ r ≤ (box.rSpan.2 : ℝ))
    (hlic : (if box.licensed then
      (classConditionMargin c cell (.var 0) (.var 1)).nonnegativeOK (boxEnv ts box.rSpan)
      else true) = true) :
    (recipe c cell box).evalR (realBoxEnv t r) ≤ Checks.windowCellMinimum c cell t r := by
  cases hl : box.licensed with
  | false =>
    simpa [recipe, hl, Expr.evalR, realBoxEnv] using
      classLowerRecipe_le (realBoxEnv t r) (.var 0) (.var 1) c cell box.roots
  | true =>
    have hm : 0 ≤ (classConditionMargin c cell (.var 0) (.var 1)).evalR (realBoxEnv t r) :=
      Expr.nonnegativeOK_sound _ (boxEnv_mem ht hr) (by simpa [hl] using hlic)
    exact le_of_eq (by simpa [recipe, hl, Expr.evalR, realBoxEnv] using
      classLicensedRecipe_eq (realBoxEnv t r) (.var 0) (.var 1) c cell box.roots hm)

theorem margin_sound {c : V22Class} {cell : V22Cell} {box : Box} {ts : Span} {t r : ℝ}
    {req : Expr} (ht : (ts.1 : ℝ) ≤ t ∧ t ≤ (ts.2 : ℝ))
    (hr : (box.rSpan.1 : ℝ) ≤ r ∧ r ≤ (box.rSpan.2 : ℝ))
    (hlic : (if box.licensed then
      (classConditionMargin c cell (.var 0) (.var 1)).nonnegativeOK (boxEnv ts box.rSpan)
      else true) = true)
    (hm : (margin c cell box req).nonnegativeOK (boxEnv ts box.rSpan) = true) :
    req.evalR (realBoxEnv t r) ≤ Checks.windowCellMinimum c cell t r := by
  have hv := Expr.nonnegativeOK_sound _ (boxEnv_mem ht hr) hm
  have hl := recipe_le ht hr hlic
  simp only [margin, Expr.evalR] at hv
  linarith

def uniformSign (c : V22Class) (cell : V22Cell) : TargetMode → Prop
  | .positive => ∀ t : ℝ, (cell.lo : ℝ) ≤ t → t ≤ (cell.hi : ℝ) → 0 < Checks.classTarget c t
  | .negative => ∀ t : ℝ, (cell.lo : ℝ) ≤ t → t ≤ (cell.hi : ℝ) → Checks.classTarget c t ≤ 0
  | .crossing => True

theorem uniformSign_of_cellPasses {c : V22Class} {cell : V22Cell} {cert : CellCertificate}
    (h : cellPasses c cell cert = true) : uniformSign c cell cert.mode := by
  simp only [cellPasses, Bool.and_eq_true] at h
  cases hm : cert.mode with
  | positive =>
    intro t ht0 ht1
    obtain ⟨ts, hts, ht⟩ := partitionFrom_covers h.1 ⟨ht0, ht1⟩
    obtain ⟨row, hrow, heq⟩ := List.mem_map.mp hts
    subst ts
    have hp := (List.all_eq_true.mp h.2) row hrow
    simp only [rowPasses, Bool.and_eq_true] at hp
    have hs : (target c.b c.beta (.var 0)).positiveOK (spanEnv row.tSpan) = true := by
      simpa [signPasses, hm] using hp.1.2
    have hv := Expr.positiveOK_sound _ (spanEnv_mem ht) hs
    simpa [Expr.evalR, realSpanEnv, Checks.classTarget] using hv
  | negative =>
    intro t ht0 ht1
    obtain ⟨ts, hts, ht⟩ := partitionFrom_covers h.1 ⟨ht0, ht1⟩
    obtain ⟨row, hrow, heq⟩ := List.mem_map.mp hts
    subst ts
    have hp := (List.all_eq_true.mp h.2) row hrow
    simp only [rowPasses, Bool.and_eq_true] at hp
    have hs : (Expr.neg (target c.b c.beta (.var 0))).nonnegativeOK (spanEnv row.tSpan) = true := by
      simpa [signPasses, hm] using hp.1.2
    have hv := Expr.nonnegativeOK_sound _ (spanEnv_mem ht) hs
    simp [Expr.evalR, realSpanEnv] at hv
    unfold Checks.classTarget
    linarith
  | crossing => trivial

theorem cellPasses_sound {c : V22Class} {cell : V22Cell} {cert : CellCertificate}
    (h : cellPasses c cell cert = true) (t r : ℝ)
    (ht0 : (cell.lo : ℝ) ≤ t) (ht1 : t ≤ (cell.hi : ℝ))
    (hr0 : (c.ra : ℝ) ≤ r) (hr1 : r ≤ (c.rb : ℝ)) :
    (0 < Checks.classTarget c t → Checks.classTarget c t / t ≤ Checks.windowCellMinimum c cell t r) ∧
    (Checks.classTarget c t ≤ 0 →
      let N0 := (c.muD : ℝ) * (cell.lo : ℝ) + 2
      Checks.classTarget c t * (N0 - 2) / (t * N0) ≤ Checks.windowCellMinimum c cell t r) ∧
    (Checks.targetChangesSign c cell →
      max (Checks.classTarget c t / t) 0 ≤ Checks.windowCellMinimum c cell t r) := by
  have hs := uniformSign_of_cellPasses h
  simp only [cellPasses, Bool.and_eq_true] at h
  obtain ⟨ts, hts, ht⟩ := partitionFrom_covers h.1 ⟨ht0, ht1⟩
  obtain ⟨row, hrow, heq⟩ := List.mem_map.mp hts
  subst ts
  have hp := (List.all_eq_true.mp h.2) row hrow
  simp only [rowPasses, Bool.and_eq_true] at hp
  obtain ⟨rs, hrs, hr⟩ := partitionFrom_covers hp.1.1 ⟨hr0, hr1⟩
  obtain ⟨box, hbox, heq⟩ := List.mem_map.mp hrs
  subst rs
  have hb := (List.all_eq_true.mp hp.2) box hbox
  simp only [boxPasses, Bool.and_eq_true] at hb
  cases hm : cert.mode with
  | positive =>
    have hpR : Checks.classTarget c t / t ≤ Checks.windowCellMinimum c cell t r := by
      have hx := margin_sound ht hr hb.1.2 (by simpa [hm] using hb.2)
      simpa [Expr.evalR, realBoxEnv, Checks.classTarget] using hx
    have hsg : ∀ u : ℝ, (cell.lo : ℝ) ≤ u → u ≤ (cell.hi : ℝ) → 0 < Checks.classTarget c u := by
      simpa [uniformSign, hm] using hs
    refine ⟨fun _ => hpR, ?_, ?_⟩
    · intro hn
      exact False.elim (not_le_of_gt (hsg t ht0 ht1) hn)
    · intro hc
      obtain ⟨u, hu0, hu1, hun⟩ := hc.2
      exact False.elim (not_le_of_gt (hsg u hu0 hu1) hun)
  | negative =>
    have hnR : Checks.classTarget c t * ((cellStart c cell : ℝ) - 2) /
        (t * (cellStart c cell : ℝ)) ≤ Checks.windowCellMinimum c cell t r := by
      have hx := margin_sound ht hr hb.1.2 (by simpa [hm] using hb.2)
      simpa [Expr.evalR, realBoxEnv, Checks.classTarget] using hx
    have hsg : ∀ u : ℝ, (cell.lo : ℝ) ≤ u → u ≤ (cell.hi : ℝ) → Checks.classTarget c u ≤ 0 := by
      simpa [uniformSign, hm] using hs
    refine ⟨?_, ?_, ?_⟩
    · intro hp
      exact False.elim (not_lt_of_ge (hsg t ht0 ht1) hp)
    · intro _
      simpa only [cellStart_cast] using hnR
    · intro hc
      obtain ⟨u, hu0, hu1, hup⟩ := hc.1
      exact False.elim (not_lt_of_ge (hsg u hu0 hu1) hup)
  | crossing =>
    have hb3 :
        ((margin c cell box (positiveRequirement c.b c.beta (.var 0))).nonnegativeOK
          (boxEnv row.tSpan box.rSpan) = true ∧
        (margin c cell box (negativeRequirement (cellStart c cell) c.b c.beta (.var 0))).nonnegativeOK
          (boxEnv row.tSpan box.rSpan) = true) ∧
        (margin c cell box (crossingRequirement c.b c.beta (.var 0))).nonnegativeOK
          (boxEnv row.tSpan box.rSpan) = true := by
      simpa [hm, Bool.and_eq_true] using hb.2
    refine ⟨?_, ?_, ?_⟩
    · intro _
      have hx := margin_sound ht hr hb.1.2 hb3.1.1
      simpa [Expr.evalR, realBoxEnv, Checks.classTarget] using hx
    · intro _
      have hx := margin_sound ht hr hb.1.2 hb3.1.2
      simpa [Expr.evalR, realBoxEnv, Checks.classTarget, cellStart_cast] using hx
    · intro _
      have hx := margin_sound ht hr hb.1.2 hb3.2
      simpa [Expr.evalR, realBoxEnv, Checks.classTarget] using hx

theorem check_sound {data : V22Cell → CellCertificate} (h : check data = true) :
    Checks.lemma_7_20 := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  intro c hc cell hcell hid t r ht0 ht1 hr0 hr1
  have hp := (List.all_eq_true.mp ((List.all_eq_true.mp h.2) c hc)) cell hcell
  have hpass : cellPasses c cell (data cell) = true := by simpa [hid] using hp
  exact cellPasses_sound hpass t r ht0 ht1 hr0 hr1

theorem original_window_cell_count : windowCells.length = 54 := by rfl

end
end Erdos993Lean.Analytic.V22.Compute.WindowCellChecks
