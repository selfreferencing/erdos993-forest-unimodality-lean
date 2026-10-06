import Erdos993Lean.Analytic.V22.Compute.WindowChecks
import Erdos993Lean.Analytic.V22.WindowExprsSound
import Erdos993Lean.Analytic.V22.GridSound
import Erdos993Lean.Analytic.V22.Checks.LateStatements

/-!
# D1, D1′ and D2 checker soundness

A successful checker covers every actual activity in its exact class range.
Only checked enclosure and coverage facts are consumed here. No derivative
transport, numeric evaluation or displayed-margin substitution is assumed.
-/

namespace Erdos993Lean.Analytic.V22.Compute.WindowChecks

theorem d1GroupCount_eq : d1GroupCount = 8 := by decide
theorem d1PrimeGroupCount_eq : d1PrimeGroupCount = 15 := by decide
theorem d1PrimePhysicalCellCount_eq : d1PrimePhysicalCellCount = 14 := by decide
theorem d2GroupCount_eq : d2GroupCount = 8 := by decide

theorem classStart_cast (c : V22Class) :
    (classStart c : ℝ) = (c.muD : ℝ) * (c.tau : ℝ) + 2 := by
  simp [classStart]

theorem spikeStart_cast (c : V22Class) (cell : V22SpikeCell) :
    (spikeStart c cell : ℝ) = (c.muD : ℝ) * (cell.lo : ℝ) + 2 := by
  simp [spikeStart]

theorem d1AtOK_sound {c : V22Class} {N0 : Rat}
    (h : d1AtOK c N0 = true) {r : ℝ}
    (hr : (c.ra : ℝ) ≤ r ∧ r ≤ (c.rb : ℝ)) : windowConditions r (N0 : ℝ) := by
  simp only [d1AtOK, Bool.and_eq_true] at h
  have h1 : 0 < 1 - ZL r (N0 : ℝ) 3 := by
    simpa [Expr.evalR, realSpanEnv] using positiveOn_sound h.1.1.1 h.1.1.2 hr
  have h2 : 0 < 1 - (r + ZR r (N0 : ℝ) 3) := by
    simpa [Expr.evalR, realSpanEnv] using positiveOn_sound h.1.1.1 h.1.2 hr
  have h3 : 0 ≤ 12 * (1 - (r + ZR r (N0 : ℝ) 3)^2) /
      ((1 - r^2) * rho (N0 : ℝ)) - 3 := by
    simpa [Expr.evalR, realSpanEnv] using nonnegativeOn_sound h.1.1.1 h.2 hr
  exact ⟨by linarith, by linarith, by linarith⟩

theorem d1PrimeAtOK_sound {c : V22Class} {N0 : Rat}
    (h : d1PrimeAtOK c N0 = true) {r : ℝ}
    (hr : (c.ra : ℝ) ≤ r ∧ r ≤ (c.rb : ℝ)) : Checks.c3PrimeAt r (N0 : ℝ) := by
  simp only [d1PrimeAtOK, Bool.and_eq_true] at h
  have hm : 0 ≤ 12 * (1 - (r + ZR r (N0 : ℝ) 3)^2) / (1 - r^2) - 3 := by
    simpa [Expr.evalR, realSpanEnv] using nonnegativeOn_sound h.1 h.2 hr
  unfold Checks.c3PrimeAt
  linarith

theorem d2AtOK_sound {c : V22Class} {N0 : Rat}
    (h : d2AtOK c N0 = true) {r : ℝ}
    (hr : (c.ra : ℝ) ≤ r ∧ r ≤ (c.rb : ℝ)) : 0 < uMonoDerivative r (N0 : ℝ) := by
  simp only [d2AtOK, Bool.and_eq_true] at h
  simpa [Expr.evalR, realSpanEnv] using positiveOn_sound h.1 h.2 hr

/-- Full D1 checker success implies the exact closed statement 7.17. -/
theorem d1AllOK_sound (h : d1AllOK = true) : Checks.lemma_7_17 := by
  intro c hc r hra hrb
  have hp : d1ClassOK c = true := (List.all_eq_true.mp h) c hc
  simpa only [classStart_cast] using d1AtOK_sound hp ⟨hra, hrb⟩

/-- Full D1′ success retains every marked physical cell and class start. -/
theorem d1PrimeAllOK_sound (h : d1PrimeAllOK = true) : Checks.lemma_7_18 := by
  constructor
  · intro c hc r hra hrb
    have hp : d1PrimeClassOK c = true := (List.all_eq_true.mp h) c hc
    simp only [d1PrimeClassOK, Bool.and_eq_true] at hp
    simpa only [classStart_cast] using d1PrimeAtOK_sound hp.1 ⟨hra, hrb⟩
  · intro c hc cell hcell hid hwindow r hra hrb
    have hp : d1PrimeClassOK c = true := (List.all_eq_true.mp h) c hc
    simp only [d1PrimeClassOK, Bool.and_eq_true] at hp
    have hcellp : d1PrimeCellOK c cell = true := (List.all_eq_true.mp hp.2) cell hcell
    have hmarked : markedCellFor c cell = true := by
      simp [markedCellFor, hid, hwindow]
    simp [d1PrimeCellOK, hmarked] at hcellp
    simpa only [spikeStart_cast] using d1PrimeAtOK_sound hcellp ⟨hra, hrb⟩

/-- Full D2 checker success implies statement 7.19 at the exact starts. -/
theorem d2AllOK_sound (h : d2AllOK = true) : Checks.lemma_7_19 := by
  intro c hc r hra hrb
  have hp : d2ClassOK c = true := (List.all_eq_true.mp h) c hc
  simpa only [classStart_cast] using d2AtOK_sound hp ⟨hra, hrb⟩

end Erdos993Lean.Analytic.V22.Compute.WindowChecks
