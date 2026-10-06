import Erdos993Lean.Analytic.V22.Compute.SpikeWindowExprs
import Erdos993Lean.Analytic.V22.WindowCellChecksSound
import Erdos993Lean.Analytic.V22.WindowChecksSound
import Erdos993Lean.Analytic.V22.Checks.EarlyStatements

/-!
# Marked-spike price soundness and the named analytic consumer

The finite checker bounds the explicit original-cell window-price recipe
for every actual t and r. It does not assume that the fiber deficit is
bounded by that recipe. The latter is a separately named transport object,
consumed by Lemma 7.14(b), with the class, integer fiber, starting mean,
block, shape, and derivative hypotheses retained. No transport instance is
constructed here. Its analytic source chain is Lemmas 5.9--5.13,
Theorem 5.14 and Corollary 5.15 in lane E; Lemma 4.10(b) supplies
the rhoU comparison used there.
-/

namespace Erdos993Lean.Analytic.V22.Compute.SpikeWindowExprs

open Erdos993Lean.Analytic.TailCert
open WindowCellChecks
open Checks (inCell)
noncomputable section

def windowPrice (c : V22Class) (cell : V22SpikeCell) (t r : ℝ) : ℝ :=
  positivePart (Checks.classTarget c t + (bMax c cell : ℝ) *
    positivePart (-Checks.windowCellMinimum c (asWindowCell cell) t r))

theorem cellStart_cast (c : V22Class) (cell : V22SpikeCell) :
    (cellStart c cell : ℝ) = (c.muD : ℝ) * (cell.lo : ℝ) + 2 := by
  simp [cellStart]

theorem bMax_cast (c : V22Class) (cell : V22SpikeCell) :
    (bMax c cell : ℝ) = (cell.hi : ℝ) * ((c.muD : ℝ) * (cell.lo : ℝ) + 2) /
      ((c.muD : ℝ) * (cell.lo : ℝ)) := by
  simp [bMax, cellStart]

theorem pw_ge_windowPrice {c : V22Class} {cell : V22SpikeCell} {box : Box}
    {ts : Span} {t r : ℝ}
    (ht : (ts.1 : ℝ) ≤ t ∧ t ≤ (ts.2 : ℝ))
    (hr : (box.rSpan.1 : ℝ) ≤ r ∧ r ≤ (box.rSpan.2 : ℝ))
    (hlic : (if box.licensed then
      (WindowCellExprs.classConditionMargin c (asWindowCell cell) (.var 0) (.var 1)).nonnegativeOK
        (boxEnv ts box.rSpan) else true) = true)
    (hB : 0 ≤ (bMax c cell : ℝ)) :
    windowPrice c cell t r ≤ (pw c cell box).evalR (realBoxEnv t r) := by
  have hl : (lower c cell box).evalR (realBoxEnv t r) ≤
      Checks.windowCellMinimum c (asWindowCell cell) t r := recipe_le ht hr hlic
  have hn : positivePart (-Checks.windowCellMinimum c (asWindowCell cell) t r) ≤
      positivePart (-(lower c cell box).evalR (realBoxEnv t r)) :=
    max_le_max (neg_le_neg hl) le_rfl
  have hprod := mul_le_mul_of_nonneg_left hn hB
  have hsum := add_le_add (le_refl (Checks.classTarget c t)) hprod
  have hprice := max_le_max hsum (le_refl (0 : ℝ))
  simpa [windowPrice, pw, Expr.evalR, realBoxEnv, Checks.classTarget,
    EarlyCoefficients.positivePart, positivePart] using hprice

theorem boxPass_sound {c : V22Class} {cell : V22SpikeCell} {bound : Rat}
    {ts : Span} {box : Box} {t r : ℝ}
    (hpass : boxPass c cell bound ts box = true)
    (ht : (ts.1 : ℝ) ≤ t ∧ t ≤ (ts.2 : ℝ))
    (hr : (box.rSpan.1 : ℝ) ≤ r ∧ r ≤ (box.rSpan.2 : ℝ)) :
    windowPrice c cell t r ≤ (bound : ℝ) := by
  simp only [boxPass, Bool.and_eq_true] at hpass
  have hB := (Expr.rat (bMax c cell)).nonnegativeOK_sound (boxEnv_mem ht hr) hpass.1.2
  have hm := (pwMargin c cell bound box).nonnegativeOK_sound (boxEnv_mem ht hr) hpass.2
  have hprice := pw_ge_windowPrice ht hr hpass.1.1 (by simpa [Expr.evalR] using hB)
  simp only [pwMargin, Expr.evalR] at hm
  linarith

/-- This is an unconditional numerical bound on the explicit recipe, on
the complete original t/r cell. It does not identify a fiber deficit. -/
theorem cellPass_sound {c : V22Class} {cell : V22SpikeCell} {bound : Rat} {cert : Certificate}
    (hpass : cellPass c cell bound cert = true) {t r : ℝ}
    (ht : (cell.lo : ℝ) ≤ t ∧ t ≤ (cell.hi : ℝ))
    (hr : (c.ra : ℝ) ≤ r ∧ r ≤ (c.rb : ℝ)) : windowPrice c cell t r ≤ (bound : ℝ) := by
  simp only [cellPass, Bool.and_eq_true] at hpass
  obtain ⟨ts, hts, ht'⟩ := partitionFrom_covers hpass.1 ht
  obtain ⟨row, hrow, heq⟩ := List.mem_map.mp hts
  subst ts
  have hp := List.all_eq_true.mp hpass.2 row hrow
  simp only [rowPass, Bool.and_eq_true] at hp
  obtain ⟨rs, hrs, hr'⟩ := partitionFrom_covers hp.1 hr
  obtain ⟨box, hbox, heq⟩ := List.mem_map.mp hrs
  subst rs
  exact boxPass_sound (List.all_eq_true.mp hp.2 box hbox) ht' hr'

theorem startPass_sound {c : V22Class} {cell : V22SpikeCell} {pieces : List Span}
    (h : startPass c cell pieces = true) {r : ℝ}
    (hr : (c.ra : ℝ) ≤ r ∧ r ≤ (c.rb : ℝ)) :
    windowConditions r (cellStart c cell : ℝ) ∧
      persistentWindowConditions r (cellStart c cell : ℝ) ∧
      0 < uMonoDerivative r (cellStart c cell : ℝ) := by
  simp only [startPass, Bool.and_eq_true] at h
  have hcover := h.1.1.1.1.1
  have h1 : 0 < 1 - ZL r (cellStart c cell : ℝ) 3 := by
    simpa [Expr.evalR, realSpanEnv] using positiveOn_sound hcover h.1.1.1.1.2 hr
  have h2 : 0 < 1 - (r + ZR r (cellStart c cell : ℝ) 3) := by
    simpa [Expr.evalR, realSpanEnv] using positiveOn_sound hcover h.1.1.1.2 hr
  have h3 : 0 ≤ 12 * (1 - (r + ZR r (cellStart c cell : ℝ) 3)^2) /
      ((1-r^2)*rho (cellStart c cell : ℝ)) - 3 := by
    simpa [Expr.evalR, realSpanEnv] using nonnegativeOn_sound hcover h.1.1.2 hr
  have hp : 0 ≤ 12 * (1 - (r + ZR r (cellStart c cell : ℝ) 3)^2) / (1-r^2) - 3 := by
    simpa [Expr.evalR, realSpanEnv] using nonnegativeOn_sound hcover h.1.2 hr
  have hd : 0 < uMonoDerivative r (cellStart c cell : ℝ) := by
    simpa [Expr.evalR, realSpanEnv] using positiveOn_sound hcover h.2 hr
  exact ⟨⟨by linarith, by linarith, by linarith⟩,
    ⟨by linarith, by linarith, by linarith⟩, hd⟩

/-- Named analytic transport still to be produced by lane E. The finite
price checker above does not provide this fiber-infimum inequality. -/
structure DeficitToWindowPriceTransport : Prop where
  bound : ∀ c ∈ classes, ∀ cell ∈ spikeCells, cell.classId = c.classId → cell.window = true →
    (∀ r : ℝ, (c.ra : ℝ) ≤ r → r ≤ (c.rb : ℝ) →
      windowConditions r ((c.muD : ℝ)*(cell.lo : ℝ)+2) ∧
        persistentWindowConditions r ((c.muD : ℝ)*(cell.lo : ℝ)+2) ∧
        0 < uMonoDerivative r ((c.muD : ℝ)*(cell.lo : ℝ)+2)) →
    ∀ i : Nat, i < 5 → ∀ (t q : ℝ) (M : Nat), 0 < t → 8 ≤ M →
      inCell cell.lo cell.hi t → inCell c.ra c.rb |2*q-1| → inCell (1/4) (3/4) q →
      inSpikeBlock cell i M → (c.muD : ℝ) ≤ (M : ℝ)/t →
      deficitG q ((M : ℝ)/t) c.b c.beta M ≤ windowPrice c cell t |2*q-1|

/-- Conditional consumer only: no instance of the analytic transport is
assumed discharged by the finite window-price certificate. -/
theorem marked_min_bound_of_transport (transport : DeficitToWindowPriceTransport)
    {c : V22Class} {cell : V22SpikeCell} {i : Nat} {cert : Certificate}
    (hc : c ∈ classes) (hcell : cell ∈ spikeCells) (hid : cell.classId = c.classId)
    (hw : cell.window = true)
    (hstart : ∀ r : ℝ, (c.ra : ℝ) ≤ r → r ≤ (c.rb : ℝ) →
      windowConditions r ((c.muD : ℝ)*(cell.lo : ℝ)+2) ∧
        persistentWindowConditions r ((c.muD : ℝ)*(cell.lo : ℝ)+2) ∧
        0 < uMonoDerivative r ((c.muD : ℝ)*(cell.lo : ℝ)+2))
    (hi : i < 5) (hpass : cellPass c cell (cell.logBounds.getD i 0) cert = true)
    {t q : ℝ} {M : Nat} (htpos : 0 < t) (hM : 8 ≤ M)
    (ht : inCell cell.lo cell.hi t) (hr : inCell c.ra c.rb |2*q-1|)
    (hq : inCell (1/4) (3/4) q) (hblock : inSpikeBlock cell i M)
    (hmu : (c.muD : ℝ) ≤ (M : ℝ)/t) :
    min (Checks.spikePhi cell i t M) (deficitG q ((M : ℝ)/t) c.b c.beta M) ≤
      (cell.logBounds.getD i 0 : ℝ) := by
  have hdef := transport.bound c hc cell hcell hid hw hstart i hi t q M htpos hM ht hr hq hblock hmu
  have hprice := cellPass_sound hpass ht hr
  exact (min_le_right _ _).trans (hdef.trans hprice)

end
end Erdos993Lean.Analytic.V22.Compute.SpikeWindowExprs
