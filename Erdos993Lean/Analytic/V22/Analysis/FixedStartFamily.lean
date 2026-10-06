import Erdos993Lean.Analytic.V22.Analysis.SpikedWindowBridge
import Erdos993Lean.Analytic.V22.WindowTransportFromPointwise
import Erdos993Lean.Analytic.V22.Checks.Independent
import Erdos993Lean.Analytic.V22.Checks.Main
import Erdos993Lean.Analytic.V22.Analysis.InterfaceDefinitions

/-!
# The actual original-start family and the Section 7 transport

This adapter consumes E's independent all-integer fiber lower family at the
exact mean `M / t`. It retains D's native class, original spike cell, block,
both activity halves, and all integer offsets. The local start hypotheses
are explicit in `FixedStartFiberLowerFamily`; neither the B3 price nor
`FiniteChecks` is assumed when constructing the family.

D's marked-start helper and finite checks can consequently consume the
transport. The resulting bundle includes both the displayed Lemma 7.14
statement and its certified exports, in the exact order required by E's
`FiniteChecks`. This module does not import `FinalInterface`.
-/

namespace Erdos993Lean.Analytic.V22.Analysis

noncomputable section

/-- The retained all-offset object, with the actual mean and original start.
In particular there is no final `t ≥ tau` restriction on marked cells. -/
theorem fixedStartFiberLowerFamily : V22.FixedStartFiberLowerFamily := by
  refine ⟨?_⟩
  intro c hc cell hcell hid _hw hstart i hi t q M htpos hM ht hr hq hblock hmean j
  have hMn : 0 < M := by omega
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hMn
  have hinverse : (M : ℝ) / ((M : ℝ) / t) = t := by
    field_simp [hMr.ne', htpos.ne'] <;> ring
  have hactivity : V22.Checks.inCell cell.lo cell.hi
      ((M : ℝ) / ((M : ℝ) / t)) := by
    rw [hinverse]
    exact ht
  have hlocal := hstart |2*q-1| hr.1 hr.2
  have hpoint := (spike_window_original_start_family
    (M := M) (q := q) (mu := (M : ℝ) / t)
    hcell hc hid.symm hi hM hr hq hmean hactivity hblock
    hlocal.2.1 hlocal.2.2).1 j
  simpa only [spikeWindowMinimum,
    V22.Compute.SpikeWindowExprs.asWindowCell, hinverse] using hpoint

/-- The original-cell start license supplied by D independently of B3.
Its class and marked-cell fields are exactly those used by the family. -/
theorem fixedStartCheckedStartConditions
    {c : V22.V22Class} (hc : c ∈ V22.classes)
    {cell : V22.V22SpikeCell} (hcell : cell ∈ V22.spikeCells)
    (hid : cell.classId = c.classId) (hw : cell.window = true) :
    ∀ r : ℝ, (c.ra : ℝ) ≤ r → r ≤ (c.rb : ℝ) →
      V22.windowConditions r ((c.muD : ℝ) * (cell.lo : ℝ) + 2) ∧
        V22.persistentWindowConditions r ((c.muD : ℝ) * (cell.lo : ℝ) + 2) ∧
        0 < V22.uMonoDerivative r ((c.muD : ℝ) * (cell.lo : ℝ) + 2) := by
  intro r hra hrb
  exact V22.Checked.markedSpikeStartConditions cell hcell hw c hc hid.symm r ⟨hra, hrb⟩

/-- D's exact multiplier/infimum transport consumed from the actual family. -/
theorem fixedStartWindowPriceTransport :
    V22.Compute.SpikeWindowExprs.DeficitToWindowPriceTransport :=
  V22.transport_of_pointwise fixedStartFiberLowerFamily

/-- All Section 7 facts, including B3 and its certified exports, obtained
through the named analytic transport rather than an assumed finite bundle. -/
theorem fixedStartSection7Facts : V22.Checked.Section7Facts :=
  V22.Checked.checkedSection7 fixedStartWindowPriceTransport

/-- Lossless ordering adapter from D's record to E's conjunction. -/
theorem section7Facts_to_finiteChecks (h : V22.Checked.Section7Facts) :
    V22.FiniteChecks := by
  exact ⟨h.l7_1, h.l7_2, h.l7_3, h.l7_4, h.l7_5, h.l7_6,
    h.l7_7, h.l7_8, h.l7_9, h.l7_10, h.l7_11, h.l7_12,
    h.l7_13, h.l7_14, h.l7_14_certified, h.l7_15, h.l7_16,
    h.l7_17, h.l7_18, h.l7_19, h.l7_20, h.l7_21⟩

/-- The finite bundle required by the final E interface. No finite-check
hypothesis is introduced: the B3 dependency is the independent actual family. -/
theorem fixedStartFiniteChecks : V22.FiniteChecks :=
  section7Facts_to_finiteChecks fixedStartSection7Facts

end

end Erdos993Lean.Analytic.V22.Analysis
