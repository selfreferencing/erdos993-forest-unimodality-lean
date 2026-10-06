import Erdos993Lean.Analytic.V22.Checks.EvaluatedSpikeCoefficients
import Erdos993Lean.Analytic.V22.Checks.EvaluatedSpikeBounds
import Erdos993Lean.Analytic.V22.SpikeCoefficientChecksSound
import Erdos993Lean.Analytic.V22.SpikeBoundsChecksSound

/-! Unconditional coefficient facts and exact conditional 7.14 consumers.
The analytic transport is an explicit argument; no instance is declared.
-/
namespace Erdos993Lean.Analytic.V22.Checked

theorem spikePhiCoefficientsValid :
    ∀ c ∈ spikeCells, ∀ i : Nat, i < 5 → ∀ t : ℝ,
      Checks.inCell c.lo c.hi t → Checks.spikePhiCoefficientsValid c i t :=
  Compute.SpikeCoefficientChecks.allOK_sound
    (Bool.and_eq_true_iff.mp Checks.Evaluated.spikeCoefficients).2

/-- Original marked-cell start hypotheses for the generic fixed-start
window comparison. This theorem does not require the fiber transport. -/
theorem markedSpikeStartConditions :
    ∀ cell ∈ spikeCells, cell.window = true → ∀ c ∈ classes,
      c.classId = cell.classId → ∀ r : ℝ, Checks.inCell c.ra c.rb r →
      windowConditions r ((c.muD : ℝ) * (cell.lo : ℝ) + 2) ∧
        persistentWindowConditions r ((c.muD : ℝ) * (cell.lo : ℝ) + 2) ∧
        0 < uMonoDerivative r ((c.muD : ℝ) * (cell.lo : ℝ) + 2) := by
  intro cell hcell hw c hc hid r hr
  have hp := Compute.SpikeBoundsChecks.markedClassOK_of_check
    Checks.Evaluated.spikeBounds hcell hw hc hid
  exact Compute.SpikeBoundsChecks.startOK_sound (Bool.and_eq_true_iff.mp hp).1 hr

/-- Lemma 7.14, with the exact analytical window transport supplied by E/F. -/
theorem lemma_7_14
    (transport : Compute.SpikeWindowExprs.DeficitToWindowPriceTransport) :
    Checks.lemma_7_14 :=
  Compute.SpikeBoundsChecks.lemma_7_14_of_check transport Checks.Evaluated.spikeBounds

/-- Certified six-digit exports with the same explicit analytical dependency. -/
theorem lemma_7_14_certified
    (transport : Compute.SpikeWindowExprs.DeficitToWindowPriceTransport) :
    Checks.lemma_7_14_certified :=
  Compute.SpikeBoundsChecks.lemma_7_14_certified_of_check transport Checks.Evaluated.spikeBounds

end Erdos993Lean.Analytic.V22.Checked
