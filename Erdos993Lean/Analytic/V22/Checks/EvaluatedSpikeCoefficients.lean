import Erdos993Lean.Analytic.V22.Compute.GeneratedSpikeCoefficientData

/-! Complete compiled coefficient checks, separately from any fiber transport. -/
namespace Erdos993Lean.Analytic.V22.Checks.Evaluated

theorem spikeCoefficients : Compute.GeneratedSpikeCoefficientData.check = true := by
  native_decide

end Erdos993Lean.Analytic.V22.Checks.Evaluated
