import Erdos993Lean.Analytic.V22.Compute.SpikeBoundsChecks

/-! Every finite bound/guard for 7.14; actual fiber transport is a separate argument. -/
namespace Erdos993Lean.Analytic.V22.Checks.Evaluated

theorem spikeBounds : Compute.SpikeBoundsChecks.check = true := by
  native_decide

end Erdos993Lean.Analytic.V22.Checks.Evaluated
