import Erdos993Lean.Analytic.V22.Compute.GeneratedA2Data
import Erdos993Lean.Analytic.V22.GeneratedWingData
import Erdos993Lean.Analytic.V22.Compute.GeneratedWindowData
import Erdos993Lean.Analytic.V22.Compute.RayChecks
import Erdos993Lean.Analytic.V22.Compute.Rows
import Erdos993Lean.Analytic.V22.Compute.GeneratedSpikeWindowData

/-! Draft compiled-evaluation declarations for generated finite certificates.
This module imports pure computation only. The lane's serial Lean queue must
validate every declaration; real soundness consumers live in a separate file.
The nonwindow B3 evaluation does not assert the full marked-cell statement.
-/

namespace Erdos993Lean.Analytic.V22.Checks.Evaluated

theorem a2 : Compute.A2Checks.check Compute.GeneratedA2Data.candidates = true := by
  native_decide

theorem c1 : Compute.GeneratedWingData.checked = true := by
  native_decide

theorem d3 : Compute.WindowCellChecks.check Compute.GeneratedWindowData.candidates = true := by
  native_decide

theorem b3Nonwindow : Compute.RayChecks.generatedNonwindowOK = true := by
  native_decide

theorem rows : Compute.Rows.check = true := by
  native_decide

/-- Independent marked-cell price evaluation; no full B3 consumer is asserted here. -/
theorem spikeWindowPrice : Compute.GeneratedSpikeWindowData.check = true := by
  native_decide

end Erdos993Lean.Analytic.V22.Checks.Evaluated
