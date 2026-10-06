import Erdos993Lean.Analytic.V22.Compute.A0D0
import Erdos993Lean.Analytic.V22.Compute.A1
import Erdos993Lean.Analytic.V22.Compute.B1

/-! Compiled Boolean checks. Every declaration checks the full stated rational
partition and all arithmetic/domain guards. Real soundness is separate. -/
namespace Erdos993Lean.Analytic.V22.Checks.Evaluated

theorem a0 : Compute.a0Pass = true := by native_decide

theorem a1 : Compute.A1.check = true := by native_decide

theorem d0 : classes.all Compute.d0Pass = true := by native_decide

theorem b1 : Compute.B1.check = true := by native_decide

end Erdos993Lean.Analytic.V22.Checks.Evaluated
