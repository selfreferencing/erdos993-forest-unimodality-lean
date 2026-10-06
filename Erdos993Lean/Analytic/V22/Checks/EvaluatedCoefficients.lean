import Erdos993Lean.Analytic.V22.Compute.CoefficientChecks
import Erdos993Lean.Analytic.V22.Compute.A4d
import Erdos993Lean.Analytic.V22.Compute.A4m
import Erdos993Lean.Analytic.V22.Compute.LargeT
import Erdos993Lean.Analytic.V22.Compute.SpikeLowerChecks
import Erdos993Lean.Analytic.V22.Compute.WindowChecks

/-! Compiled checks of coefficient, lower-spike and window-shape recipes.
Every declaration is separately countable; soundness consumers are separate. -/
namespace Erdos993Lean.Analytic.V22.Checks.Evaluated

theorem a3 : Compute.CoefficientChecks.a3OK = true := by native_decide

theorem a3Prime : Compute.CoefficientChecks.a3PrimeOK = true := by native_decide

theorem a4 : Compute.CoefficientChecks.a4OK = true := by native_decide

theorem a4Prime : Compute.CoefficientChecks.a4PrimeOK = true := by native_decide

theorem a4d : Compute.A4d.check = true := by native_decide

theorem a4m : Compute.A4m.check = true := by native_decide

theorem a5 : Compute.LargeT.a5Check = true := by native_decide

theorem d4 : Compute.LargeT.d4Check = true := by native_decide

theorem b2 : Compute.SpikeLowerChecks.b2OK = true := by native_decide

theorem d1 : Compute.WindowChecks.d1AllOK = true := by native_decide

theorem d1Prime : Compute.WindowChecks.d1PrimeAllOK = true := by native_decide

theorem d2 : Compute.WindowChecks.d2AllOK = true := by native_decide

end Erdos993Lean.Analytic.V22.Checks.Evaluated
