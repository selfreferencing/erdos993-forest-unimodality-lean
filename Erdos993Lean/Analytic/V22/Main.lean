import Erdos993Lean.Analytic.V22.Ceiling
import Erdos993Lean.Fiber.Floor

/-! Paper v2.2 Theorems 3.1 and 1.1, conditional only on E's exact
above-start fiber interface. The floor reuses all 249 kernel certificates.
No instance of the remaining analytic premise is supplied by lane F. -/
namespace Erdos993Lean.Analytic.V22

open Erdos993Lean

/-- Theorem 3.1, at every actual forest window rank, conditional on E. -/
theorem noWeakValley_window_25 (fiberAbove : ParameterNoValley)
    (F : FiniteForest) (hn : 25 ≤ F.n) (k : ℕ)
    (hk1 : (F.n + 3) / 4 < k) (hk2 : k < hB F) :
    ¬ (independenceCount F k ≤ independenceCount F (k - 1) ∧
       independenceCount F k ≤ independenceCount F (k + 1)) :=
  noWeakValley_of_parameterNoValley (parameterNoValley fiberAbove) F hn k hk1 hk2

/-- Theorem 3.1: the ceiling at 25, conditional only on the E interface. -/
theorem ceilingStatement_25 (fiberAbove : ParameterNoValley) : CeilingStatement 25 :=
  ceilingStatement_25_of_parameterNoValley (parameterNoValley fiberAbove)

/-- Theorem 1.1, conditional only on the named above-start fiber theorem. -/
theorem erdos993_v22 (fiberAbove : ParameterNoValley) : Erdos993Statement :=
  erdos993_of_floor_of_ceiling Fiber.floorStatement_25_fiber (ceilingStatement_25 fiberAbove)

end Erdos993Lean.Analytic.V22
