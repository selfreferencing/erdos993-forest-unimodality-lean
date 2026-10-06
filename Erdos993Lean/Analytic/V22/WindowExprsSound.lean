import Erdos993Lean.Analytic.V22.Compute.WindowExprs
import Erdos993Lean.Analytic.V22.EarlyCoefficientsSound

/-! Exact semantic identities for the actual-activity window builders.
The margin identities encode c1/c2 with strict positivity and c3/c3′ with
nonnegativity; they do not assert that any cell passes these conditions. -/

namespace Erdos993Lean.Analytic.V22.Compute.WindowExprs

variable (env : Nat → ℝ) (r N W t : Expr)

@[simp] theorem evalR_varianceR :
    (varianceR r).evalR env = V22.varianceR (r.evalR env) := by
  simp [varianceR, Expr.evalR, V22.varianceR]

@[simp] theorem evalR_Delta : (Delta r N).evalR env = V22.Delta (r.evalR env) (N.evalR env) := by
  simp [Delta, Expr.evalR, V22.Delta]

@[simp] theorem evalR_gamma : (gamma r N).evalR env = V22.gamma (r.evalR env) (N.evalR env) := by
  simp [gamma, Expr.evalR, V22.gamma]

@[simp] theorem evalR_artanh : (artanh r).evalR env = V22.artanh (r.evalR env) := by
  simp [artanh, Expr.evalR, V22.artanh]

@[simp] theorem evalR_aHat : (aHat r).evalR env = V22.aHat (r.evalR env) := by
  simp [aHat, Expr.evalR, V22.aHat]

@[simp] theorem evalR_sN : (sN r N).evalR env = V22.sN (r.evalR env) (N.evalR env) := by
  simp [sN, Expr.evalR, V22.sN]

@[simp] theorem evalR_epsilon :
    (epsilon r N).evalR env = V22.epsilon (r.evalR env) (N.evalR env) := by
  simp [epsilon, Expr.evalR, V22.epsilon]

@[simp] theorem evalR_c0 : (c0 r N).evalR env = V22.c0 (r.evalR env) (N.evalR env) := by
  simp [c0, Expr.evalR, V22.c0]

@[simp] theorem evalR_ZL :
    (ZL r N W).evalR env = V22.ZL (r.evalR env) (N.evalR env) (W.evalR env) := by
  simp [ZL, Expr.evalR, V22.ZL]

@[simp] theorem evalR_ZR :
    (ZR r N W).evalR env = V22.ZR (r.evalR env) (N.evalR env) (W.evalR env) := by
  simp [ZR, Expr.evalR, V22.ZR]

@[simp] theorem evalR_quarticError :
    (quarticError r N W).evalR env = V22.quarticError (r.evalR env) (N.evalR env) (W.evalR env) := by
  simp [quarticError, Expr.evalR, V22.quarticError]

@[simp] theorem evalR_cr : (cr r).evalR env = V22.cr (r.evalR env) := by
  simp [cr, Expr.evalR, V22.cr]

@[simp] theorem evalR_windowEL :
    (windowEL r N).evalR env = V22.windowEL (r.evalR env) (N.evalR env) := by
  simp [windowEL, Expr.evalR, V22.windowEL]

@[simp] theorem evalR_windowRhoL :
    (windowRhoL r N).evalR env = V22.windowRhoL (r.evalR env) (N.evalR env) := by
  simp [windowRhoL, Expr.evalR, V22.windowRhoL]

@[simp] theorem evalR_windowRhoLbar :
    (windowRhoLbar r N).evalR env = V22.windowRhoLbar (r.evalR env) (N.evalR env) := by
  simp [windowRhoLbar, Expr.evalR, V22.windowRhoLbar]

@[simp] theorem evalR_lambdaT : (lambdaT t).evalR env = V22.lambdaT (t.evalR env) := by
  norm_num [lambdaT, Expr.evalR, V22.lambdaT]

@[simp] theorem evalR_windowSbar (lo hi : Rat) :
    (windowSbar t r N lo hi).evalR env = V22.windowSbar (t.evalR env) (r.evalR env) (N.evalR env) := by
  simp [windowSbar, Expr.evalR, V22.windowSbar]

@[simp] theorem evalR_windowCondition1 :
    (windowCondition1 r N).evalR env = 1 - V22.ZL (r.evalR env) (N.evalR env) 3 := by
  simp [windowCondition1, Expr.evalR]

@[simp] theorem evalR_windowCondition2 :
    (windowCondition2 r N).evalR env = 1 - (r.evalR env + V22.ZR (r.evalR env) (N.evalR env) 3) := by
  simp [windowCondition2, Expr.evalR]

@[simp] theorem evalR_windowCondition3 :
    (windowCondition3 r N).evalR env =
      12 * (1 - (r.evalR env + V22.ZR (r.evalR env) (N.evalR env) 3)^2) /
        ((1 - (r.evalR env)^2) * V22.rho (N.evalR env)) - 3 := by
  simp [windowCondition3, Expr.evalR]

@[simp] theorem evalR_c3PrimeMargin :
    (c3PrimeMargin r N).evalR env =
      12 * (1 - (r.evalR env + V22.ZR (r.evalR env) (N.evalR env) 3)^2) /
        (1 - (r.evalR env)^2) - 3 := by
  simp [c3PrimeMargin, Expr.evalR]

@[simp] theorem evalR_uMonoDerivative :
    (uMonoDerivative r N).evalR env = V22.uMonoDerivative (r.evalR env) (N.evalR env) := by
  norm_num [uMonoDerivative, Expr.evalR, V22.uMonoDerivative]

@[simp] theorem evalR_windowH :
    (windowH r N).evalR env = V22.windowH (r.evalR env) (N.evalR env) := by
  simp [windowH, Expr.evalR, V22.windowH]

end Erdos993Lean.Analytic.V22.Compute.WindowExprs
