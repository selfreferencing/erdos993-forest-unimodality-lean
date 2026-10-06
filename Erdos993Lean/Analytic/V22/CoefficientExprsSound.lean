import Erdos993Lean.Analytic.V22.Compute.CoefficientExprs
import Erdos993Lean.Analytic.V22.ExprSound

/-! Exact real meanings of the coefficient AST builders. No interval pass
or coefficient inequality is assumed or asserted in these identities. -/

namespace Erdos993Lean.Analytic.V22.Compute.CoefficientExprs

variable (env : Nat → ℝ) (N rm nm nu : Expr)

@[simp] theorem evalR_cCoef : (cCoef N).evalR env = V22.cCoef (N.evalR env) := by
  simp [cCoef, Expr.evalR, V22.cCoef]

@[simp] theorem evalR_rho : (rho N).evalR env = V22.rho (N.evalR env) := by
  simp [rho, Expr.evalR, V22.rho]

@[simp] theorem evalR_Z0 : (Z0 N).evalR env = V22.Z0 (N.evalR env) := by
  simp [Z0, Expr.evalR, V22.Z0]

@[simp] theorem evalR_phiM : (phiM N rm).evalR env = V22.phiM (N.evalR env) (rm.evalR env) := by
  simp [phiM, Expr.evalR, V22.phiM]

@[simp] theorem evalR_KL : (KL N rm).evalR env = V22.KL (N.evalR env) (rm.evalR env) := by
  simp [KL, Expr.evalR, V22.KL]

@[simp] theorem evalR_KR : (KR N rm).evalR env = V22.KR (N.evalR env) (rm.evalR env) := by
  simp [KR, Expr.evalR, V22.KR]

@[simp] theorem evalR_cL1 : (cL1 N rm).evalR env = V22.cL1 (N.evalR env) (rm.evalR env) := by
  simp [cL1, Expr.evalR, V22.cL1]

@[simp] theorem evalR_cL2 : (cL2 N rm).evalR env = V22.cL2 (N.evalR env) (rm.evalR env) := by
  simp [cL2, Expr.evalR, V22.cL2]

@[simp] theorem evalR_cR1 : (cR1 N rm).evalR env = V22.cR1 (N.evalR env) (rm.evalR env) := by
  simp [cR1, Expr.evalR, V22.cR1]

@[simp] theorem evalR_cR2 : (cR2 N rm).evalR env = V22.cR2 (N.evalR env) (rm.evalR env) := by
  simp [cR2, Expr.evalR, V22.cR2]

@[simp] theorem evalR_alpha1 :
    (alpha1 N rm).evalR env = V22.alpha1 (N.evalR env) (rm.evalR env) := by
  simp [alpha1, Expr.evalR, V22.alpha1]

@[simp] theorem evalR_alpha2 :
    (alpha2 N rm).evalR env = V22.alpha2 (N.evalR env) (rm.evalR env) := by
  simp [alpha2, Expr.evalR, V22.alpha2]

@[simp] theorem evalR_rhoStar :
    (rhoStar N rm).evalR env = V22.rhoStar (N.evalR env) (rm.evalR env) := by
  simp [rhoStar, Expr.evalR, V22.rhoStar]

@[simp] theorem evalR_kappaA :
    (kappaA N rm).evalR env = V22.kappaA (N.evalR env) (rm.evalR env) := by
  simp [kappaA, Expr.evalR, V22.kappaA]

@[simp] theorem evalR_e2 : e2.evalR env = V22.e2 := by
  norm_num [e2, Expr.evalR, V22.e2]

@[simp] theorem evalR_e3 : (e3 rm).evalR env = V22.e3 (rm.evalR env) := by
  simp [e3, Expr.evalR, V22.e3]

@[simp] theorem evalR_e4 : (e4 N rm).evalR env = V22.e4 (N.evalR env) (rm.evalR env) := by
  simp [e4, Expr.evalR, V22.e4]

@[simp] theorem evalR_e5 : (e5 rm).evalR env = V22.e5 (rm.evalR env) := by
  simp [e5, Expr.evalR, V22.e5]

@[simp] theorem evalR_E2 :
    (E2 N rm nm).evalR env = V22.E2 (N.evalR env) (rm.evalR env) (nm.evalR env) := by
  simp [E2, Expr.evalR, V22.E2]

@[simp] theorem evalR_cappedNu :
    (cappedNu N rm).evalR env = min 6 (rm.evalR env * Real.sqrt (N.evalR env)) := by
  simp [cappedNu, Expr.evalR]

@[simp] theorem evalR_ebar :
    (ebar N rm nm).evalR env = V22.ebar (N.evalR env) (rm.evalR env) (nm.evalR env) := by
  simp [ebar, Expr.evalR, V22.ebar]

@[simp] theorem evalR_betaE :
    (betaE N rm nm).evalR env = V22.betaE (N.evalR env) (rm.evalR env) (nm.evalR env) := by
  simp [betaE, Expr.evalR, V22.betaE]

@[simp] theorem evalR_lambdaBonusF :
    (lambdaBonusF N rm).evalR env = V22.lambdaBonusF (N.evalR env) (rm.evalR env) := by
  norm_num [lambdaBonusF, Expr.evalR, V22.lambdaBonusF]

@[simp] theorem evalR_Xbar :
    (Xbar nu N rm).evalR env = V22.Xbar (nu.evalR env) (N.evalR env) (rm.evalR env) := by
  simp [Xbar, Expr.evalR, V22.Xbar]

end Erdos993Lean.Analytic.V22.Compute.CoefficientExprs
