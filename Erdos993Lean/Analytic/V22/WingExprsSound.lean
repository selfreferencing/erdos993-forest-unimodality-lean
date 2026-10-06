import Erdos993Lean.Analytic.V22.Compute.WingExprs
import Erdos993Lean.Analytic.V22.EarlyCoefficientsSound
import Erdos993Lean.Analytic.V22.WingQuadraticSound

/-! Exact semantics of the frozen wing expressions. The identities retain
the original cell start and make no numerical certificate claim. -/

namespace Erdos993Lean.Analytic.V22.Compute.WingExprs

variable (env : Nat → ℝ) (c : V22WingClass) (cell : V22Cell) (t n : Expr) (br : RootBrackets)

theorem N0_cast : (N0 c cell : ℝ) = Checks.wingN0 c cell := by
  simp [N0, Checks.wingN0]

@[simp] theorem evalR_baseRoot :
    (baseRoot t br).evalR env = rootMap (lambdaT (t.evalR env)) := by
  norm_num [baseRoot, Expr.evalR, lambdaT]

@[simp] theorem evalR_G0 : (G0 t br).evalR env = V22.G (lambdaT (t.evalR env)) := by
  simp [G0, Expr.evalR, V22.G]

@[simp] theorem evalR_G1 : (G1 t br).evalR env = V22.G1 (lambdaT (t.evalR env)) := by
  simp [G1, Expr.evalR, V22.G1]

@[simp] theorem evalR_G2 : (G2 t br).evalR env = V22.G2 (lambdaT (t.evalR env)) := by
  simp [G2, Expr.evalR, V22.G2]

@[simp] theorem evalR_absolute (x : Expr) : (absolute x).evalR env = |x.evalR env| := by
  change max (x.evalR env) (-x.evalR env) = |x.evalR env|
  rcases le_total (0 : ℝ) (x.evalR env) with h | h
  · rw [abs_of_nonneg h, max_eq_left (by linarith)]
  · rw [abs_of_nonpos h, max_eq_right (by linarith)]

@[simp] theorem evalR_Ghat :
    (Ghat c cell t br).evalR env = V22.Ghat (t.evalR env) (Checks.wingN0 c cell - 2) := by
  norm_num [Ghat, Expr.evalR, V22.Ghat, V22.G, N0_cast, lambdaT]

@[simp] theorem evalR_slack : (slack t br).evalR env = gaussianSlack (t.evalR env) := by
  norm_num [slack, Expr.evalR, gaussianSlack]

@[simp] theorem evalR_nuMax : (nuMax c cell).evalR env = Checks.wingNuMax c cell := by
  simp [nuMax, Checks.wingNuMax, N0_cast, Expr.evalR]

@[simp] theorem evalR_rhoStar :
    (rhoStar c cell).evalR env = V22.rhoStar (Checks.wingN0 c cell) c.rb := by
  simp [rhoStar, Expr.evalR, N0_cast]

@[simp] theorem evalR_betaE :
    (betaE c cell).evalR env = V22.betaE (Checks.wingN0 c cell) c.rb (Checks.wingNuMax c cell) := by
  simp [betaE, Expr.evalR, N0_cast]

@[simp] theorem evalR_kPrime :
    (kPrime c cell t br).evalR env = Checks.wingKPrime c cell (t.evalR env) := by
  simp [kPrime, Expr.evalR, Checks.wingKPrime, N0_cast]

@[simp] theorem evalR_bPrime :
    (bPrime c cell t br).evalR env = Checks.wingBPrime c cell (t.evalR env) := by
  simp [bPrime, Expr.evalR, Checks.wingBPrime, N0_cast]

@[simp] theorem evalR_C : (C c cell t n br).evalR env = Checks.wingC c cell (t.evalR env) (n.evalR env) := by
  simp [C, Expr.evalR, Checks.wingC]

@[simp] theorem evalR_De : (De c cell).evalR env = Checks.wingDe c cell := by
  simp [De, Expr.evalR, Checks.wingDe]

@[simp] theorem evalR_tau1 : (tau1 c cell t br).evalR env = Checks.wingTau1 c cell (t.evalR env) := by
  norm_num [tau1, Expr.evalR, Checks.wingTau1, N0_cast]

@[simp] theorem evalR_A : (A c).evalR env = WingQuadratic.wingA c := by
  simp [A, Expr.evalR, WingQuadratic.wingA]

@[simp] theorem evalR_B : (B c cell t br).evalR env = WingQuadratic.wingB c cell (t.evalR env) := by
  simp [B, Expr.evalR, WingQuadratic.wingB]

@[simp] theorem evalR_sqrtSlope :
    (sqrtSlope c cell t br).evalR env = WingQuadratic.wingSlope c cell (t.evalR env) := by
  simp [sqrtSlope, Expr.evalR, WingQuadratic.wingSlope]

@[simp] theorem evalR_D : (D c cell t br).evalR env = WingQuadratic.wingD c cell (t.evalR env) := by
  simp [D, Expr.evalR, WingQuadratic.wingD]

@[simp] theorem evalR_startingSlope :
    (startingSlope c cell t br).evalR env = WingQuadratic.startingSlope
      (WingQuadratic.wingA c) (WingQuadratic.wingB c cell (t.evalR env))
      (WingQuadratic.wingSlope c cell (t.evalR env)) (Checks.wingN0 c cell) := by
  simp [startingSlope, Expr.evalR, WingQuadratic.startingSlope, N0_cast]

@[simp] theorem evalR_startingValue :
    (startingValue c cell t br).evalR env = WingQuadratic.quadratic
      (WingQuadratic.wingA c) (WingQuadratic.wingB c cell (t.evalR env))
      (WingQuadratic.wingSlope c cell (t.evalR env)) (WingQuadratic.wingD c cell (t.evalR env))
      (Checks.wingN0 c cell) := by
  simp [startingValue, Expr.evalR, WingQuadratic.quadratic, N0_cast]

@[simp] theorem evalR_tangentBound (N1 : Rat) :
    (tangentBound c cell t br N1).evalR env = WingQuadratic.tangentBound
      (WingQuadratic.wingA c) (WingQuadratic.wingB c cell (t.evalR env))
      (WingQuadratic.wingSlope c cell (t.evalR env)) (WingQuadratic.wingD c cell (t.evalR env)) N1 := by
  simp [tangentBound, Expr.evalR, WingQuadratic.tangentBound]

end Erdos993Lean.Analytic.V22.Compute.WingExprs
