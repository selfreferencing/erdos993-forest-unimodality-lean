import Erdos993Lean.Analytic.V22.Compute.EarlyCoefficients
import Erdos993Lean.Analytic.V22.CoefficientExprsSound
import Erdos993Lean.Analytic.V22.Checks.EarlyStatements

/-!
The numerical A2 recipe uses upper bounds for `sigma0` and `Ghat`, so its
denominators are deliberately named recipes. These identities preserve those
choices; they do not silently identify a conservative recipe with the actual
root expression. A3/A3′ identities cover only the explicit numerical bounds.
No derivative, endpoint transport or monotonicity conclusion is claimed.
-/

namespace Erdos993Lean.Analytic.V22.Compute.EarlyCoefficients

noncomputable section

variable (env : Nat → ℝ) (s N0 M0 rm nm Nlo Nhi Ma : Expr)

@[simp] theorem evalR_positivePart :
    (positivePart s).evalR env = V22.positivePart (s.evalR env) := by
  simp [positivePart, Expr.evalR, V22.positivePart]

@[simp] theorem evalR_tOfS : (tOfS s).evalR env = V22.tOfS (s.evalR env) := by
  norm_num [tOfS, Expr.evalR, V22.tOfS]

@[simp] theorem evalR_a2M0 (mean : Rat) :
    (a2M0 mean s).evalR env = (mean : ℝ) * V22.tOfS (s.evalR env) := by
  simp [a2M0, Expr.evalR]

@[simp] theorem evalR_a2N0 : (a2N0 M0).evalR env = M0.evalR env + 2 := by
  simp [a2N0, Expr.evalR]

@[simp] theorem evalR_a2NuMax :
    (a2NuMax N0 rm).evalR env = rm.evalR env * Real.sqrt (N0.evalR env) := by
  simp [a2NuMax, Expr.evalR]

@[simp] theorem evalR_kbar : (kbar M0).evalR env = V22.kbar (M0.evalR env) := by
  norm_num [kbar, Expr.evalR, V22.kbar]

@[simp] theorem evalR_hbar : (hbar M0).evalR env = V22.hbar (M0.evalR env) := by
  simp [hbar, Expr.evalR, V22.hbar]

@[simp] theorem evalR_lambdaOfS :
    (lambdaOfS s).evalR env = s.evalR env + Real.log (1 + s.evalR env) := by
  simp [lambdaOfS, Expr.evalR]

@[simp] theorem evalR_G0 :
    (G0 s).evalR env = (s.evalR env)^2 / (1 + s.evalR env) := by
  simp [G0, Expr.evalR]

@[simp] theorem evalR_G1 : (G1 s).evalR env = s.evalR env / (1 + s.evalR env) := by
  simp [G1, Expr.evalR]

@[simp] theorem evalR_G2 :
    (G2 s).evalR env = 1 / ((1 + s.evalR env) * (2 + s.evalR env)) := by
  simp [G2, Expr.evalR]

@[simp] theorem evalR_phi : (phi s).evalR env = V22.phi (s.evalR env) := by
  norm_num [phi, Expr.evalR, V22.phi]

@[simp] theorem evalR_sigmaBound :
    (sigmaBound s M0).evalR env = V22.positivePart (s.evalR env + V22.hbar (M0.evalR env)) := by
  simp [sigmaBound, Expr.evalR]

@[simp] theorem evalR_ghatBound :
    (ghatBound s M0).evalR env = max
      ((s.evalR env)^2 / (1 + s.evalR env))
      ((V22.positivePart (s.evalR env + Real.log (1 + s.evalR env) + V22.hbar (M0.evalR env)))^2 / 4) := by
  simp [ghatBound, Expr.evalR]

/-- A2's conservative lower denominator, with the retained `sigmaBound`. -/
def betaLRecipeReal (s N0 M0 rm nm : ℝ) : ℝ :=
  (N0 - 1) * (1 - V22.ebar N0 rm nm)
    - 2 * V22.positivePart (s + V22.hbar M0) * V22.alpha2 N0 rm
    - (2 * (V22.alpha1 N0 rm)^2 + 4 * V22.alpha1 N0 rm * V22.alpha2 N0 rm * nm
      + 2 * (V22.alpha2 N0 rm)^2 * nm^2) / (N0 + 1)

@[simp] theorem evalR_betaLRecipe :
    (betaLRecipe s N0 M0 rm nm).evalR env =
      betaLRecipeReal (s.evalR env) (N0.evalR env) (M0.evalR env) (rm.evalR env) (nm.evalR env) := by
  simp [betaLRecipe, Expr.evalR, betaLRecipeReal]

@[simp] theorem evalR_dLRecipe :
    (dLRecipe s N0 M0 rm nm).evalR env =
      (V22.positivePart (s.evalR env + V22.hbar (M0.evalR env)) *
        V22.alpha1 (N0.evalR env) (rm.evalR env))^2 /
      betaLRecipeReal (s.evalR env) (N0.evalR env) (M0.evalR env) (rm.evalR env) (nm.evalR env) := by
  simp [dLRecipe, Expr.evalR]

@[simp] theorem evalR_capN : (capN rm).evalR env = (6 / rm.evalR env)^2 := by
  simp [capN, Expr.evalR]

@[simp] theorem evalR_e2DerivativeBoundOn :
    (e2DerivativeBoundOn rm Nlo Nhi).evalR env =
      V22.e3 (rm.evalR env) * rm.evalR env / (2 * Real.sqrt (Nlo.evalR env))
        + V22.e4 (Nlo.evalR env) (rm.evalR env) * (rm.evalR env)^2
        + (3/2) * V22.e5 (rm.evalR env) * (rm.evalR env)^3 * Real.sqrt (Nhi.evalR env) := by
  norm_num [e2DerivativeBoundOn, Expr.evalR]

@[simp] theorem evalR_e2DerivativeBound :
    (e2DerivativeBound rm Nlo).evalR env = Checks.e2DerivativeBound (rm.evalR env) (Nlo.evalR env) := by
  simp [e2DerivativeBound, Checks.e2DerivativeBound]

@[simp] theorem evalR_betaDerivativeBound :
    (betaDerivativeBound rm Nlo).evalR env = Checks.betaDerivativeBound (rm.evalR env) (Nlo.evalR env) := by
  simp [betaDerivativeBound, Expr.evalR, Checks.betaDerivativeBound]

@[simp] theorem evalR_cappedBeta :
    (cappedBeta rm N0).evalR env = Checks.cappedBeta (rm.evalR env) (N0.evalR env) := by
  simp [cappedBeta, Checks.cappedBeta]

@[simp] theorem evalR_a3LowerBound :
    a3LowerBound.evalR env = Checks.betaDerivativeBound (1/4) (67/5) := by
  norm_num [a3LowerBound, Expr.evalR]

@[simp] theorem evalR_a3Margin :
    a3Margin.evalR env = Checks.betaDerivativeBound (1/4) (67/5) - 744/1000 := by
  norm_num [a3Margin, Expr.evalR]

@[simp] theorem evalR_a3EnvelopeStart (mean : Rat) :
    (a3EnvelopeStart mean).evalR env = (mean : ℝ) * V22.tOfS (-66/125) + 2 := by
  norm_num [a3EnvelopeStart, Expr.evalR]

@[simp] theorem evalR_a3FinalBlockStart :
    (a3FinalBlockStart Ma).evalR env = 16 * Ma.evalR env + 2 := by
  simp [a3FinalBlockStart, Expr.evalR]

@[simp] theorem evalR_a3CappedStartMargin :
    (a3CappedStartMargin rm Nlo).evalR env = Nlo.evalR env - ((6 / rm.evalR env)^2 + 46/5) := by
  norm_num [a3CappedStartMargin, Expr.evalR]

end

end Erdos993Lean.Analytic.V22.Compute.EarlyCoefficients
