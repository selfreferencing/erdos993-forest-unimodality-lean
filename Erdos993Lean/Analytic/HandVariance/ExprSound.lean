import Erdos993Lean.Analytic.HandVariance.Compute.Expr
import Erdos993Lean.Analytic.Reserve.Cert.CellSound
import Erdos993Lean.Analytic.TailCert.ExpLog

/-!
# Soundness of the hand variance formula grammar

Source: the interval evaluation of explicit formulas in TWIN v1.8 Appendix N.4,
Section `hand:var:set`; this proof uses the existing checked arithmetic and
exp/log remainder bounds. It proves formula evaluation, not covering or signs.
-/

namespace Erdos993Lean.Analytic.HandVariance.Compute

open Real Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute

/-- The real meaning of the explicit Appendix N.4 formula grammar. -/
noncomputable def Expr.evalR (env : Nat → ℝ) : Expr → ℝ
  | .rat q => q
  | .var i => env i
  | .add a b => a.evalR env + b.evalR env
  | .sub a b => a.evalR env - b.evalR env
  | .neg a => -a.evalR env
  | .mul a b => a.evalR env * b.evalR env
  | .div a b => a.evalR env / b.evalR env
  | .minimum a b => min (a.evalR env) (b.evalR env)
  | .maximum a b => max (a.evalR env) (b.evalR env)
  | .sq a => a.evalR env ^ 2
  | .exp a => Real.exp (a.evalR env)
  | .log a => Real.log (a.evalR env)

/-- Source: Section `hand:var:set`. Every safely evaluated formula encloses
its real value whenever every retained variable is enclosed. -/
theorem Expr.evalI_mem (e : Expr) {env : Nat → Ival} {realEnv : Nat → ℝ}
    (henv : ∀ i, (env i).Mem (realEnv i)) (hsafe : e.safe env = true) :
    (e.evalI env).Mem (e.evalR realEnv) := by
  induction e with
  | rat q => exact mem_ofRat q
  | var i => exact henv i
  | add a b ia ib =>
    simp only [Expr.safe, Bool.and_eq_true] at hsafe
    exact mem_add (ia hsafe.1) (ib hsafe.2)
  | sub a b ia ib =>
    simp only [Expr.safe, Bool.and_eq_true] at hsafe
    exact mem_sub (ia hsafe.1) (ib hsafe.2)
  | neg a ia => exact mem_neg (ia hsafe)
  | mul a b ia ib =>
    simp only [Expr.safe, Bool.and_eq_true] at hsafe
    exact mem_mul (ia hsafe.1) (ib hsafe.2)
  | div a b ia ib =>
    simp only [Expr.safe, Bool.and_eq_true, decide_eq_true_eq] at hsafe
    exact mem_div (ia hsafe.1.1) (ib hsafe.1.2) hsafe.2
  | minimum a b ia ib =>
    simp only [Expr.safe, Bool.and_eq_true] at hsafe
    have ha := ia hsafe.1
    have hb := ib hsafe.2
    exact ⟨by simpa [Expr.evalI, Expr.evalR, toR_min] using min_le_min ha.1 hb.1,
      by simpa [Expr.evalI, Expr.evalR, toR_min] using min_le_min ha.2 hb.2⟩
  | maximum a b ia ib =>
    simp only [Expr.safe, Bool.and_eq_true] at hsafe
    have ha := ia hsafe.1
    have hb := ib hsafe.2
    exact ⟨by simpa [Expr.evalI, Expr.evalR, toR_max] using max_le_max ha.1 hb.1,
      by simpa [Expr.evalI, Expr.evalR, toR_max] using max_le_max ha.2 hb.2⟩
  | sq a ia =>
    exact Reserve.Cert.mem_sqI (ia hsafe)
  | exp a ia => exact mem_expI (ia hsafe)
  | log a ia =>
    simp only [Expr.safe, Bool.and_eq_true, decide_eq_true_eq] at hsafe
    exact mem_logI (ia hsafe.1) hsafe.2

end Erdos993Lean.Analytic.HandVariance.Compute
