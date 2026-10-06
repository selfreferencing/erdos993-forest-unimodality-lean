import Erdos993Lean.Analytic.Reserve.Cert.Compute.Cell

/-!
# Formula grammar for the hand variance finite checks

Source: TWIN v1.8 Appendix N.4, `tgt:lem:dY`, `tgt:lem:dmu`,
and the exact interval formulas of `certfree/two_gen_transport/scripts/verify_final.py`
and `certfree/multiplier_curve/scripts/curve_all.py`.
This module contains only computable syntax and interval evaluation.
All division and logarithm guards are retained and checked.
-/

namespace Erdos993Lean.Analytic.HandVariance.Compute

open Erdos993Lean.Analytic.TailCert.Compute

/-- Arithmetic syntax of the explicit finite-check formulas in Appendix N.4. -/
inductive Expr where
  | rat : Rat → Expr
  | var : Nat → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | neg : Expr → Expr
  | mul : Expr → Expr → Expr
  | div : Expr → Expr → Expr
  | minimum : Expr → Expr → Expr
  | maximum : Expr → Expr → Expr
  | sq : Expr → Expr
  | exp : Expr → Expr
  | log : Expr → Expr
  deriving Repr

/-- Outward interval evaluation, reusing the package's proved arithmetic. -/
def Expr.evalI (env : Nat → Ival) : Expr → Ival
  | .rat q => ofRat q
  | .var i => env i
  | .add a b => TailCert.Compute.add (a.evalI env) (b.evalI env)
  | .sub a b => TailCert.Compute.sub (a.evalI env) (b.evalI env)
  | .neg a => TailCert.Compute.neg (a.evalI env)
  | .mul a b => TailCert.Compute.mul (a.evalI env) (b.evalI env)
  | .div a b => TailCert.Compute.div (a.evalI env) (b.evalI env)
  | .minimum a b => ⟨min (a.evalI env).lo (b.evalI env).lo,
      min (a.evalI env).hi (b.evalI env).hi⟩
  | .maximum a b => ⟨max (a.evalI env).lo (b.evalI env).lo,
      max (a.evalI env).hi (b.evalI env).hi⟩
  | .sq a => Reserve.Cert.Compute.sqI (a.evalI env)
  | .exp a => expI (a.evalI env)
  | .log a => logI (a.evalI env)

/-- The guards required by the exact interval semantics: divisors and log
arguments have positive lower endpoints. A failed guard never yields a proof. -/
def Expr.safe (env : Nat → Ival) : Expr → Bool
  | .rat _ | .var _ => true
  | .add a b | .sub a b | .mul a b | .minimum a b | .maximum a b => a.safe env && b.safe env
  | .neg a | .sq a | .exp a => a.safe env
  | .div a b => a.safe env && b.safe env && decide (0 < (b.evalI env).lo)
  | .log a => a.safe env && decide (0 < (a.evalI env).lo)

end Erdos993Lean.Analytic.HandVariance.Compute
