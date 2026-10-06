import Erdos993Lean.Analytic.Reserve.Cert.Compute.Cell

/-!
# Version 2.2 finite-check expression grammar

This module imports only the existing computational interval core. It extends
the hand-variance grammar locally; it does not change that grammar or any
source formula. A root node carries an exact rational bracket, whose endpoint
signs must pass outward interval checks before its enclosure is usable.
-/

namespace Erdos993Lean.Analytic.V22.Compute

open Erdos993Lean.Analytic.TailCert.Compute

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
  | powNat : Expr → Nat → Expr
  | exp : Expr → Expr
  | log : Expr → Expr
  | sqrt : Expr → Expr
  | rpow : Expr → Rat → Expr
  | root : Rat → Rat → Expr → Expr
  deriving Repr

/-- Natural powers use the already proved four-corner multiplication. -/
def powNatI (A : Ival) : Nat → Ival
  | 0 => ofRat 1
  | n + 1 => mul (powNatI A n) A

/-- The outward enclosure of the exact bracket `[a,b]`. -/
def bracketI (a b : Rat) : Ival := ⟨(ofRat a).lo, (ofRat b).hi⟩

/-- The positive logarithm argument in the endpoint root equation. -/
def rootShiftI (a : Rat) : Ival := add (ofRat 1) (ofRat a)

/-- Enclosure of `a + log(1+a)` at an exact rational endpoint. -/
def rootEndpointI (a : Rat) : Ival := add (ofRat a) (logI (rootShiftI a))

/-- Every root bracket guard is checked, including both log domains and
the directions of the two outward endpoint sign tests. -/
def rootBracketOK (a b : Rat) (L : Ival) : Bool :=
  decide (-1 < a) && decide (a ≤ b) &&
  decide (0 < (rootShiftI a).lo) && decide (0 < (rootShiftI b).lo) &&
  decide ((rootEndpointI a).hi ≤ L.lo) &&
  decide (L.hi ≤ (rootEndpointI b).lo)

/-- Outward interval evaluation. No unguarded value supplies a theorem. -/
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
  | .powNat a n => powNatI (a.evalI env) n
  | .exp a => expI (a.evalI env)
  | .log a => logI (a.evalI env)
  | .sqrt a => sqrtI (a.evalI env)
  | .rpow a q => expI (TailCert.Compute.mul (ofRat q) (logI (a.evalI env)))
  | .root lo hi _ => bracketI lo hi

/-- Domains are retained: positive divisors/log and rational-power bases,
nonnegative square-root inputs, and certified root signs. -/
def Expr.safe (env : Nat → Ival) : Expr → Bool
  | .rat _ | .var _ => true
  | .add a b | .sub a b | .mul a b | .minimum a b | .maximum a b =>
      a.safe env && b.safe env
  | .neg a | .sq a | .powNat a _ | .exp a => a.safe env
  | .div a b => a.safe env && b.safe env && decide (0 < (b.evalI env).lo)
  | .log a | .rpow a _ => a.safe env && decide (0 < (a.evalI env).lo)
  | .sqrt a => a.safe env && decide (0 ≤ (a.evalI env).lo)
  | .root lo hi a => a.safe env && rootBracketOK lo hi (a.evalI env)

/-- Strict positivity of the lower endpoint, after every domain guard. -/
def Expr.positiveOK (env : Nat → Ival) (e : Expr) : Bool :=
  e.safe env && decide (0 < (e.evalI env).lo)

/-- Nonnegativity of the lower endpoint, after every domain guard. -/
def Expr.nonnegativeOK (env : Nat → Ival) (e : Expr) : Bool :=
  e.safe env && decide (0 ≤ (e.evalI env).lo)

/-- A rational upper bound uses the downward-rounded rational endpoint. -/
def Expr.upperOK (env : Nat → Ival) (e : Expr) (q : Rat) : Bool :=
  e.safe env && decide ((e.evalI env).hi ≤ (ofRat q).lo)

/-- A strict rational upper bound uses the same conservative endpoint. -/
def Expr.strictUpperOK (env : Nat → Ival) (e : Expr) (q : Rat) : Bool :=
  e.safe env && decide ((e.evalI env).hi < (ofRat q).lo)

end Erdos993Lean.Analytic.V22.Compute
