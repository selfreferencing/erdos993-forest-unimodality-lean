import Erdos993Lean.Analytic.V22.Compute.RayExprs

/-! Conservative quadratic envelopes cover sign-transition subcells without
assuming a strict sign through an irrational zero. Original block parameters
and the exact source supremum remain unchanged. -/
namespace Erdos993Lean.Analytic.V22.Compute.RayEnvelope
open Expr RayExprs

structure EnvelopeMethods where
  base : FiniteMethods
  firstUniversal : Bool
  secondUniversal : Bool
  deriving Repr

def quadraticEnvelope (a b nm : Expr) : Expr :=
  add (mul a nm) (mul (positivePart (neg b)) (sq nm))

def selected (universal isPositive : Bool) (a b nm : Expr) : Expr :=
  if universal then quadraticEnvelope a b nm else quadraticSup isPositive a b nm

def selectedGuard (universal isPositive : Bool) (env : Nat → TailCert.Compute.Ival) (b : Expr) : Bool :=
  if universal then true else signGuard isPositive env b

def remainder (br : RootBrackets) (m : EnvelopeMethods) (t : Expr) (M1 M2 rm : Rat) : Expr :=
  let N := blockN M1
  let nm := phiBlockNuMax M2 rm
  let Gh := phiBlockGhat br t M1 M2
  let g1 := phiBlockG1Bound br m.base t M1 M2 rm
  add
    (positivePart (selected m.firstUniversal m.base.quadratic.firstPositive
      (blockFirstA Gh N nm (rat rm)) (blockFirstB Gh N nm (rat rm)) nm))
    (mul g1 (positivePart (selected m.secondUniversal m.base.quadratic.secondPositive
      (blockSecondA N nm (rat rm)) (blockSecondB N nm (rat rm)) nm)))

def phiUpper (br : RootBrackets) (m : EnvelopeMethods) (t M : Expr) (M1 M2 rm : Rat) : Expr :=
  phiWithRemainder br.base t M (remainder br m t M1 M2 rm)

def guard (br : RootBrackets) (m : EnvelopeMethods) (env : Nat → TailCert.Compute.Ival)
    (t : Expr) (M1 M2 rm : Rat) : Bool :=
  let N := blockN M1
  let nm := phiBlockNuMax M2 rm
  let Gh := phiBlockGhat br t M1 M2
  signGuard m.base.q2positive env (phiBlockQ2 M1 M2 rm) &&
  (rhoStarBlock N nm (rat rm)).positiveOK env &&
  selectedGuard m.firstUniversal m.base.quadratic.firstPositive env (blockFirstB Gh N nm (rat rm)) &&
  selectedGuard m.secondUniversal m.base.quadratic.secondPositive env (blockSecondB N nm (rat rm))

def finitePass (br : RootBrackets) (m : EnvelopeMethods) (env : Nat → TailCert.Compute.Ival)
    (t M : Expr) (M1 M2 rm bound : Rat) : Bool :=
  guard br m env t M1 M2 rm && (phiUpper br m t M M1 M2 rm).upperOK env bound

end Erdos993Lean.Analytic.V22.Compute.RayEnvelope
