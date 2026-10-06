import Erdos993Lean.Analytic.V22.Compute.Grid
import Erdos993Lean.Analytic.V22.RationalData
import Erdos993Lean.Analytic.V21.Pieces

/-!
# Exact ASTs for all fifty-five reconstructed row margins

No activity, theta, D, or rate table is duplicated. Every row reads the
existing pieceV21 and the exact V22 data. Variable 0 is pi; every other
variable is zero. Branches are selected by retained interval sign guards.
-/

namespace Erdos993Lean.Analytic.V22.Compute.Rows

open Expr
open Erdos993Lean.Analytic.TailCert.Compute

def pieceQ (p : Nat) := Erdos993Lean.Analytic.V21.pieceV21 p
def meanQ (p : Nat) : Rat := mu0Data.getD p 0
def classQ (p : Nat) : Option V22Class := classes.find? (fun c => decide (p ∈ c.iotas))
def wingQ (p : Nat) : Option V22WingClass := wingClasses.find? (fun c => decide (p ∈ c.iotas))
def excessQ (p : Nat) : Rat := match classQ p with | some c => c.b | none => 0
def cutoffQ (p : Nat) : Rat := match classQ p with
  | some c => c.tau
  | none => match wingQ p with | some c => c.tau | none => 3 / 5

def qaQ (p : Nat) : Rat := (pieceQ p).lamLo / (1 + (pieceQ p).lamLo)
def qbQ (p : Nat) : Rat := (pieceQ p).lamHi / (1 + (pieceQ p).lamHi)
def ellQ (p : Nat) : Rat := ((pieceQ p).tilts.getD 0 (0, 0)).2
def vminQ (p : Nat) : Rat := min (qaQ p * (1 - qaQ p)) (qbQ p * (1 - qbQ p))
def absQ (x : Rat) : Rat := max x (-x)
def rhiQ (p : Nat) : Rat := max (absQ (2 * qaQ p - 1)) (absQ (2 * qbQ p - 1))

/-- Rational endpoints from Real.pi_gt_d20 and Real.pi_lt_d20. -/
def piSpan : Span :=
  (314159265358979323846 / 100000000000000000000,
   314159265358979323847 / 100000000000000000000)

def env : Nat → Ival := spanEnv piSpan

def gaussianE : Expr := div (exp (rat (-1 / 2))) (sqrt (mul (rat 2) (var 0)))
def meanE (p : Nat) : Expr := rat (meanQ p)
def excessE (p : Nat) : Expr := rat (excessQ p)
def ellE (p : Nat) : Expr := rat (ellQ p)
def vminE (p : Nat) : Expr := rat (vminQ p)
def rhiE (p : Nat) : Expr := rat (rhiQ p)
def lbE (p : Nat) : Expr := neg (log (sub (rat 1) (rat (qbQ p))))
def psiE (t : Expr) : Expr := sub t (mul (rat (9 / 2)) (sq (sub t (rat 1))))
def AE (p M : Nat) : Expr :=
  div (rat (smallK.getD M 0)) (mul (mul (rat 4) gaussianE) (sqrt (vminE p)))

def smallAmplitudeE (p M : Nat) : Expr := mul (AE p M) (rpow (meanE p) (3 / 2))
def smallBaseE (p M : Nat) : Expr :=
  add (add (smallAmplitudeE p M) (psiE (div (rat M) (meanE p)))) (excessE p)

def smallPositive (p M : Nat) : Bool := (smallBaseE p M).positiveOK env
def smallNonpositive (p M : Nat) : Bool := (smallBaseE p M).upperOK env 0

/-- A branch is consumed only if its exact sign is certified. -/
def smallPriceE (p M : Nat) : Expr :=
  mul (mul (if smallPositive p M then smallBaseE p M else smallAmplitudeE p M)
    (rpow (sub (rat 1) (rat (qbQ p))) (-(M : Rat))))
    (exp (neg (mul (ellE p) (meanE p))))

def smallPositiveSideE (p M : Nat) : Expr :=
  sub (mul (ellE p) (smallBaseE p M))
    (mul (mul (rat (3 / 2)) (AE p M)) (sqrt (meanE p)))

def smallNonpositiveSideE (p : Nat) : Expr := sub (mul (ellE p) (meanE p)) (rat (3 / 2))

def smallGuard (p M : Nat) : Bool :=
  if smallPositive p M then (smallPositiveSideE p M).nonnegativeOK env
  else smallNonpositive p M && (smallNonpositiveSideE p).nonnegativeOK env

def maxE (xs : List Expr) : Expr := xs.foldl maximum (rat 0)
def zaE (p : Nat) : Expr := maxE ((List.range 8).map (smallPriceE p))

/-- Exact class membership and wing cutoff select the source's actual cells. -/
def usesCell (p : Nat) (cell : V22SpikeCell) : Bool := match classQ p with
  | some c => decide (cell.classId = c.classId)
  | none => decide (cell.classId = 0 ∧ cell.hi ≤ cutoffQ p)

def multiplierQ (i : Nat) : Rat := ([1, 2, 4, 8, 16] : List Nat).getD i 0
def blockMlowE (p : Nat) (cell : V22SpikeCell) (i : Nat) : Expr :=
  maximum (maximum (mul (rat (multiplierQ i)) (rat cell.ma)) (rat 8))
    (mul (rat cell.lo) (meanE p))

def blockExponentE (p : Nat) (cell : V22SpikeCell) (i : Nat) : Expr :=
  maximum (mul (sub (div (ellE p) (rat cell.hi)) (lbE p)) (blockMlowE p cell i))
    (mul (sub (ellE p) (mul (rat cell.hi) (lbE p))) (meanE p))

/-- Every block uses its fixed six-digit upward export. -/
def blockPriceE (p : Nat) (cell : V22SpikeCell) (i : Nat) : Expr :=
  mul (add (rat (cell.logBounds.getD i 0)) (excessE p))
    (exp (neg (blockExponentE p cell i)))

def zbE (p : Nat) : Expr := maxE (spikeCells.flatMap fun cell =>
  if usesCell p cell then (List.range 5).map (blockPriceE p cell) else [])

def mcE (p : Nat) : Expr := maximum (meanE p) (rat (400 / 11))
def smallRateE (p : Nat) : Expr := sub (ellE p) (mul (rat (11 / 50)) (lbE p))
def zcE (p : Nat) : Expr :=
  mul (add (div (rpow (mcE p) (3 / 2))
    (mul (mul (rat 16) (sqrt (vminE p))) gaussianE)) (excessE p))
    (exp (neg (mul (smallRateE p) (mcE p))))

/-- The actual rowMargin formula, including the same three-price maximum. -/
def marginE (p : Nat) : Expr :=
  sub (sub (sub (sub (add (rat 1) (excessE p)) (rat (pieceQ p).theta))
    (div (mul (rat 9) (rat (pieceQ p).D)) (mul (rat 2) (meanE p))))
    (div (sq (rhiE p)) (mul (sub (rat 1) (sq (rhiE p))) (meanE p))))
    (maximum (zaE p) (maximum (zbE p) (zcE p)))

def decayE (p : Nat) (cell : V22SpikeCell) : Expr := sub (div (ellE p) (rat cell.hi)) (lbE p)
def verySmallSideE (p : Nat) : Expr := sub (mul (smallRateE p) (mcE p)) (rat (3 / 2))

/-- Every side condition of the exact statement is retained. -/
def rowGuard (p : Nat) : Bool :=
  decide (19 ≤ meanQ p ∧ 0 ≤ excessQ p ∧ excessQ p ≤ 1) &&
  decide (0 < ellQ p ∧ 0 < vminQ p) &&
  (List.range 8).all (smallGuard p) &&
  (verySmallSideE p).nonnegativeOK env &&
  spikeCells.all (fun cell => !usesCell p cell || (decayE p cell).positiveOK env)

def rowPass (p : Nat) : Bool := rowGuard p && (marginE p).positiveOK env
def check : Bool := (List.range 55).all rowPass

end Erdos993Lean.Analytic.V22.Compute.Rows
