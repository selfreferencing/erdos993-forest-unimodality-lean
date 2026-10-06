import Erdos993Lean.Analytic.V22.Compute.CoefficientExprs

/-!
# Finite and infinite block ray expressions

These ASTs retain the exact `Functions.lean` block choices. The four root
brackets certify the base, lower shift, upper shift, and optional shifted
derivative arguments. Three explicit Boolean method choices retain the
`q₂` branch and both quadratic-supremum branches. A method may be consumed
only with its exact interval sign guard. The finite `q₂` is built entirely
from rational block parameters, independently of the variable `t`.

The recipes return bounds on `phiBlock` or `phiInfiniteBlock`. Transport to
the actual fiber deficit, including the window infimum, is separate.
-/

namespace Erdos993Lean.Analytic.V22.Compute.RayExprs

open Expr
open Erdos993Lean.Analytic.TailCert.Compute

abbrev RootBracket := Rat × Rat

structure RootBrackets where
  base : RootBracket
  shiftLow : RootBracket
  shiftHigh : RootBracket
  g1Shift : RootBracket
  deriving Repr

structure QuadraticMethods where
  firstPositive : Bool
  secondPositive : Bool
  deriving Repr

structure FiniteMethods where
  q2positive : Bool
  quadratic : QuadraticMethods
  deriving Repr

def rootAt (b : RootBracket) (l : Expr) : Expr := root b.1 b.2 l
def G (b : RootBracket) (l : Expr) : Expr :=
  div (sq (rootAt b l)) (add (rat 1) (rootAt b l))
def G1 (b : RootBracket) (l : Expr) : Expr :=
  div (rootAt b l) (add (rat 1) (rootAt b l))
def G2 (b : RootBracket) (l : Expr) : Expr :=
  div (rat 1) (mul (add (rat 1) (rootAt b l)) (add (rat 2) (rootAt b l)))

def positivePart (x : Expr) : Expr := maximum x (rat 0)
def absolute (x : Expr) : Expr := maximum x (neg x)
def lambdaT (t : Expr) : Expr := mul (rat (5 / 2)) (log t)
def kbar (M : Expr) : Expr := add (rat (77 / 20)) (div (rat 10) M)
def hbar (M : Expr) : Expr := div (kbar M) (add M (rat 3))

def gaussianSlack (b : RootBracket) (t : Expr) : Expr :=
  sub (div (mul (rat (9 / 2)) (sq (sub t (rat 1)))) t)
    (mul (rat 2) (G b (lambdaT t)))

def rhoStarBlock (N nm rm : Expr) : Expr :=
  sub (mul (sub (rat 1) (sq rm)) (CoefficientExprs.rho N))
    (div (add (div (mul (rat 2) nm) (add N (rat 1)))
      (div (powNat nm 3) (mul (mul (rat 3) N) (sub (rat 1) (sq rm)))))
      (sqrt (add (rat 1) (mul (CoefficientExprs.cCoef N) (sq nm)))))

def kappaABlock (N nm rm : Expr) : Expr :=
  add (rat 2) (div
    (mul (div (mul (rat 2) (add N (rat 1)))
      (mul (mul (rat 3) N) (sub (rat 1) (sq rm)))) nm)
    (sqrt (add (rat 1) (mul (CoefficientExprs.cCoef N) (sq nm)))))

/-- The sign choice is retained, rather than replacing the minimum branch. -/
def quadraticSup (isPositive : Bool) (a b nm : Expr) : Expr :=
  if isPositive then minimum (div (sq a) (mul (rat 4) b)) (mul a nm)
  else sub (mul a nm) (mul b (sq nm))

def signGuard (isPositive : Bool) (env : Nat → Ival) (b : Expr) : Bool :=
  if isPositive then b.positiveOK env else b.upperOK env 0

def blockFirstA (Gh N nm rm : Expr) : Expr :=
  div (mul (rat 4) Gh) (rhoStarBlock N nm rm)
def blockFirstB (Gh N nm rm : Expr) : Expr :=
  sub (sub N (rat 1))
    (div (mul (kappaABlock N nm rm) Gh) (rhoStarBlock N nm rm))
def blockSecondA (N nm rm : Expr) : Expr := div (rat 4) (rhoStarBlock N nm rm)
def blockSecondB (N nm rm : Expr) : Expr :=
  sub (sub N (rat 1))
    (mul (div (rat 2) (rhoStarBlock N nm rm)) (CoefficientExprs.E2 N rm nm))

def dUbarBlock (m : QuadraticMethods) (Gh g1 N nm rm : Expr) : Expr :=
  add
    (positivePart (quadraticSup m.firstPositive
      (blockFirstA Gh N nm rm) (blockFirstB Gh N nm rm) nm))
    (mul g1 (positivePart (quadraticSup m.secondPositive
      (blockSecondA N nm rm) (blockSecondB N nm rm) nm)))

def boundedSignGuard (m : QuadraticMethods) (env : Nat → Ival)
    (Gh N nm rm : Expr) : Bool :=
  signGuard m.firstPositive env (blockFirstB Gh N nm rm) &&
  signGuard m.secondPositive env (blockSecondB N nm rm)

def phiWithRemainder (b : RootBracket) (t M D : Expr) : Expr :=
  let l := lambdaT t
  let g1 := G1 b l
  let g2 := G2 b l
  let lower := rat (71 / 20)
  let upper := kbar M
  add (mul t (positivePart (neg (gaussianSlack b t))))
    (mul (div t M) (positivePart
      (add (add (sub (mul (rat 6) (G b l)) (rat 2)) D)
        (maximum
          (add (mul (mul (rat 2) lower) g1)
            (div (mul (sq lower) g2) (add M (rat 3))))
          (add (mul (mul (rat 2) upper) g1)
            (div (mul (sq upper) g2) (add M (rat 3))))))))

def blockN (M1 : Rat) : Expr := add (rat M1) (rat 2)
def phiBlockNuMax (M2 rm : Rat) : Expr :=
  CoefficientExprs.cappedNu (add (rat M2) (rat 2)) (rat rm)

/-- This AST has no variable: `q₂` is constant on the retained block. -/
def phiBlockQ2 (M1 M2 rm : Rat) : Expr :=
  let N := blockN M1
  let nm := phiBlockNuMax M2 rm
  sub (div (mul (rhoStarBlock N nm (rat rm)) (CoefficientExprs.cCoef N)) (rat 2))
    (div (CoefficientExprs.E2 N (rat rm) nm) N)

def shiftLowArg (t : Expr) (M2 : Rat) : Expr :=
  add (lambdaT t) (div (rat (71 / 20)) (add (rat M2) (rat 3)))
def shiftHighArg (t : Expr) (M1 : Rat) : Expr := add (lambdaT t) (hbar (rat M1))
def g1ShiftArg (t : Expr) (M1 M2 rm : Rat) : Expr :=
  sub (shiftLowArg t M2)
    (div (rat 1) (mul (sq (blockN M1)) (phiBlockQ2 M1 M2 rm)))

def phiBlockGhat (b : RootBrackets) (t : Expr) (M1 M2 : Rat) : Expr :=
  maximum (G b.shiftLow (shiftLowArg t M2)) (G b.shiftHigh (shiftHighArg t M1))

def phiBlockG1Bound (b : RootBrackets) (m : FiniteMethods)
    (t : Expr) (M1 M2 rm : Rat) : Expr :=
  if m.q2positive then positivePart (neg (G1 b.g1Shift (g1ShiftArg t M1 M2 rm)))
  else positivePart (neg (G1 b.base (lambdaT t)))

def phiBlockRemainder (b : RootBrackets) (m : FiniteMethods)
    (t : Expr) (M1 M2 rm : Rat) : Expr :=
  dUbarBlock m.quadratic (phiBlockGhat b t M1 M2)
    (phiBlockG1Bound b m t M1 M2 rm) (blockN M1) (phiBlockNuMax M2 rm) (rat rm)

def phiBlock (b : RootBrackets) (m : FiniteMethods)
    (t M : Expr) (M1 M2 rm : Rat) : Expr :=
  phiWithRemainder b.base t M (phiBlockRemainder b m t M1 M2 rm)

def finiteGuard (b : RootBrackets) (m : FiniteMethods) (env : Nat → Ival)
    (t : Expr) (M1 M2 rm : Rat) : Bool :=
  signGuard m.q2positive env (phiBlockQ2 M1 M2 rm) &&
  (rhoStarBlock (blockN M1) (phiBlockNuMax M2 rm) (rat rm)).positiveOK env &&
  boundedSignGuard m.quadratic env (phiBlockGhat b t M1 M2)
    (blockN M1) (phiBlockNuMax M2 rm) (rat rm)

/-- Safety here checks every root bracket and every divided expression. -/
def finitePass (b : RootBrackets) (m : FiniteMethods) (env : Nat → Ival)
    (t M : Expr) (M1 M2 rm bound : Rat) : Bool :=
  finiteGuard b m env t M1 M2 rm && (phiBlock b m t M M1 M2 rm).upperOK env bound

def Ghat (b : RootBrackets) (t : Expr) (M1 : Rat) : Expr :=
  maximum (G b.base (lambdaT t)) (G b.shiftHigh (shiftHighArg t M1))

def infiniteFirstB (b : RootBrackets) (t : Expr) (M1 rm : Rat) : Expr :=
  sub (sub (blockN M1) (rat 1))
    (div (mul (CoefficientExprs.kappaA (blockN M1) (rat rm)) (Ghat b t M1))
      (CoefficientExprs.rhoStar (blockN M1) (rat rm)))

def infiniteBetaE (M1 rm : Rat) : Expr :=
  CoefficientExprs.betaE (blockN M1) (rat rm)
    (CoefficientExprs.cappedNu (blockN M1) (rat rm))

/-- The all-`ν` AM-GM formula, with its actual absolute derivative. -/
def phiInfiniteBlockRemainder (b : RootBrackets) (t : Expr) (M1 rm : Rat) : Expr :=
  let rs := CoefficientExprs.rhoStar (blockN M1) (rat rm)
  let Gh := Ghat b t M1
  add (div (mul (rat 4) (sq Gh)) (mul (sq rs) (infiniteFirstB b t M1 rm)))
    (div (mul (absolute (G1 b.base (lambdaT t))) (rat 4))
      (mul (sq rs) (infiniteBetaE M1 rm)))

def phiInfiniteBlock (b : RootBrackets) (t M : Expr) (M1 rm : Rat) : Expr :=
  phiWithRemainder b.base t M (phiInfiniteBlockRemainder b t M1 rm)

def infiniteGuard (b : RootBrackets) (env : Nat → Ival)
    (t : Expr) (M1 rm : Rat) : Bool :=
  (CoefficientExprs.rhoStar (blockN M1) (rat rm)).positiveOK env &&
  (infiniteFirstB b t M1 rm).positiveOK env && (infiniteBetaE M1 rm).positiveOK env

def infinitePass (b : RootBrackets) (env : Nat → Ival)
    (t M : Expr) (M1 rm bound : Rat) : Bool :=
  infiniteGuard b env t M1 rm && (phiInfiniteBlock b t M M1 rm).upperOK env bound

end Erdos993Lean.Analytic.V22.Compute.RayExprs
