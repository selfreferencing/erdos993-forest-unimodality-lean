import Erdos993Lean.Analytic.V22.Compute.EarlyCoefficients
import Erdos993Lean.Analytic.V22.RationalData

/-!
# Frozen wing-cell expressions

Every coefficient is frozen at the original `muW*cell.lo+2`. A later t-grid
may refine the cell, but its endpoint must not replace `cell.lo` here. Root
brackets for the base and shifted arguments are retained explicitly. The
source's four wing conditions and the algebraic minimum conditions remain
separate checker inputs.
-/

namespace Erdos993Lean.Analytic.V22.Compute.WingExprs

open Expr

structure RootBrackets where
  baseLo : Rat
  baseHi : Rat
  shiftedLo : Rat
  shiftedHi : Rat
  deriving Repr

def N0 (c : V22WingClass) (cell : V22Cell) : Rat := c.muW * cell.lo + 2
def baseRoot (t : Expr) (br : RootBrackets) : Expr :=
  root br.baseLo br.baseHi (mul (rat (5 / 2)) (log t))
def G0 (t : Expr) (br : RootBrackets) : Expr :=
  div (sq (baseRoot t br)) (add (rat 1) (baseRoot t br))
def G1 (t : Expr) (br : RootBrackets) : Expr :=
  div (baseRoot t br) (add (rat 1) (baseRoot t br))
def G2 (t : Expr) (br : RootBrackets) : Expr :=
  div (rat 1) (mul (add (rat 1) (baseRoot t br)) (add (rat 2) (baseRoot t br)))
def absolute (x : Expr) : Expr := maximum x (neg x)

def Ghat (c : V22WingClass) (cell : V22Cell) (t : Expr) (br : RootBrackets) : Expr :=
  let M0 := sub (rat (N0 c cell)) (rat 2)
  let shifted := root br.shiftedLo br.shiftedHi
    (add (mul (rat (5 / 2)) (log t)) (EarlyCoefficients.hbar M0))
  maximum (G0 t br) (div (sq shifted) (add (rat 1) shifted))

def slack (t : Expr) (br : RootBrackets) : Expr :=
  sub (div (mul (rat (9 / 2)) (sq (sub t (rat 1)))) t) (mul (rat 2) (G0 t br))
def nuMax (c : V22WingClass) (cell : V22Cell) : Expr :=
  CoefficientExprs.cappedNu (rat (N0 c cell)) (rat c.rb)
def rhoStar (c : V22WingClass) (cell : V22Cell) : Expr :=
  CoefficientExprs.rhoStar (rat (N0 c cell)) (rat c.rb)
def betaE (c : V22WingClass) (cell : V22Cell) : Expr :=
  CoefficientExprs.betaE (rat (N0 c cell)) (rat c.rb) (nuMax c cell)

def kPrime (c : V22WingClass) (cell : V22Cell) (t : Expr) (br : RootBrackets) : Expr :=
  div (mul (CoefficientExprs.kappaA (rat (N0 c cell)) (rat c.rb)) (Ghat c cell t br))
    (rhoStar c cell)
def bPrime (c : V22WingClass) (cell : V22Cell) (t : Expr) (br : RootBrackets) : Expr :=
  div (mul (rat 4) (Ghat c cell t br)) (rhoStar c cell)
def C (c : V22WingClass) (cell : V22Cell) (t n : Expr) (br : RootBrackets) : Expr :=
  sub (div (sub n (rat 1)) (sub (rat 1) (sq (rat c.ra)))) (kPrime c cell t br)
def De (c : V22WingClass) (cell : V22Cell) : Expr :=
  div (rat 4) (mul (sq (rhoStar c cell)) (betaE c cell))
def tau1 (c : V22WingClass) (cell : V22Cell) (t : Expr) (br : RootBrackets) : Expr :=
  let M0 := sub (rat (N0 c cell)) (rat 2)
  sub (add (sub (rat 2) (mul (rat 6) (G0 t br))) (mul (rat (71 / 10)) (absolute (G1 t br))))
    (div (mul (sq (EarlyCoefficients.kbar M0)) (G2 t br)) (add M0 (rat 3)))

def A (c : V22WingClass) : Expr := rat (c.ra^2/(1-c.ra^2))
def B (c : V22WingClass) (cell : V22Cell) (t : Expr) (br : RootBrackets) : Expr :=
  sub (sub (slack t br) (A c)) (mul (kPrime c cell t br) (sq (rat c.ra)))
def sqrtSlope (c : V22WingClass) (cell : V22Cell) (t : Expr) (br : RootBrackets) : Expr :=
  mul (bPrime c cell t br) (rat c.ra)
def D (c : V22WingClass) (cell : V22Cell) (t : Expr) (br : RootBrackets) : Expr :=
  sub (sub (tau1 c cell t br) (mul (rat 2) (slack t br)))
    (mul (absolute (G1 t br)) (De c cell))

def startingSlope (c : V22WingClass) (cell : V22Cell) (t : Expr) (br : RootBrackets) : Expr :=
  sub (add (mul (mul (rat 2) (A c)) (rat (N0 c cell))) (B c cell t br))
    (div (sqrtSlope c cell t br) (mul (rat 2) (sqrt (rat (N0 c cell)))))
def startingValue (c : V22WingClass) (cell : V22Cell) (t : Expr) (br : RootBrackets) : Expr :=
  add (sub (add (mul (A c) (sq (rat (N0 c cell)))) (mul (B c cell t br) (rat (N0 c cell))))
    (mul (sqrtSlope c cell t br) (sqrt (rat (N0 c cell))))) (D c cell t br)
def tangentBound (c : V22WingClass) (cell : V22Cell) (t : Expr) (br : RootBrackets) (N1 : Rat) : Expr :=
  sub (sub (D c cell t br) (div (mul (sqrtSlope c cell t br) (sqrt (rat N1))) (rat 2)))
    (div (sq (sub (B c cell t br) (div (sqrtSlope c cell t br) (mul (rat 2) (sqrt (rat N1))))))
      (mul (rat 4) (A c)))

/-- Strict c(N0), nonnegative ν margin, strict rhoStar and strict betaE. -/
def sourceConditions (c : V22WingClass) (cell : V22Cell) (t : Expr) (br : RootBrackets) :
    Expr × Expr × Expr × Expr :=
  let c0 := C c cell t (rat (N0 c cell)) br
  (c0, sub (mul (rat c.ra) (sqrt (rat (N0 c cell)))) (div (bPrime c cell t br) (mul (rat 2) c0)),
    rhoStar c cell, betaE c cell)

def tangentMultipliers : List Rat := [1, 3/2, 2, 3, 4, 6, 8]
def tangentPoints (c : V22WingClass) (cell : V22Cell) : List Rat :=
  tangentMultipliers.map fun m => N0 c cell * m

end Erdos993Lean.Analytic.V22.Compute.WingExprs
