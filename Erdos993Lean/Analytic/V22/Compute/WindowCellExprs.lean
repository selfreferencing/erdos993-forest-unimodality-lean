import Erdos993Lean.Analytic.V22.Compute.WindowExprs
import Erdos993Lean.Analytic.V22.RationalData

/-!
# Exact fixed-class D3 recipes

All four root calls retain explicit rational brackets. `Dlo` and `N0` are
exact rational inputs, while `t` and the actual activity `r` remain expression
inputs. The fallback takes the smaller of the two logarithmic branches, so
it is available without a sign or window-condition assumption. A separate
condition margin can license the stronger `Wlo` recipe.
-/

namespace Erdos993Lean.Analytic.V22.Compute.WindowCellExprs

open Expr

structure RootBrackets where
  g0Lo : Rat
  g0Hi : Rat
  shiftedLo : Rat
  shiftedHi : Rat
  sbarLo : Rat
  sbarHi : Rat
  upperLo : Rat
  upperHi : Rat
  deriving Repr

def GAt (arg : Expr) (lo hi : Rat) : Expr :=
  let s := root lo hi arg
  div (sq s) (add (rat 1) s)

def yTilde (r N : Expr) : Expr :=
  add r (div (mul (WindowExprs.aHat r) (add N (rat 1))) (rat 2))
def epsilonPrime (r N : Expr) : Expr :=
  div (mul (mul (rat 4) (yTilde r N)) (WindowExprs.sN r N)) (add N (rat 1))
def c0Prime (r N : Expr) : Expr :=
  div (mul (rat 2) (sq (yTilde r N))) (add N (rat 1))
def rhoU (r N : Expr) : Expr :=
  sub (mul (sub (rat 1) (sq r)) (CoefficientExprs.rho N))
    (div (epsilonPrime r N) (sqrt (WindowExprs.gamma r N)))

/-- The positive terms of eU; the source window recipe drops `-c0Prime`
before interval evaluation, avoiding artificial cancellation dependency. -/
def eUDrop (r N : Expr) : Expr :=
  add
    (add (div (mul (sq r) (CoefficientExprs.rho N)) (rat 2))
      (mul (div (epsilonPrime r N) (rat 2))
        (add (sqrt (WindowExprs.gamma r N)) (div (rat 1) (sqrt (WindowExprs.gamma r N))))))
    (mul (add N (rat 1)) (WindowExprs.cr r))
def eU (r N : Expr) : Expr := sub (eUDrop r N) (c0Prime r N)

def Wlo (Dlo : Rat) : Expr := minimum (rat 3) (add (rat 1) (rat Dlo))
def qShift (N0 : Rat) (t r : Expr) : Expr :=
  add (add (WindowExprs.lambdaT t) (EarlyCoefficients.hbar (sub (rat N0) (rat 2))))
    (WindowExprs.windowEL r (rat N0))

def ghat (N0 : Rat) (t : Expr) (br : RootBrackets) : Expr :=
  maximum (GAt (WindowExprs.lambdaT t) br.g0Lo br.g0Hi)
    (GAt (add (WindowExprs.lambdaT t) (EarlyCoefficients.hbar (sub (rat N0) (rat 2))))
      br.shiftedLo br.shiftedHi)
def sbar (N0 : Rat) (t r : Expr) (br : RootBrackets) : Expr :=
  WindowExprs.windowSbar t r (rat N0) br.sbarLo br.sbarHi

def Xsplit (Dlo N0 : Rat) (t r : Expr) (br : RootBrackets) : Expr :=
  sub
    (add (sub (rat 1) (mul (div (rat 2) (CoefficientExprs.rho (rat N0))) (ghat N0 t br)))
      (div (rat Dlo) (add (add (rat 1) (sbar N0 t r br))
        (div (mul (WindowExprs.windowRhoLbar r (rat N0)) (rat Dlo)) (rat 2)))))
    (div (mul (rat 2) (WindowExprs.windowEL r (rat N0))) (CoefficientExprs.rho (rat N0)))

def logByRho (N0 : Rat) (t r : Expr) : Expr :=
  sub (rat 1) (div (mul (rat 2) (qShift N0 t r)) (CoefficientExprs.rho (rat N0)))
def logByRhoLbar (N0 : Rat) (t r : Expr) : Expr :=
  sub (rat 1) (div (mul (rat 2) (qShift N0 t r)) (WindowExprs.windowRhoLbar r (rat N0)))

def fallbackLower (Dlo N0 : Rat) (t r : Expr) (br : RootBrackets) : Expr :=
  minimum (Wlo Dlo) (maximum (Xsplit Dlo N0 t r br)
    (minimum (logByRho N0 t r) (logByRhoLbar N0 t r)))

def upperLambda (N0 : Rat) (t r : Expr) : Expr :=
  sub
    (add (add (WindowExprs.lambdaT t) (div (rat (71 / 20)) (add (rat N0) (rat 1))))
      (div (mul (rhoU r (rat N0)) (WindowExprs.Delta r (rat N0))) (rat 2)))
    (eUDrop r (rat N0))

def upperRecipe (Dlo N0 rb : Rat) (t r : Expr) (br : RootBrackets) : Expr :=
  sub (add (rat 1) (rat Dlo))
    (mul (div (rat 2) (CoefficientExprs.rhoStar (rat N0) (rat rb)))
      (GAt (minimum (rat 0) (upperLambda N0 t r)) br.upperLo br.upperHi))

def lowerRecipe (Dlo N0 rb : Rat) (t r : Expr) (br : RootBrackets) : Expr :=
  minimum (fallbackLower Dlo N0 t r br) (minimum (rat 3) (upperRecipe Dlo N0 rb t r br))

/-- This nonnegative margin licenses the source's window-condition branch.
The choice depends only on the retained exact rational Dlo. -/
def conditionMargin (Dlo N0 : Rat) (t r : Expr) : Expr :=
  let lhs := add (qShift N0 t r) (WindowExprs.windowRhoLbar r (rat N0))
  if 2 ≤ Dlo then
    sub (log (add (rat 1) (div (mul (CoefficientExprs.rho (rat N0)) (sub (rat Dlo) (rat 2))) (rat 2)))) lhs
  else neg lhs

def licensedRecipe (Dlo N0 rb : Rat) (t r : Expr) (br : RootBrackets) : Expr :=
  minimum (Wlo Dlo) (minimum (rat 3) (upperRecipe Dlo N0 rb t r br))

def target (b beta : Rat) (t : Expr) : Expr :=
  add (add (sub t (mul (rat (9 / 2)) (sq (sub t (rat 1))))) (rat b))
    (mul (rat beta) (sub t (rat 1)))
def positiveRequirement (b beta : Rat) (t : Expr) : Expr := div (target b beta t) t
def negativeRequirement (N0 b beta : Rat) (t : Expr) : Expr :=
  div (mul (target b beta t) (sub (rat N0) (rat 2))) (mul t (rat N0))
def crossingRequirement (b beta : Rat) (t : Expr) : Expr :=
  maximum (positiveRequirement b beta t) (rat 0)

def cellStart (c : V22Class) (cell : V22Cell) : Rat := c.muD * cell.lo + 2
def classDlo (c : V22Class) (cell : V22Cell) : Rat :=
  let N0 := cellStart c cell
  c.ra^2 * (N0^2 - N0 + 1) / ((1 - c.ra^2) * N0)
def classLowerRecipe (c : V22Class) (cell : V22Cell) (t r : Expr) (br : RootBrackets) : Expr :=
  lowerRecipe (classDlo c cell) (cellStart c cell) c.rb t r br
def classLicensedRecipe (c : V22Class) (cell : V22Cell) (t r : Expr) (br : RootBrackets) : Expr :=
  licensedRecipe (classDlo c cell) (cellStart c cell) c.rb t r br
def classConditionMargin (c : V22Class) (cell : V22Cell) (t r : Expr) : Expr :=
  conditionMargin (classDlo c cell) (cellStart c cell) t r

def positiveMargin (c : V22Class) (cell : V22Cell) (t r : Expr) (br : RootBrackets) : Expr :=
  sub (classLowerRecipe c cell t r br) (positiveRequirement c.b c.beta t)
def negativeMargin (c : V22Class) (cell : V22Cell) (t r : Expr) (br : RootBrackets) : Expr :=
  sub (classLowerRecipe c cell t r br) (negativeRequirement (cellStart c cell) c.b c.beta t)
def crossingMargin (c : V22Class) (cell : V22Cell) (t r : Expr) (br : RootBrackets) : Expr :=
  sub (classLowerRecipe c cell t r br) (crossingRequirement c.b c.beta t)

end Erdos993Lean.Analytic.V22.Compute.WindowCellExprs
