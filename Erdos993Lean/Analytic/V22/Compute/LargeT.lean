import Erdos993Lean.Analytic.V22.Compute.CoefficientExprs
import Erdos993Lean.Analytic.V22.Compute.Box

/-! A5/D4 use the exact radical split through an affine coordinate in [0,1].
The enclosure grids refine the source: 600 first-range and 3000 second-range
pieces. The source uses 4/8 pieces for A5 and 8/12 pieces for D4.
No rounded split constant is used. -/

namespace Erdos993Lean.Analytic.V22.Compute.LargeT
open Expr

def firstPieces : List Span := subdivide 0 1 600
def secondPieces : List Span := subdivide 0 1 3000
def cut (rm Nstar : Rat) : Expr := mul (rat rm) (sqrt (rat Nstar))
def firstNu (rm Nstar : Rat) : Expr := mul (cut rm Nstar) (var 0)
def secondNu (rm Nstar : Rat) : Expr :=
  add (cut rm Nstar) (mul (sub (rat 6) (cut rm Nstar)) (var 0))
def threshold (N : Expr) (rm : Rat) : Expr :=
  log (mul (rat (257/100)) (CoefficientExprs.rhoStar N (rat rm)))
def firstMargin (rm Nstar : Rat) : Expr :=
  sub (threshold (rat Nstar) rm)
    (CoefficientExprs.Xbar (firstNu rm Nstar) (rat Nstar) (rat rm))
def secondN (rm Nstar : Rat) : Expr := div (sq (secondNu rm Nstar)) (sq (rat rm))
def secondMargin (rm Nstar : Rat) : Expr :=
  sub (threshold (secondN rm Nstar) rm)
    (CoefficientExprs.Xbar (secondNu rm Nstar) (secondN rm Nstar) (rat rm))
def largeConstant (N : Expr) : Expr :=
  mul (mul (mul (rat 2) (exp (rat (-1/2)))) (rpow (rat (8/5)) (-3/2)))
    (exp (add (div (rat (3/4)) N) (div (rat (11/10)) (sq N))))
def zeroEnv : Nat → TailCert.Compute.Ival := fun _ => TailCert.Compute.ofRat 0
def check (rm Nstar : Rat) : Bool :=
  partitionFrom 0 1 firstPieces && partitionFrom 0 1 secondPieces &&
  nonnegativeOn (firstMargin rm Nstar) firstPieces &&
  nonnegativeOn (secondMargin rm Nstar) secondPieces &&
  (largeConstant (rat Nstar)).upperOK zeroEnv (249/400)
def a5Check : Bool := check (1/4) (162/5)
def d4Check : Bool := check (1/2) 66

end Erdos993Lean.Analytic.V22.Compute.LargeT
