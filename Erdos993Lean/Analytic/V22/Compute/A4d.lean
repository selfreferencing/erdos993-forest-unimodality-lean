import Erdos993Lean.Analytic.V22.Compute.WindowExprs

/-! The 33 exact `(r,N)` subblocks inside the seven A4d source log groups.
This recipe directly encloses the retained termwise worst-end formula. -/

namespace Erdos993Lean.Analytic.V22.Compute.A4d
open Expr

abbrev Block := Rat × Rat × Rat × Rat

def blocks : List Block :=
  (([3793/10000,2/5,21/50,11/25,23/50,12/25] : List Rat).zip
    [2/5,21/50,11/25,23/50,12/25,1/2] |>.flatMap fun r =>
      (([229/20,25/2,14,16,18] : List Rat).zip [25/2,14,16,18,20]).map
        (fun n => (r.1,r.2,n.1,n.2))) ++
    [(3793/10000,1/2,20,23),(3793/10000,1/2,23,26),(3793/10000,1/2,26,291/10)]

def yTilde (r N : Expr) : Expr :=
  add r (div (mul (WindowExprs.aHat r) (add N (rat 1))) (rat 2))

def lower (ra rb Na Nb : Expr) : Expr :=
  let third := add
    (div (rat 1) (mul (add Na (rat 1)) (sqrt (CoefficientExprs.cCoef Na))))
    (div (sq rb) (mul (mul (rat 6) (sub (rat 1) (sq rb)))
      (sqrt (CoefficientExprs.cCoef Na))))
  sub
    (add (div (rat (71/20)) (add Nb (rat 1)))
      (div (mul (CoefficientExprs.rhoStar Na rb) (WindowExprs.Delta ra Na)) (rat 2)))
    (add
      (add
        (add (div (mul (sq rb) (CoefficientExprs.rho Nb)) (rat 2))
          (div (mul (yTilde rb Nb)
            (sqrt (add Nb (mul (sq rb) (sq (sub Nb (rat 1))))))) (add Nb (rat 1))))
        third)
      (mul (add Nb (rat 1)) (WindowExprs.cr rb)))

def recipe (b : Block) : Expr := lower (rat b.1) (rat b.2.1) (rat b.2.2.1) (rat b.2.2.2)

def env : Nat → TailCert.Compute.Ival := fun _ => TailCert.Compute.ofRat 0
def passes (b : Block) : Bool := (recipe b).nonnegativeOK env
def check : Bool := blocks.all passes

end Erdos993Lean.Analytic.V22.Compute.A4d
