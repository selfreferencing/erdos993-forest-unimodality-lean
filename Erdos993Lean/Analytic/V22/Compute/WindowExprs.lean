import Erdos993Lean.Analytic.V22.Compute.EarlyCoefficients

/-!
# Exact window expressions

Builders keep the real functions' argument order (`r,N,W` and `t,r,N`).
`windowSbar` takes the root certificate's rational lower/upper endpoints as
two final arguments. Shape conditions are represented by individual margins:
the first two require strict positivity, while c3 and c3′ require
nonnegativity. This module contains no conditional window or sign branches.
-/

namespace Erdos993Lean.Analytic.V22.Compute.WindowExprs

open Expr

def varianceR (r : Expr) : Expr := div (sub (rat 1) (sq r)) (rat 4)
def Delta (r N : Expr) : Expr :=
  div (mul (sq r) (add (sub (sq N) N) (rat 1))) (mul (sub (rat 1) (sq r)) N)
def gamma (r N : Expr) : Expr := add (rat 1) (Delta r N)
def artanh (r : Expr) : Expr := div (log (div (add (rat 1) r) (sub (rat 1) r))) (rat 2)
def aHat (r : Expr) : Expr := sub (artanh r) r
def sN (r N : Expr) : Expr := sqrt (mul (varianceR r) N)

def epsilon (r N : Expr) : Expr :=
  div (mul r (sqrt N)) (mul (sqrt (varianceR r)) (add N (rat 1)))
def c0 (r N : Expr) : Expr :=
  div (sq r) (mul (mul (rat 2) (varianceR r)) (add N (rat 1)))
def ZL (r N W : Expr) : Expr :=
  div (mul (rat 2) (add (mul (sqrt W) (sN r N)) r)) (add N (rat 1))
def ZR (r N W : Expr) : Expr :=
  div (mul (mul (rat 2) (sqrt W)) (sN r N)) (add N (rat 1))

def quarticError (r N W : Expr) : Expr :=
  maximum
    (div (mul (add N (rat 1)) (powNat (ZL r N W) 4))
      (mul (mul (rat 12) (sub (rat 1) (sq (ZL r N W)))) (sub (rat 1) (sq r))))
    (div (mul (add N (rat 1)) (powNat (ZR r N W) 4))
      (mul (mul (rat 12) (sub (rat 1) (sq (add r (ZR r N W))))) (sub (rat 1) (sq r))))

def cr (r : Expr) : Expr :=
  div (add (sq (artanh r)) (log (sub (rat 1) (sq r)))) (rat 2)

def windowEL (r N : Expr) : Expr :=
  add (add (c0 r N) (quarticError r N (rat 3)))
    (mul (epsilon r N) (add (div (sqrt (rat 3)) (rat 2))
      (div (rat 1) (mul (rat 2) (sqrt (rat 3))))))
def windowRhoL (r N : Expr) : Expr :=
  add (CoefficientExprs.rho N) (div (epsilon r N) (sqrt (rat 3)))
def windowRhoLbar (r N : Expr) : Expr := add (rat 1) (div (epsilon r N) (sqrt (rat 3)))

def lambdaT (t : Expr) : Expr := mul (rat (5 / 2)) (log t)
def windowSbar (t r N : Expr) (lo hi : Rat) : Expr :=
  EarlyCoefficients.positivePart (root lo hi
    (add (add (lambdaT t) (EarlyCoefficients.hbar (sub N (rat 2)))) (windowEL r N)))

/-- D1's c1 margin, checked strictly positive. -/
def windowCondition1 (r N : Expr) : Expr := sub (rat 1) (ZL r N (rat 3))
/-- D1's c2 margin, checked strictly positive. -/
def windowCondition2 (r N : Expr) : Expr := sub (rat 1) (add r (ZR r N (rat 3)))
/-- D1's c3 margin, checked nonnegative. -/
def windowCondition3 (r N : Expr) : Expr :=
  sub (div (mul (rat 12) (sub (rat 1) (sq (add r (ZR r N (rat 3))))))
    (mul (sub (rat 1) (sq r)) (CoefficientExprs.rho N))) (rat 3)
/-- D1′'s c3′ margin, checked nonnegative. -/
def c3PrimeMargin (r N : Expr) : Expr :=
  sub (div (mul (rat 12) (sub (rat 1) (sq (add r (ZR r N (rat 3))))))
    (sub (rat 1) (sq r))) (rat 3)

def windowConditions (r N : Expr) : Expr × Expr × Expr :=
  (windowCondition1 r N, windowCondition2 r N, windowCondition3 r N)
def persistentWindowConditions (r N : Expr) : Expr × Expr × Expr :=
  (windowCondition1 r N, windowCondition2 r N, c3PrimeMargin r N)

def uMonoDerivative (r N : Expr) : Expr :=
  let m := add N (rat 1)
  sub
    (sub
      (sub
        (sub
          (sub
            (sub (sub (div (sq r) (rat 2)) (mul (aHat r) r)) (cr r))
            (div (mul (rat 2) (sq r)) m))
          (div (mul (rat 4) (sq r)) (sq m)))
        (div (rat 1) (mul m (sub m (rat 2)))))
      (div (aHat r) (mul (mul (rat 2) r) (sub m (rat 2)))))
    (div (rat (71 / 20)) (sq m))

def windowH (r N : Expr) : Expr :=
  sub (mul (aHat r) (add (rat 1) (mul (mul (rat 2) (sq r)) (sub N (rat 1)))))
    (div (mul (mul (mul (rat 2) r) (sub (rat 1) (mul (rat 4) (sq r)))) (sub N (rat 1)))
      (sq (add N (rat 1))))

end Erdos993Lean.Analytic.V22.Compute.WindowExprs
