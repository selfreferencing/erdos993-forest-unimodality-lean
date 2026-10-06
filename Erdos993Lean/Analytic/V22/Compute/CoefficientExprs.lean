import Erdos993Lean.Analytic.V22.Compute.Expr

/-!
# Exact coefficient expressions for the version 2.2 checks

API: the builders in `V22.Compute.CoefficientExprs` accept expressions for
`N`, `rm` and, where required, an explicit `nm` or `nu`. They return syntax,
not bounds. `cappedNu N rm` is the exact expression `min(6,rm*sqrt(N))`.
Every fraction is rational and every denominator remains guarded by
`Expr.safe`. The real correspondence is proved separately.
-/

namespace Erdos993Lean.Analytic.V22.Compute.CoefficientExprs

open Expr

def cCoef (N : Expr) : Expr := sub (rat 1) (div (rat 1) N)
def rho (N : Expr) : Expr := div N (add N (rat 1))
def Z0 (N : Expr) : Expr := div (sqrt N) (add N (rat 1))
def phiM (N rm : Expr) : Expr := add (rat 1) (div (mul (rat 2) rm) (sqrt N))

def KL (N rm : Expr) : Expr :=
  add (rat 1) (div (sq (phiM N rm))
    (sub (rat 1) (mul (sq (Z0 N)) (sq (phiM N rm)))))

def KR (N rm : Expr) : Expr := div (rat 1) (sub (rat 1) (sq (add rm (Z0 N))))

def cL1 (N rm : Expr) : Expr :=
  div (mul (rat 4) (KL N rm)) (mul N (sub (rat 1) (sq rm)))

def cL2 (N rm : Expr) : Expr :=
  div (add (div (mul (rat 4) (KL N rm)) (sq N)) (div (rat 1) N))
    (sub (rat 1) (sq rm))

def cR1 (N rm : Expr) : Expr :=
  div (mul (rat 2) (KR N rm)) (mul (add N (rat 1)) (sub (rat 1) (sq rm)))

def cR2 (N rm : Expr) : Expr :=
  div (add (KR N rm) (rat 1)) (mul N (sub (rat 1) (sq rm)))

def alpha1 (N rm : Expr) : Expr :=
  add (div (rat 2) (sqrt (sub (rat 1) (sq rm))))
    (div (maximum (cL1 N rm) (cR1 N rm)) (rat 12))

def alpha2 (N rm : Expr) : Expr :=
  add (div (rat 2) (mul N (sub (rat 1) (sq rm))))
    (div (maximum (cL2 N rm) (cR2 N rm)) (rat 12))

def rhoStar (N rm : Expr) : Expr :=
  sub (sub (mul (sub (rat 1) (sq rm)) (rho N))
    (div (rat 2) (mul (add N (rat 1)) (sqrt (cCoef N)))))
    (div (sq rm) (mul (mul (rat 3) (sub (rat 1) (sq rm))) (sqrt (cCoef N))))

def kappaA (N rm : Expr) : Expr :=
  add (rat 2) (div (mul (rat 2) (add N (rat 1)))
    (mul (mul (mul (rat 3) N) (sub (rat 1) (sq rm))) (sqrt (cCoef N))))

def e2 : Expr := rat (1 / 2)
def e3 (rm : Expr) : Expr := div (rat 5) (mul (rat 6) (sub (rat 1) (sq rm)))
def e4 (N rm : Expr) : Expr :=
  div (add N (rat 1)) (mul (mul (rat 12) N) (sq (sub (rat 1) (sq rm))))
def e5 (rm : Expr) : Expr := div (rat 1) (mul (rat 12) (sq (sub (rat 1) (sq rm))))

def E2 (N rm nm : Expr) : Expr :=
  add (add (add e2 (mul (e3 rm) nm)) (mul (e4 N rm) (sq nm)))
    (mul (e5 rm) (powNat nm 3))

def cappedNu (N rm : Expr) : Expr := minimum (rat 6) (mul rm (sqrt N))

def ebar (N rm nm : Expr) : Expr :=
  div (add (mul (alpha1 N rm) nm) (mul (alpha2 N rm) (sq nm))) (add N (rat 1))

def betaE (N rm nm : Expr) : Expr :=
  sub (sub N (rat 1)) (mul (div (rat 2) (rhoStar N rm)) (E2 N rm nm))

def lambdaBonusF (N rm : Expr) : Expr :=
  sub (sub (div (mul (sub N (rat 1)) (rhoStar N rm)) (rat 2))
    (E2 N rm (cappedNu N rm))) (div (add N (rat 1)) (mul (rat (71 / 20)) N))

def Xbar (nu N rm : Expr) : Expr :=
  sub
    (add
      (div (mul (add N (rat 1)) (powNat nu 4))
        (mul (mul (rat 12) (sq N)) (sq (sub (rat 1) (sq rm)))))
      (mul (div (mul nu (sqrt (add (rat 1) (sq nu)))) (add N (rat 1)))
        (add (rat 1) (div (mul (sq nu) (add N (rat 1)))
          (mul (mul (rat 6) N) (sub (rat 1) (sq rm)))))))
    (mul (div (rhoStar N rm) (rat 2)) (add (rat 1) (mul (sq nu) (cCoef N))))

end Erdos993Lean.Analytic.V22.Compute.CoefficientExprs
