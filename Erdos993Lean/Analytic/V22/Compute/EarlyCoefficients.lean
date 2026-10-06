import Erdos993Lean.Analytic.V22.Compute.CoefficientExprs

/-!
# A2, A3 and A3′ coefficient recipes

The ASTs below retain the exact source constants and the conservative
coefficient choices of `fc_check_A.env_cell`. The A2 branch is selected by
the exact rational left cell endpoint, never by a floating approximation.
All divisions, square roots and rational powers retain `Expr.safe` guards.
These are numerical recipes; derivative and endpoint transport are separate
proof obligations and are not asserted here.
-/

namespace Erdos993Lean.Analytic.V22.Compute.EarlyCoefficients

open Expr

def positivePart (x : Expr) : Expr := maximum x (rat 0)

def tOfS (s : Expr) : Expr := rpow (mul (exp s) (add (rat 1) s)) (2 / 5)
def a2M0 (mean : Rat) (sa : Expr) : Expr := mul (rat mean) (tOfS sa)
def a2N0 (M0 : Expr) : Expr := add M0 (rat 2)
def a2NuMax (N0 rm : Expr) : Expr := mul rm (sqrt N0)

def kbar (M0 : Expr) : Expr := add (rat (77 / 20)) (div (rat 10) M0)
def hbar (M0 : Expr) : Expr := div (kbar M0) (add M0 (rat 3))
def lambdaOfS (s : Expr) : Expr := add s (log (add (rat 1) s))
def G0 (s : Expr) : Expr := div (sq s) (add (rat 1) s)
def G1 (s : Expr) : Expr := div s (add (rat 1) s)
def G2 (s : Expr) : Expr := div (rat 1) (mul (add (rat 1) s) (add (rat 2) s))

def phi (s : Expr) : Expr :=
  sub (mul (rat (18 / 25)) (sq (sub (rat 2) (div s (rat 2)))))
    (div (rat 2) (add (rat 1) s))

/-- The source upper bound `σ₀≤(s+h)_+`, not an unproved root evaluation. -/
def sigmaBound (s M0 : Expr) : Expr := positivePart (add s (hbar M0))

/-- The source bound `Ghat≤max(G₀,((λ+h)_+)²/4)`. -/
def ghatBound (s M0 : Expr) : Expr :=
  maximum (G0 s) (div (sq (positivePart (add (lambdaOfS s) (hbar M0)))) (rat 4))

/-- Explicit lower denominator with the retained conservative `σ₀`. -/
def betaLRecipe (s N0 M0 rm nm : Expr) : Expr :=
  sub
    (sub (mul (sub N0 (rat 1)) (sub (rat 1) (CoefficientExprs.ebar N0 rm nm)))
      (mul (mul (rat 2) (sigmaBound s M0)) (CoefficientExprs.alpha2 N0 rm)))
    (div
      (add
        (add (mul (rat 2) (sq (CoefficientExprs.alpha1 N0 rm)))
          (mul (mul (mul (rat 4) (CoefficientExprs.alpha1 N0 rm)) (CoefficientExprs.alpha2 N0 rm)) nm))
        (mul (mul (rat 2) (sq (CoefficientExprs.alpha2 N0 rm))) (sq nm)))
      (add N0 (rat 1)))

def dLRecipe (s N0 M0 rm nm : Expr) : Expr :=
  div (sq (mul (sigmaBound s M0) (CoefficientExprs.alpha1 N0 rm))) (betaLRecipe s N0 M0 rm nm)

def upperDenominator (s N0 M0 rm : Expr) : Expr :=
  sub (sub N0 (rat 1))
    (div (mul (CoefficientExprs.kappaA N0 rm) (ghatBound s M0)) (CoefficientExprs.rhoStar N0 rm))

def dURecipe (s N0 M0 rm nm : Expr) : Expr :=
  add
    (div (mul (rat 4) (sq (ghatBound s M0)))
      (mul (sq (CoefficientExprs.rhoStar N0 rm)) (upperDenominator s N0 M0 rm)))
    (div (mul (positivePart (neg (G1 s))) (rat 4))
      (mul (sq (CoefficientExprs.rhoStar N0 rm)) (CoefficientExprs.betaE N0 rm nm)))

def templateBase (s M0 k : Expr) : Expr :=
  sub (sub (sub (rat 2) (mul (rat 6) (G0 s)))
    (mul (mul (rat 2) k) (G1 s)))
    (div (mul (sq k) (G2 s)) (add M0 (rat 3)))

/-- One source A2 endpoint recipe. The nominal cell endpoint selects the
Gaussian and upper-range branches; every actual `s` remains an input. -/
def a2Envelope (sa : Rat) (s M0 rm k : Expr) : Expr :=
  let N0 := a2N0 M0
  let nm := a2NuMax N0 rm
  let base := templateBase s M0 k
  let base := if 0 ≤ sa then add base (mul (mul M0 (sq s)) (phi s)) else base
  let dL := dLRecipe s N0 M0 rm nm
  let d := if sa < 0 then maximum dL (dURecipe s N0 M0 rm nm) else dL
  sub base d

/-- Both exact template endpoint choices for one source A2 cell. -/
def a2EndpointRecipes (sa : Rat) (s M0 rm : Expr) : Expr × Expr :=
  (a2Envelope sa s M0 rm (rat (71 / 20)), a2Envelope sa s M0 rm (kbar M0))

/-- Every A2 coefficient condition, expressed as positivity/nonnegativity
of an AST. The guard on the remainder divisions still belongs to `safe`. -/
def a2CoefficientConditions (sa : Rat) (s M0 rm : Expr) : List Expr :=
  let N0 := a2N0 M0
  let nm := a2NuMax N0 rm
  [betaLRecipe s N0 M0 rm nm, sub (rat 1) (CoefficientExprs.ebar N0 rm nm)] ++
    if sa < 0 then [CoefficientExprs.rhoStar N0 rm, CoefficientExprs.betaE N0 rm nm, upperDenominator s N0 M0 rm] else []

def capN (rm : Expr) : Expr := sq (div (rat 6) rm)

/-- Termwise upper bound of the derivative contribution before the cap.
`Nhi` stays explicit, allowing the fixed 576 and general `(6/rm)²` cases. -/
def e2DerivativeBoundOn (rm Nlo Nhi : Expr) : Expr :=
  add
    (add (div (mul (CoefficientExprs.e3 rm) rm) (mul (rat 2) (sqrt Nlo)))
      (mul (CoefficientExprs.e4 Nlo rm) (sq rm)))
    (mul (mul (mul (rat (3 / 2)) (CoefficientExprs.e5 rm)) (powNat rm 3)) (sqrt Nhi))

def e2DerivativeBound (rm Nlo : Expr) : Expr := e2DerivativeBoundOn rm Nlo (capN rm)
def betaDerivativeBound (rm Nlo : Expr) : Expr :=
  sub (rat 1) (mul (div (rat 2) (CoefficientExprs.rhoStar Nlo rm)) (e2DerivativeBound rm Nlo))

def cappedBeta (rm N : Expr) : Expr := CoefficientExprs.betaE N rm (CoefficientExprs.cappedNu N rm)

/-- A3's exact numerical target; this does not claim a derivative theorem. -/
def a3LowerBound : Expr := betaDerivativeBound (rat (1 / 4)) (rat (67 / 5))
def a3Margin : Expr := sub a3LowerBound (rat (93 / 125))

/-- The three A3′ wing starts, kept as exact rationals. -/
def a3WingPairs : List (Rat × Rat) :=
  [(741 / 10000, 651 / 50), (139 / 1250, 13), (1667 / 10000, 388 / 25)]

/-- A3′ central and variant starts retain the exact `t(-0.528)`. -/
def a3EnvelopeStart (mean : Rat) : Expr := add (a2M0 mean (rat (-66 / 125))) (rat 2)

/-- A3′ uses the exact final block start `16Ma+2` for each class cell. -/
def a3FinalBlockStart (Ma : Expr) : Expr := add (mul (rat 16) Ma) (rat 2)

/-- The already-capped C1 side condition is separate from the pre-cap
derivative recipe: `Nlo≥(6/rm)²+9.2`. -/
def a3CappedStartMargin (rm Nlo : Expr) : Expr := sub Nlo (add (capN rm) (rat (46 / 5)))

end Erdos993Lean.Analytic.V22.Compute.EarlyCoefficients
