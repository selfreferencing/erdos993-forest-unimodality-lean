import Erdos993Lean.Analytic.V22.Compute.EarlyCoefficients
import Erdos993Lean.Analytic.V22.RationalData

/-!
# Endpoint checkers for A3, A3′, A4 and A4′

The numerical checks retain every domain and positivity premise needed by
the analytic transports. A beta range may use a positive derivative bound
or a separately checked already-capped start. No derivative or monotonicity
target is used as numerical input. Physical duplicate class-cell starts are
checked individually: A3′ has 31 starts in 13 source groups (3 wings, 2
envelope starts, and 26 outer cells grouped by their 8 classes).
-/

namespace Erdos993Lean.Analytic.V22.Compute.CoefficientChecks

open Erdos993Lean.Analytic.TailCert.Compute Expr

def closedEnv : Nat → Ival := fun _ => ofRat 0
def closedPositive (e : Expr) : Bool := e.positiveOK closedEnv
def closedNonnegative (e : Expr) : Bool := e.nonnegativeOK closedEnv
def closedUpper (e : Expr) (q : Rat) : Bool := e.upperOK closedEnv q
def allClosedPositive (es : List Expr) : Bool := es.all closedPositive

def betaGuards (rm : Rat) (Nlo : Expr) : List Expr :=
  [.rat rm, .sub Nlo (.rat 1), CoefficientExprs.rhoStar Nlo (.rat rm)]
def betaGuardsOK (rm : Rat) (Nlo : Expr) : Bool :=
  allClosedPositive (betaGuards rm Nlo) && closedUpper (.rat rm) (1/2)

def betaRangeOK (rm : Rat) (Nlo : Expr) : Bool :=
  betaGuardsOK rm Nlo &&
    (closedPositive (EarlyCoefficients.betaDerivativeBound (.rat rm) Nlo) ||
      closedNonnegative (.sub Nlo (EarlyCoefficients.capN (.rat rm))))

def a3OK : Bool := betaGuardsOK (1/4) (.rat (67/5)) &&
  closedNonnegative EarlyCoefficients.a3Margin

def spikeRmRat (cell : V22SpikeCell) : Rat :=
  match classes.find? (fun c => c.classId == cell.classId) with
  | some c => c.rb
  | none => 1/4

def outerStart (cell : V22SpikeCell) : Expr :=
  EarlyCoefficients.a3FinalBlockStart (.rat cell.ma)

def outerBetaOK (cell : V22SpikeCell) : Bool :=
  if cell.classId = 0 then true else
    betaRangeOK (spikeRmRat cell) (outerStart cell) &&
      (if cell.classId = 1 then decide
        ((6 / spikeRmRat cell)^2 + 46/5 ≤ 16*cell.ma + 2) else true)

def a3PrimeOK : Bool :=
  (EarlyCoefficients.a3WingPairs.all fun p => betaRangeOK p.1 (.rat p.2)) &&
  betaRangeOK (1/4) (EarlyCoefficients.a3EnvelopeStart 19) &&
  betaRangeOK (7/25) (EarlyCoefficients.a3EnvelopeStart 30) &&
  spikeCells.all outerBetaOK

/-- The exact fixed-coefficient quadratic tail, with the cap frozen. -/
def bonusTail (rm N : Expr) : Expr :=
  let Nc := EarlyCoefficients.capN rm
  .sub
    (.sub (.div (.mul (.mul N (.sub N (.rat 1))) (CoefficientExprs.rhoStar Nc rm)) (.rat 2))
      (.mul N (CoefficientExprs.E2 Nc rm (.rat 6))))
    (.div (.add N (.rat 1)) (.rat (71/20)))

def bonusTailDerivative (rm N : Expr) : Expr :=
  let Nc := EarlyCoefficients.capN rm
  .sub (.sub (.mul (CoefficientExprs.rhoStar Nc rm) (.sub N (.rat (1/2))))
    (CoefficientExprs.E2 Nc rm (.rat 6))) (.div (.rat 1) (.rat (71/20)))

def bonusPreMargin (rm : Rat) (Nlo : Expr) : Expr :=
  .sub (.div (CoefficientExprs.rhoStar Nlo (.rat rm)) (.rat 2))
    (EarlyCoefficients.e2DerivativeBound (.rat rm) Nlo)

def bonusEndpointExprs (rm : Rat) (Nlo : Expr) : List Expr :=
  let r := .rat rm
  let Nc := EarlyCoefficients.capN r
  [.rat rm, .sub Nlo (.rat 1), CoefficientExprs.rhoStar Nlo r,
    .sub Nc Nlo, CoefficientExprs.lambdaBonusF Nlo r, bonusPreMargin rm Nlo,
    bonusTail r Nc, bonusTailDerivative r Nc]

def bonusEndpointsOK (rm : Rat) (Nlo : Expr) : Bool :=
  allClosedPositive (bonusEndpointExprs rm Nlo) && closedUpper (.rat rm) (1/2)

def a4OK : Bool := bonusEndpointsOK (1/4) (.rat (67/5))
def a4Pairs : List (Rat × Rat) :=
  [(1/4,10),(7/25,10),(194/625,10),(861/2500,10),(3847/10000,12),(2/5,12)]
def a4PrimeOK : Bool := a4Pairs.all fun p => bonusEndpointsOK p.1 (.rat p.2)

def a3GroupCount : Nat := 1
def a3PrimeGroupCount : Nat := EarlyCoefficients.a3WingPairs.length + 2 + classes.length
def a3PrimePhysicalStartCount : Nat := EarlyCoefficients.a3WingPairs.length + 2 +
  (spikeCells.filter fun c => decide (c.classId ≠ 0)).length
def a4GroupCount : Nat := 3
def a4PrimeGroupCount : Nat := a4Pairs.length

end Erdos993Lean.Analytic.V22.Compute.CoefficientChecks
