import Erdos993Lean.Analytic.V22.Compute.EarlyCoefficients
import Erdos993Lean.Analytic.V22.Compute.Grid

/-! A2 checker interface with exact nominal endpoints and a separately
supplied rational partition. No numerical pass is asserted here. -/

namespace Erdos993Lean.Analytic.V22.Compute.A2Checks
open Expr EarlyCoefficients

def envelopeCells : List (Rat × Rat) :=
  [(-66/125,-373/1000),(-373/1000,-13/125),(-13/125,0),
   (0,31/200),(31/200,47/200),(47/200,317/1000),
   (317/1000,53/125),(53/125,117/200),(117/200,67/100)]


def cellPasses (c : Span) (pieces : List Span) : Bool :=
  let s := Expr.var 0
  let M0 := a2M0 19 (rat c.1)
  let N0 := a2N0 M0
  let endpoints := a2EndpointRecipes c.1 s M0 (rat (1/4))
  decide ((-1:Rat) < c.1 ∧ c.1 ≤ c.2 ∧ (0 ≤ c.1 ∨ c.2 ≤ 0)) &&
    partitionFrom c.1 c.2 pieces && positiveOn M0 pieces &&
    nonnegativeOn (sub N0 (rat 10)) pieces &&
    (a2CoefficientConditions c.1 s M0 (rat (1/4))).all (fun e => positiveOn e pieces) &&
    nonnegativeOn endpoints.1 pieces && nonnegativeOn endpoints.2 pieces

def check (parts : Span → List Span) : Bool :=
  envelopeCells.all (fun c => cellPasses c (parts c))

end Erdos993Lean.Analytic.V22.Compute.A2Checks
