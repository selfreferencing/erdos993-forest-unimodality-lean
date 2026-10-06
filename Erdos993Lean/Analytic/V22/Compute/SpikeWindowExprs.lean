import Erdos993Lean.Analytic.V22.Compute.WindowCellChecks
import Erdos993Lean.Analytic.V22.Compute.WindowChecks

/-!
# Window prices for the fourteen marked spike cells

The source's `pw` uses the original cell start `N0=muD*lo+2` and
`Bmax=hi*N0/(N0-2)`. Refinement changes only the t/r boxes. This module
checks an unconditional upper bound for the explicit window-price recipe;
the analytic inequality from the actual fiber deficit is separate.
-/

namespace Erdos993Lean.Analytic.V22.Compute.SpikeWindowExprs

open Expr
open Erdos993Lean.Analytic.TailCert.Compute

def asWindowCell (cell : V22SpikeCell) : V22Cell := ⟨cell.classId, cell.lo, cell.hi⟩
def cellStart (c : V22Class) (cell : V22SpikeCell) : Rat := c.muD * cell.lo + 2
def bMax (c : V22Class) (cell : V22SpikeCell) : Rat :=
  cell.hi * cellStart c cell / (cellStart c cell - 2)

/-- The retained conservative lower recipe, optionally licensed by its
separate exact condition margin. -/
def lower (c : V22Class) (cell : V22SpikeCell) (box : WindowCellChecks.Box) : Expr :=
  WindowCellChecks.recipe c (asWindowCell cell) box

def pw (c : V22Class) (cell : V22SpikeCell) (box : WindowCellChecks.Box) : Expr :=
  EarlyCoefficients.positivePart
    (add (WindowCellExprs.target c.b c.beta (var 0))
      (mul (rat (bMax c cell)) (EarlyCoefficients.positivePart (neg (lower c cell box)))))

def pwMargin (c : V22Class) (cell : V22SpikeCell) (bound : Rat)
    (box : WindowCellChecks.Box) : Expr := sub (rat bound) (pw c cell box)

def boxPass (c : V22Class) (cell : V22SpikeCell) (bound : Rat)
    (ts : Span) (box : WindowCellChecks.Box) : Bool :=
  let env := WindowCellChecks.boxEnv ts box.rSpan
  (if box.licensed then
    (WindowCellExprs.classConditionMargin c (asWindowCell cell) (var 0) (var 1)).nonnegativeOK env
   else true) &&
  (rat (bMax c cell)).nonnegativeOK env && (pwMargin c cell bound box).nonnegativeOK env

structure Certificate where
  rows : List WindowCellChecks.Row
  deriving Repr

def rowPass (c : V22Class) (cell : V22SpikeCell) (bound : Rat)
    (row : WindowCellChecks.Row) : Bool :=
  partitionFrom c.ra c.rb (row.boxes.map (·.rSpan)) &&
    row.boxes.all (boxPass c cell bound row.tSpan)

def cellPass (c : V22Class) (cell : V22SpikeCell) (bound : Rat) (cert : Certificate) : Bool :=
  partitionFrom cell.lo cell.hi (cert.rows.map (·.tSpan)) && cert.rows.all (rowPass c cell bound)

/-- Both the original and persistent shape conditions are retained, along
with strict derivative positivity, at the original marked-cell start. -/
def startPass (c : V22Class) (cell : V22SpikeCell) (pieces : List Span) : Bool :=
  let N := rat (cellStart c cell)
  partitionFrom c.ra c.rb pieces &&
  positiveOn (WindowExprs.windowCondition1 (var 0) N) pieces &&
  positiveOn (WindowExprs.windowCondition2 (var 0) N) pieces &&
  nonnegativeOn (WindowExprs.windowCondition3 (var 0) N) pieces &&
  nonnegativeOn (WindowExprs.c3PrimeMargin (var 0) N) pieces &&
  positiveOn (WindowExprs.uMonoDerivative (var 0) N) pieces

end Erdos993Lean.Analytic.V22.Compute.SpikeWindowExprs
