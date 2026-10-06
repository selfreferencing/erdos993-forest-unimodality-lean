import Erdos993Lean.Analytic.V22.Compute.WindowExprs
import Erdos993Lean.Analytic.V22.Compute.Grid
import Erdos993Lean.Analytic.V22.RationalData

/-!
# D1, D1′ and D2 window checkers

Each class activity interval is partitioned into exactly twenty closed pieces
by exact rational interpolation. Every checker validates the complete exact
partition before checking its formulas. Class starts are `muD*tau+2`; marked
spike-cell starts are `muD*lo+2`, with no displayed decimal substituted.

D1 and D2 have eight class groups each. D1′ has eight class-start groups and
seven classes containing marked cells (fifteen reported groups); its second
part checks all fourteen physical marked spike cells. No numeric pass is
claimed in this module.
-/

namespace Erdos993Lean.Analytic.V22.Compute.WindowChecks

def rEdge (c : V22Class) (i : Nat) : Rat :=
  c.ra + (c.rb - c.ra) * (i : Rat) / 20

def rPieces (c : V22Class) : List Span :=
  (List.range 20).map fun i => (rEdge c i, rEdge c (i + 1))

def classStart (c : V22Class) : Rat := c.muD * c.tau + 2
def spikeStart (c : V22Class) (cell : V22SpikeCell) : Rat := c.muD * cell.lo + 2

/-- D1: c1/c2 are strict, while c3 retains its non-strict inequality. -/
def d1AtOK (c : V22Class) (N0 : Rat) : Bool :=
  partitionFrom c.ra c.rb (rPieces c) &&
  positiveOn (WindowExprs.windowCondition1 (.var 0) (.rat N0)) (rPieces c) &&
  positiveOn (WindowExprs.windowCondition2 (.var 0) (.rat N0)) (rPieces c) &&
  nonnegativeOn (WindowExprs.windowCondition3 (.var 0) (.rat N0)) (rPieces c)

def d1ClassOK (c : V22Class) : Bool := d1AtOK c (classStart c)
def d1AllOK : Bool := classes.all d1ClassOK

/-- D1′: c3′ is checked with the source's non-strict inequality. -/
def d1PrimeAtOK (c : V22Class) (N0 : Rat) : Bool :=
  partitionFrom c.ra c.rb (rPieces c) &&
  nonnegativeOn (WindowExprs.c3PrimeMargin (.var 0) (.rat N0)) (rPieces c)

def markedCellFor (c : V22Class) (cell : V22SpikeCell) : Bool :=
  decide (cell.classId = c.classId) && cell.window

def d1PrimeCellOK (c : V22Class) (cell : V22SpikeCell) : Bool :=
  if markedCellFor c cell then d1PrimeAtOK c (spikeStart c cell) else true

def d1PrimeClassOK (c : V22Class) : Bool :=
  d1PrimeAtOK c (classStart c) && spikeCells.all (d1PrimeCellOK c)
def d1PrimeAllOK : Bool := classes.all d1PrimeClassOK

/-- D2 checks the exact pointwise derivative lower bound, strictly positive.
Transport to larger N belongs to the analytic consumer, not this checker. -/
def d2AtOK (c : V22Class) (N0 : Rat) : Bool :=
  partitionFrom c.ra c.rb (rPieces c) &&
  positiveOn (WindowExprs.uMonoDerivative (.var 0) (.rat N0)) (rPieces c)

def d2ClassOK (c : V22Class) : Bool := d2AtOK c (classStart c)
def d2AllOK : Bool := classes.all d2ClassOK

/-- Group and physical-cell counts are distinct diagnostic quantities. -/
def d1GroupCount : Nat := classes.length
def d1PrimeGroupCount : Nat := classes.length +
  (classes.filter fun c => spikeCells.any (markedCellFor c)).length
def d1PrimePhysicalCellCount : Nat := (spikeCells.filter fun cell => cell.window).length
def d2GroupCount : Nat := classes.length

end Erdos993Lean.Analytic.V22.Compute.WindowChecks
