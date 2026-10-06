import Erdos993Lean.Analytic.V22.Compute.RayChecks
import Erdos993Lean.Analytic.V22.Compute.GeneratedSpikeWindowData
import Erdos993Lean.Analytic.V22.Compute.GeneratedSpikeCoefficientData

/-! The complete finite checker consumed by both exact versions of 7.14.
Every expression is rebuilt with the actual spike cell and actual class.
The exact-key marked lookup selects candidate data only; no class-record
identity is inferred from it. All marked cells must pass their starting
conditions, including marked cells whose five bounds use the pure ray.
Analytic deficit-to-window-price transport is separate. -/

namespace Erdos993Lean.Analytic.V22.Compute.SpikeBoundsChecks

/-- Domain and export guards on every original cell and every block. -/
def domainOK (c : V22SpikeCell) (i : Nat) : Bool :=
  decide (i < 5 ∧ 0 < c.lo ∧ 8 ≤ GeneratedRayData.m1 c i ∧
    c.logBounds.getD i 0 ≤ c.bounds.getD i 0)

def pureOK (c : V22SpikeCell) (i : Nat) : Bool :=
  RayChecks.checkedBlockOK GeneratedRayData.blocks c i

def coefficientOK (c : V22SpikeCell) (i : Nat) : Bool :=
  SpikeCoefficientChecks.checkedBlockOK GeneratedSpikeCoefficientData.allBlocks c i

def markedKey (c : V22SpikeCell) (d : GeneratedSpikeWindowData.MarkedCell) : Bool :=
  decide (d.cellIndex < spikeCells.length ∧
    (GeneratedSpikeWindowData.spikeCell d.cellIndex).classId = c.classId ∧
    (GeneratedSpikeWindowData.spikeCell d.cellIndex).lo = c.lo ∧
    (GeneratedSpikeWindowData.spikeCell d.cellIndex).hi = c.hi)

def markedFor (c : V22SpikeCell) : Option GeneratedSpikeWindowData.MarkedCell :=
  GeneratedSpikeWindowData.data.find? (markedKey c)

def startOK (c : V22SpikeCell) (k : V22Class) : Bool :=
  match markedFor c with
  | none => false
  | some d => SpikeWindowExprs.startPass k c d.startPieces

def windowOK (c : V22SpikeCell) (k : V22Class) (i : Nat) : Bool :=
  match markedFor c with
  | none => false
  | some d => SpikeWindowExprs.cellPass k c (c.logBounds.getD i 0) d.price

def markedClassOK (c : V22SpikeCell) (k : V22Class) : Bool :=
  startOK c k && (List.range 5).all (fun i => pureOK c i || windowOK c k i)

def cellOK (c : V22SpikeCell) : Bool :=
  (List.range 5).all (domainOK c) && (List.range 5).all (coefficientOK c) &&
  if c.window then
    classes.all (fun k => if k.classId == c.classId then markedClassOK c k else true)
  else (List.range 5).all (pureOK c)

def check : Bool := spikeCells.all cellOK

end Erdos993Lean.Analytic.V22.Compute.SpikeBoundsChecks
