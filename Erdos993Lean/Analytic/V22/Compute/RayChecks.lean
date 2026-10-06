import Erdos993Lean.Analytic.V22.Compute.GeneratedRayData

/-!
# Exact-key ray-block coverage checkers

The lookup key retains class identity, both exact nominal cell endpoints,
and the actual block index. Numeric expressions and partition endpoints
are rebuilt using the supplied actual cell, so no equality instance on
whole class records is needed. All original coefficients and six-digit
exports remain visible. A nonwindow checker must pass every one of its
five blocks; status-zero window blocks can also supply a pure-Phi bound.
-/

namespace Erdos993Lean.Analytic.V22.Compute.RayChecks

open GeneratedRayData

def keyOK (c : V22SpikeCell) (i : Nat) (b : RayBlock) : Bool :=
  decide (b.cellIndex < spikeCells.length ∧ b.blockIndex = i ∧ b.status = 0 ∧
    (cell b.cellIndex).classId = c.classId ∧ (cell b.cellIndex).lo = c.lo ∧
    (cell b.cellIndex).hi = c.hi)

def domainOK (c : V22SpikeCell) (i : Nat) : Bool :=
  decide (i < 5 ∧ 0 ≤ c.lo ∧ 8 ≤ m1 c i ∧
    c.logBounds.getD i 0 ≤ c.bounds.getD i 0)

/-- The actual cell and index supply every coefficient and bound. -/
def blockOK (c : V22SpikeCell) (i : Nat) (b : RayBlock) : Bool :=
  keyOK c i b && domainOK c i &&
  partitionFrom c.lo c.hi (b.pieces.map (·.tspan)) &&
  b.pieces.all (piecePass c i)

def blockFor (blocks : List RayBlock) (c : V22SpikeCell) (i : Nat) : Option RayBlock :=
  blocks.find? (keyOK c i)

def checkedBlockOK (blocks : List RayBlock) (c : V22SpikeCell) (i : Nat) : Bool :=
  match blockFor blocks c i with
  | none => false
  | some b => blockOK c i b

def nonwindowAllOK (blocks : List RayBlock) : Bool :=
  spikeCells.all fun c => if c.window then true else
    (List.range 5).all (checkedBlockOK blocks c)

/-- Interface for a separately generated complete cell/index selector. -/
def suppliedNonwindowOK (select : V22SpikeCell → Nat → RayBlock) : Bool :=
  spikeCells.all fun c => if c.window then true else
    (List.range 5).all fun i => blockOK c i (select c i)

def generatedNonwindowOK : Bool := nonwindowAllOK GeneratedRayData.blocks

end Erdos993Lean.Analytic.V22.Compute.RayChecks
