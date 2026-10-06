import Erdos993Lean.Analytic.V22.Compute.GeneratedRayData

/-! Bound-independent exact coefficient checks for all original spike blocks.
The checker uses the actual supplied cell for every coefficient and retains
an exact contiguous t partition. It asserts no Phi upper bound, fiber
infimum bound, or infinite-block betaE monotonicity. -/

namespace Erdos993Lean.Analytic.V22.Compute.SpikeCoefficientChecks

open GeneratedRayData

structure CoefficientPiece where
  tSpan : Span
  brackets : RayExprs.RootBrackets
  deriving Repr

structure CoefficientBlock where
  cellIndex : Nat
  blockIndex : Nat
  pieces : List CoefficientPiece
  deriving Repr

def keyOK (c : V22SpikeCell) (i : Nat) (b : CoefficientBlock) : Bool :=
  decide (b.cellIndex < spikeCells.length ∧ b.blockIndex = i ∧
    (cell b.cellIndex).classId = c.classId ∧ (cell b.cellIndex).lo = c.lo ∧
    (cell b.cellIndex).hi = c.hi)

def domainOK (c : V22SpikeCell) (i : Nat) : Bool :=
  decide (i < 5 ∧ 0 ≤ c.lo ∧ 8 ≤ m1 c i)

/-- The finite predicate is the retained rhoStarBlock positivity. The
infinite predicate keeps all three AM-GM denominator positivity guards. -/
def pieceOK (c : V22SpikeCell) (i : Nat) (p : CoefficientPiece) : Bool :=
  let env := spanEnv p.tSpan
  if i = 4 then RayExprs.infiniteGuard p.brackets env (.var 0) (m1 c i) (rm c)
  else (RayExprs.rhoStarBlock (RayExprs.blockN (m1 c i))
    (RayExprs.phiBlockNuMax (2 * m1 c i) (rm c)) (.rat (rm c))).positiveOK env

def blockOK (c : V22SpikeCell) (i : Nat) (b : CoefficientBlock) : Bool :=
  keyOK c i b && domainOK c i && partitionFrom c.lo c.hi (b.pieces.map (·.tSpan)) &&
    b.pieces.all (pieceOK c i)

def blockFor (blocks : List CoefficientBlock) (c : V22SpikeCell) (i : Nat) :
    Option CoefficientBlock := blocks.find? (keyOK c i)

def checkedBlockOK (blocks : List CoefficientBlock) (c : V22SpikeCell) (i : Nat) : Bool :=
  match blockFor blocks c i with
  | none => false
  | some b => blockOK c i b

def allOK (blocks : List CoefficientBlock) : Bool :=
  spikeCells.all fun c => (List.range 5).all (checkedBlockOK blocks c)

end Erdos993Lean.Analytic.V22.Compute.SpikeCoefficientChecks
