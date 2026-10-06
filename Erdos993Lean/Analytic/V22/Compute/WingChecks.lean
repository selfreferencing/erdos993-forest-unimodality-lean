import Erdos993Lean.Analytic.V22.Compute.WingExprs
import Erdos993Lean.Analytic.V22.Compute.Grid

/-!
# C1: full eleven-cell wing checker

A candidate piece retains two root brackets and an endpoint-or-tangent
minimum certificate. Every formula is built with the original wing cell,
so refinement changes only the interval for variable `t`, never the frozen
`N0`. Four source conditions and all three algebraic guards are checked.
Every root and arithmetic domain is checked by `Expr.safe`. Each exact
original cell must have a contiguous, complete rational partition.
-/

namespace Erdos993Lean.Analytic.V22.Compute.WingChecks

structure PieceCandidate where
  span : Span
  roots : WingExprs.RootBrackets
  tangent : Option Rat
  deriving Repr

structure CellCertificate where
  classId : Nat
  lo : Rat
  hi : Rat
  pieces : List PieceCandidate
  deriving Repr

def sourceOK (c : V22WingClass) (cell : V22Cell) (p : PieceCandidate) : Bool :=
  let cs := WingExprs.sourceConditions c cell (.var 0) p.roots
  cs.1.positiveOK (spanEnv p.span) &&
  cs.2.1.nonnegativeOK (spanEnv p.span) &&
  cs.2.2.1.positiveOK (spanEnv p.span) &&
  cs.2.2.2.positiveOK (spanEnv p.span)

def algebraOK (c : V22WingClass) (cell : V22Cell) (p : PieceCandidate) : Bool :=
  (WingExprs.A c).positiveOK (spanEnv p.span) &&
  (WingExprs.sqrtSlope c cell (.var 0) p.roots).nonnegativeOK (spanEnv p.span) &&
  (Expr.rat (WingExprs.N0 c cell)).positiveOK (spanEnv p.span)

/-- A tangent point must be one of the source's seven exact multiples.
Both certificate branches prove the whole half-line. -/
def minimumOK (c : V22WingClass) (cell : V22Cell) (p : PieceCandidate) : Bool :=
  match p.tangent with
  | none =>
      (WingExprs.startingSlope c cell (.var 0) p.roots).nonnegativeOK (spanEnv p.span) &&
      (WingExprs.startingValue c cell (.var 0) p.roots).nonnegativeOK (spanEnv p.span)
  | some N1 => decide (N1 ∈ WingExprs.tangentPoints c cell) &&
      (Expr.rat N1).positiveOK (spanEnv p.span) &&
      (WingExprs.tangentBound c cell (.var 0) p.roots N1).nonnegativeOK (spanEnv p.span)

def pieceOK (c : V22WingClass) (cell : V22Cell) (p : PieceCandidate) : Bool :=
  sourceOK c cell p && algebraOK c cell p && minimumOK c cell p

def cellOK (c : V22WingClass) (cell : V22Cell) (pieces : List PieceCandidate) : Bool :=
  partitionFrom cell.lo cell.hi (pieces.map PieceCandidate.span) &&
    pieces.all (pieceOK c cell)

def certificateFor (certificates : List CellCertificate) (cell : V22Cell) :
    Option CellCertificate := certificates.find? fun cert =>
      decide (cert.classId = cell.classId ∧ cert.lo = cell.lo ∧ cert.hi = cell.hi)

def checkedCell (certificates : List CellCertificate) (c : V22WingClass) (cell : V22Cell) : Bool :=
  match certificateFor certificates cell with
  | none => false
  | some cert => cellOK c cell cert.pieces

def classCellOK (certificates : List CellCertificate) (c : V22WingClass) (cell : V22Cell) : Bool :=
  if cell.classId = c.classId then checkedCell certificates c cell else true

/-- All eleven physical cells are checked on their exact canonical ranges. -/
def allOK (certificates : List CellCertificate) : Bool :=
  decide (certificates.length = wingCells.length) &&
  wingClasses.all fun c => wingCells.all (classCellOK certificates c)

def originalCellCount : Nat := wingCells.length
def pieceCount (certificates : List CellCertificate) : Nat :=
  (certificates.map fun c => c.pieces.length).foldl (· + ·) 0

end Erdos993Lean.Analytic.V22.Compute.WingChecks
