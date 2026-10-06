import Erdos993Lean.Analytic.V22.Compute.Grid
import Erdos993Lean.Analytic.V22.Compute.WindowCellExprs

/-! Exact two-dimensional certificates for the 54 source window cells.
Refinement never changes the original cell's `N0`, `Dlo` or outer endpoints.
This is a pure checker: real semantics and soundness are in a separate module.
-/

namespace Erdos993Lean.Analytic.V22.Compute.WindowCellChecks

open Erdos993Lean.Analytic.TailCert.Compute WindowCellExprs

inductive TargetMode where
  | positive | negative | crossing
  deriving Repr

structure Box where
  rSpan : Span
  roots : RootBrackets
  licensed : Bool
  deriving Repr

structure Row where
  tSpan : Span
  boxes : List Box
  deriving Repr

structure CellCertificate where
  mode : TargetMode
  rows : List Row
  deriving Repr

def boxEnv (ts rs : Span) (i : Nat) : Ival :=
  if i = 0 then spanI ts else if i = 1 then spanI rs else ofRat 0

def recipe (c : V22Class) (cell : V22Cell) (box : Box) : Expr :=
  if box.licensed then classLicensedRecipe c cell (.var 0) (.var 1) box.roots
  else classLowerRecipe c cell (.var 0) (.var 1) box.roots

def margin (c : V22Class) (cell : V22Cell) (box : Box) (req : Expr) : Expr :=
  .sub (recipe c cell box) req

def rootsPasses (c : V22Class) (cell : V22Cell) (box : Box) (env : Nat → Ival) : Bool :=
  let N0 := cellStart c cell
  let br := box.roots
  (Expr.root br.g0Lo br.g0Hi (WindowExprs.lambdaT (.var 0))).safe env &&
    (Expr.root br.shiftedLo br.shiftedHi (.add (WindowExprs.lambdaT (.var 0))
      (EarlyCoefficients.hbar (.sub (.rat N0) (.rat 2))))).safe env &&
    (Expr.root br.sbarLo br.sbarHi (qShift N0 (.var 0) (.var 1))).safe env &&
    (Expr.root br.upperLo br.upperHi (.minimum (.rat 0) (upperLambda N0 (.var 0) (.var 1)))).safe env

def boxPasses (c : V22Class) (cell : V22Cell) (mode : TargetMode) (ts : Span) (box : Box) : Bool :=
  let env := boxEnv ts box.rSpan
  let pos := positiveRequirement c.b c.beta (.var 0)
  let neg := negativeRequirement (cellStart c cell) c.b c.beta (.var 0)
  let cross := crossingRequirement c.b c.beta (.var 0)
  rootsPasses c cell box env &&
    (if box.licensed then (classConditionMargin c cell (.var 0) (.var 1)).nonnegativeOK env else true) &&
    match mode with
    | .positive => (margin c cell box pos).nonnegativeOK env
    | .negative => (margin c cell box neg).nonnegativeOK env
    | .crossing => (margin c cell box pos).nonnegativeOK env &&
        (margin c cell box neg).nonnegativeOK env && (margin c cell box cross).nonnegativeOK env

/-- Uniform sign guards rule out crossing on the original cell. Crossing
certificates instead check all three original requirements on every box. -/
def signPasses (c : V22Class) (mode : TargetMode) (ts : Span) : Bool :=
  match mode with
  | .positive => (target c.b c.beta (.var 0)).positiveOK (spanEnv ts)
  | .negative => (Expr.neg (target c.b c.beta (.var 0))).nonnegativeOK (spanEnv ts)
  | .crossing => true

def rowPasses (c : V22Class) (cell : V22Cell) (mode : TargetMode) (row : Row) : Bool :=
  partitionFrom c.ra c.rb (row.boxes.map Box.rSpan) && signPasses c mode row.tSpan &&
    row.boxes.all (boxPasses c cell mode row.tSpan)

def cellPasses (c : V22Class) (cell : V22Cell) (cert : CellCertificate) : Bool :=
  partitionFrom cell.lo cell.hi (cert.rows.map Row.tSpan) &&
    cert.rows.all (rowPasses c cell cert.mode)

def check (data : V22Cell → CellCertificate) : Bool :=
  decide (windowCells.length = 54) && classes.all fun c => windowCells.all fun cell =>
    if cell.classId = c.classId then cellPasses c cell (data cell) else true

end Erdos993Lean.Analytic.V22.Compute.WindowCellChecks
