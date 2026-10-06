import Erdos993Lean.Analytic.V22.Compute.Grid

/-! Independent exact rational partitions for two-dimensional cells. -/

namespace Erdos993Lean.Analytic.V22.Compute
open Erdos993Lean.Analytic.TailCert.Compute

abbrev Box := Span × Span

def boxEnv (b : Box) (i : Nat) : Ival :=
  if i = 0 then spanI b.1 else if i = 1 then spanI b.2 else ofRat 0

def boxPositiveOn (e : Expr) (xs ys : List Span) : Bool :=
  xs.all fun x => ys.all fun y => e.positiveOK (boxEnv (x,y))

def boxNonnegativeOn (e : Expr) (xs ys : List Span) : Bool :=
  xs.all fun x => ys.all fun y => e.nonnegativeOK (boxEnv (x,y))

def boxUpperOn (e : Expr) (q : Rat) (xs ys : List Span) : Bool :=
  xs.all fun x => ys.all fun y => e.upperOK (boxEnv (x,y)) q

/-- Every subdivision is formed from the exact nominal rational endpoints. -/
def subdivide (start stop : Rat) (n : Nat) : List Span :=
  (List.range n).map fun (i : Nat) =>
    (start+(stop-start)*(i : Rat)/(n : Rat),
     start+(stop-start)*((i+1 : Nat) : Rat)/(n : Rat))

end Erdos993Lean.Analytic.V22.Compute
