import Erdos993Lean.Analytic.V22.Compute.Expr

/-! Exact rational partitions for lane D. All nominal endpoints are retained,
and outward rounding is applied only when constructing interval enclosures. -/

namespace Erdos993Lean.Analytic.V22.Compute
open Erdos993Lean.Analytic.TailCert.Compute

abbrev Span := Rat × Rat

/-- A contiguous closed partition with the exact prescribed outer endpoints. -/
def partitionFrom (start stop : Rat) : List Span → Bool
  | [] => false
  | [s] => decide (s.1 = start ∧ s.1 ≤ s.2) && decide (s.2 = stop)
  | s :: t :: rest => decide (s.1 = start ∧ s.1 ≤ s.2) &&
      partitionFrom s.2 stop (t :: rest)

def spanI (s : Span) : Ival := ⟨(ofRat s.1).lo, (ofRat s.2).hi⟩

/-- Variable zero ranges over the span; all other variables are exactly zero. -/
def spanEnv (s : Span) (i : Nat) : Ival := if i = 0 then spanI s else ofRat 0

def spanRealEnv (x : Rat) (i : Nat) : Rat := if i = 0 then x else 0

def positiveOn (e : Expr) (pieces : List Span) : Bool :=
  pieces.all fun s => e.positiveOK (spanEnv s)

def nonnegativeOn (e : Expr) (pieces : List Span) : Bool :=
  pieces.all fun s => e.nonnegativeOK (spanEnv s)

def upperOn (e : Expr) (q : Rat) (pieces : List Span) : Bool :=
  pieces.all fun s => e.upperOK (spanEnv s) q

end Erdos993Lean.Analytic.V22.Compute
