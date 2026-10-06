import Erdos993Lean.Analytic.V22.Compute.CoefficientExprs
import Erdos993Lean.Analytic.V22.RationalData

/-!
# B2: exact lower-spike endpoint recipes

Source: note Lemma 7.13; supplementary_code/fc_check_B.py `check_B2`
and fc_check_D.py's per-class B2 loop. There are nine source groups:
one central endpoint and eight classes containing 26 physical endpoints.
Every class endpoint uses its original `ta`, `tb`, and
`N0 = max(10, muD * ta + 2)`. Subdivision never replaces these values.
B2 contains square roots and coefficient bounds, but no root-map node.
Candidate data may be generated separately; the certificate checks exact
agreement with the complete canonical list before checking its margins.
-/

namespace Erdos993Lean.Analytic.V22.Compute.SpikeLowerChecks

open Erdos993Lean.Analytic.TailCert.Compute Expr

structure Candidate where
  classId : Nat
  ta : Rat
  tb : Rat
  rm : Rat
  mean : Rat
  deriving DecidableEq, BEq

def start (c : Candidate) : Rat := max 10 (c.mean * c.ta + 2)

def slack (rm t N : Expr) : Expr :=
  let nm := mul rm (sqrt N)
  sub (mul (rat (9/2)) (sq (sub (rat 1) t)))
    (div (mul (mul (rat 2) t)
      (add (mul (CoefficientExprs.alpha1 N rm) nm)
        (mul (CoefficientExprs.alpha2 N rm) (sq nm)))) (sub N (rat 2)))

def endpoint (c : Candidate) : Expr := slack (rat c.rm) (rat c.tb) (rat (start c))

def closedEnv : Nat → Ival := fun _ => ofRat 0
def positive (e : Expr) : Bool := e.positiveOK closedEnv
def nonnegative (e : Expr) : Bool := e.nonnegativeOK closedEnv
def upper (e : Expr) (q : Rat) : Bool := e.upperOK closedEnv q

/-- These guards are retained for the all-size, whole-cell consumer. -/
def domainOK (c : Candidate) : Bool :=
  nonnegative (rat c.rm) && upper (rat c.rm) (1/2) &&
  nonnegative (rat c.ta) && nonnegative (sub (rat c.tb) (rat c.ta)) &&
  upper (rat c.tb) 1 && nonnegative (sub (rat (start c)) (rat 10))

def candidateOK (c : Candidate) : Bool := domainOK c && positive (endpoint c)

def central : Candidate := ⟨0, 0, 3/5, 1/4, 19⟩

def rmRat (cell : V22SpikeCell) : Rat :=
  match classes.find? (fun c => c.classId == cell.classId) with
  | some c => c.rb
  | none => 1/4

def meanRat (cell : V22SpikeCell) : Rat :=
  match classes.find? (fun c => c.classId == cell.classId) with
  | some c => c.muD
  | none => 19

def ofCell (cell : V22SpikeCell) : Candidate :=
  ⟨cell.classId, cell.lo, cell.hi, rmRat cell, meanRat cell⟩

def outerOK (cell : V22SpikeCell) : Bool :=
  if cell.classId = 0 then true else candidateOK (ofCell cell)

def b2OK : Bool := candidateOK central && spikeCells.all outerOK

def requiredCandidates : List Candidate := central ::
  (spikeCells.filter fun c => decide (c.classId ≠ 0)).map ofCell

/-- A supplied candidate export must retain every exact canonical endpoint. -/
def certificateOK (candidates : List Candidate) : Bool :=
  decide (candidates = requiredCandidates) && candidates.all candidateOK

def groupCount : Nat := 1 + classes.length
def outerEndpointCount : Nat :=
  (spikeCells.filter fun c => decide (c.classId ≠ 0)).length
def endpointCount : Nat := 1 + outerEndpointCount

end Erdos993Lean.Analytic.V22.Compute.SpikeLowerChecks
