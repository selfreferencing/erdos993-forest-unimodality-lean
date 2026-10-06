import Erdos993Lean.Analytic.HandVariance.Compute.Source
import Erdos993Lean.Analytic.HandVariance.Compute.Checks

/-!
# Finite geometry and recipe coverage guards for Appendix N.4

The numerical rows are not a covering proof by themselves. These additional
Boolean guards retain the exact supplied vertices, the supporting line of
every edge, each per-spatial cut, and the contiguous Taylor and tail recipes.
They contain only rational arithmetic, finite lists and guarded expressions.
-/

namespace Erdos993Lean.Analytic.HandVariance.Compute

open Erdos993Lean.Analytic.TailCert.Compute

def spanPair (s : Span) : Rat × Rat := (s.lo, s.hi)
def polygonLineRat (line : Rat × Rat) (r : Rat) : Rat := line.1 + line.2 * r

def polygonURat : List (Rat × Rat) → Rat → Rat → Rat
  | [], cap, _ => cap
  | line :: lines, cap, r => min (polygonLineRat line r) (polygonURat lines cap r)

/-- Closed pieces must occur in their actual order and meet exactly.
The last piece ends at the requested endpoint; gaps and empty lists fail. -/
def partitionFrom (start stop : Rat) : List (Rat × Rat) → Bool
  | [] => false
  | piece :: rest => decide (piece.1 = start ∧ piece.1 ≤ piece.2) &&
      match rest with
      | [] => decide (piece.2 = stop)
      | _ :: _ => partitionFrom piece.2 stop rest

/-- Finite endpoint geometry for the exact raw source vertex list. -/
def polygonGeometryCheck (lines : List (Rat × Rat)) (cap : Rat)
    (vertices : List (Rat × Rat)) : Bool :=
  decide (0 < vertices.length) &&
  decide ((vertices.getD 0 (0,0)).1 = 0) &&
  vertices.all (fun v => decide (0 ≤ v.2 ∧ v.2 = polygonURat lines cap v.1)) &&
  (List.range (vertices.length - 1)).all (fun i =>
    let v := vertices.getD i (0,0)
    let w := vertices.getD (i+1) (0,0)
    decide (v.1 < w.1) && lines.any (fun line =>
      decide (v.2 = polygonLineRat line v.1 ∧ w.2 = polygonLineRat line w.1))) &&
  decide ((vertices.getD (vertices.length-1) (0,0)).2 = cap) &&
  lines.all (fun line => decide (0 ≤ line.2)) &&
  decide ((cap,0) ∈ lines)

/-- Taylor rows for one retained upper line, preserving their source order. -/
def polygonPieces (p : Polygon) (line : Rat × Rat) : List (Rat × Rat) :=
  (p.checks.filter (fun c => decide
    (c.activity = p.activity ∧ c.intercept = line.1 ∧ c.slope = line.2))).map
      (fun c => spanPair c.spatial)

/-- Adjacent tail rows retain finite endpoints and the final infinity tag. -/
def chainCoverageCheck (activity start : Rat) (chain : List ChainCheck) : Bool :=
  decide (0 < chain.length) &&
  decide ((chain.getD 0 ⟨0,0,none⟩).left = start) &&
  chain.all (fun c => decide (c.activity = activity ∧ 0 < c.left)) &&
  (List.range (chain.length-1)).all (fun i =>
    let c := chain.getD i ⟨0,0,none⟩
    let d := chain.getD (i+1) ⟨0,0,none⟩
    decide (c.right = some d.left ∧ c.left < d.left)) &&
  decide ((chain.getD (chain.length-1) ⟨0,0,none⟩).right = none)

/-- All finite Taylor pieces and the complete infinite tail must be present.
Every checked row belongs to a retained line at the actual polygon activity. -/
def polygonCoverageCheck (p : Polygon) : Bool :=
  decide (0 < p.activity ∧ p.activity ≤ 5/2 ∧ 0 < p.tailStart) &&
  p.lines.all (fun line => decide (0 ≤ line.2)) &&
  p.checks.all (fun c => decide
    (c.activity = p.activity ∧ (c.intercept,c.slope) ∈ p.lines ∧
      0 ≤ c.spatial.lo ∧ c.spatial.lo ≤ c.spatial.hi ∧ c.spatial.hi ≤ p.tailStart)) &&
  p.lines.all (fun line => partitionFrom 0 p.tailStart (polygonPieces p line)) &&
  chainCoverageCheck p.activity p.tailStart p.chain

/-- Exact source rows at a fixed vertex and denominator tag. -/
def vertexPieces (a : Activity) (v : Rat × Rat) (tag : Bool) : List (Rat × Rat) :=
  (a.vertexChecks.filter (fun c => decide
    (c.r = v.1 ∧ c.J = v.2 ∧ c.useGamma = tag))).map (fun c => spanPair c.spatial)

def spatialGroups (a : Activity) : List (Rat × Rat) :=
  (a.vertexChecks.map (fun c => spanPair c.spatial)).eraseDups

def spatialRows (a : Activity) (s : Rat × Rat) : List VertexCheck :=
  a.vertexChecks.filter (fun c => decide (spanPair c.spatial = s))

/-- The minimum retained coordinate is the source cut (including cut=0). -/
def groupCut (rows : List VertexCheck) : Option Rat :=
  match rows with
  | [] => none
  | c :: rest => some (rest.foldl (fun r d => min r d.r) c.r)

/-- The genuine feasibility cut, evaluated with every exp/log guard. -/
def cutExpr (activityLo spatialHi : Rat) : Expr :=
  .div (.maximum (.rat 0) (.sub (.log (.rat activityLo))
    (.log (.sub (.exp (.rat spatialHi)) (.rat 1))))) (.rat spatialHi)

/-- A rational lower bound is accepted only below the enclosed actual cut. -/
def cutSafe (activityLo spatialHi rmin : Rat) : Bool :=
  match evalClosed (cutExpr activityLo spatialHi) with
  | none => false
  | some v => decide (rmin ≤ loRat v)

def rowAt (rows : List VertexCheck) (v : Rat × Rat) (tag : Bool) : Bool :=
  rows.any (fun c => decide (c.r = v.1 ∧ c.J = v.2 ∧ c.useGamma = tag))

/-- One spatial cut group retains both actual cut functions and all surviving
source vertices. No rows are replaced by a reported scalar minimum. -/
def cutGroupCheck (a : Activity) (p : Polygon) (s : Rat × Rat) : Bool :=
  let rows := spatialRows a s
  match groupCut rows with
  | none => false
  | some rmin =>
    let cut := (rmin, polygonURat p.lines a.Jcap rmin)
    decide (0 ≤ rmin) && cutSafe a.activity.lo s.2 rmin &&
    rowAt rows cut false && rowAt rows cut true &&
    a.vertices.all (fun v => decide (v.1 < rmin) ||
      (rowAt rows v false && rowAt rows v true)) &&
    rows.all (fun c => decide
      ((c.r,c.J) = cut ∨ ((c.r,c.J) ∈ a.vertices ∧ rmin ≤ c.r)))

/-- Geometry, spatial groups, vertex tags and CA recipes for one activity
row. The center and activity endpoints are kept exactly as supplied. -/
def activityCoverageCheck (a : Activity) (p : Polygon) : Bool :=
  decide (a.segment ≤ 5 ∧ 0 < a.activity.lo ∧
    a.activity.lo ≤ a.center ∧ a.center ≤ a.activity.hi ∧
    a.center = (a.activity.lo+a.activity.hi)/2 ∧
    a.activity.hi ≤ a.polygonActivity ∧ a.polygonActivity ≤ 5/2 ∧
    p.activity = a.polygonActivity ∧ 0 < a.leftEnd ∧ a.leftEnd ≤ 3 ∧
    0 < loRat (point a.activity.hi 0).k ∧
    0 < loRat (point a.activity.hi 3).k ∧
    capARat (parameters a.segment) a.activity.lo - 1 -
      gammaRat (parameters a.segment) a.activity.hi -
      alphaRat (parameters a.segment) a.activity.hi / hiRat (point a.activity.hi 3).k < 0) &&
  polygonGeometryCheck p.lines a.Jcap a.vertices &&
  a.vertexChecks.all (fun c => decide
    (a.leftEnd ≤ c.spatial.lo ∧ c.spatial.lo ≤ c.spatial.hi ∧ c.spatial.hi ≤ 3 ∧
      0 ≤ c.r ∧ 0 ≤ c.J ∧ c.J ≤ a.Jcap)) &&
  (if a.useCut then
    partitionFrom a.leftEnd 3 (spatialGroups a) &&
    (spatialGroups a).all (cutGroupCheck a p)
  else
    a.vertices.all (fun v => partitionFrom a.leftEnd 3 (vertexPieces a v false) &&
      partitionFrom a.leftEnd 3 (vertexPieces a v true)) &&
    a.vertexChecks.all (fun c => decide ((c.r,c.J) ∈ a.vertices))) &&
  a.caChecks.all (fun c => decide
    (1/500 ≤ c.spatial.lo ∧ c.spatial.lo ≤ c.spatial.hi ∧ c.spatial.hi ≤ 3)) &&
  partitionFrom (1/500) 3 (a.caChecks.map (fun c => spanPair c.spatial))

/-- The six actual activity segments retain every shared closed endpoint. -/
def segmentSpan : Nat → Rat × Rat
  | 0 => (1/3,11/20)
  | 1 => (11/20,263/200)
  | 2 => (263/200,3/2)
  | 3 => (3/2,7/4)
  | 4 => (7/4,2)
  | _ => (2,7/3)

/-- Activity coverage keeps segment identity as well as adjacent endpoints. -/
def segmentCoverageCheck (segment : Nat) (rows : List Activity) : Bool :=
  decide (segment ≤ 5) && rows.all (fun a => decide (a.segment = segment)) &&
  partitionFrom (segmentSpan segment).1 (segmentSpan segment).2
    (rows.map (fun a => spanPair a.activity))

/-- Retain an actual polygon recipe witnessing each activity row's geometry. -/
def activityCoverageIn (polygons : List Polygon) (a : Activity) : Bool :=
  polygons.any (activityCoverageCheck a)

/-- One named segment and all of its retained polygon witnesses. -/
def segmentActivityCoverageCheck (segment : Nat) (rows : List Activity)
    (polygons : List Polygon) : Bool :=
  segmentCoverageCheck segment rows && rows.all (activityCoverageIn polygons)

/-- The selected-leaf base recipes cover the same exact named activity span. -/
def baseCoverageCheck (segment : Nat) (rows : List BaseCheck) : Bool :=
  decide (segment ≤ 5) && rows.all (fun b => decide (b.segment = segment)) &&
  partitionFrom (segmentSpan segment).1 (segmentSpan segment).2
    (rows.map (fun b => spanPair b.activity))

end Erdos993Lean.Analytic.HandVariance.Compute
