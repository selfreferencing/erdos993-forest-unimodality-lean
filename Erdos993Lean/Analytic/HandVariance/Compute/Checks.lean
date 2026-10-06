import Erdos993Lean.Analytic.HandVariance.Compute.Context

/-!
# Numeric part of the 4,321 Appendix N.4 checks

Source: the final mid verifier and the other-segment transport verifier.
These functions compute rational Taylor and transport bounds; they do not
assert that a passing check proves a forest theorem. Soundness and coverage
must consume the exact recipes and retained function derivatives separately.
-/

namespace Erdos993Lean.Analytic.HandVariance.Compute

open Erdos993Lean.Analytic.TailCert.Compute

def eval (ctx : Context) (e : Expr) : Option Ival :=
  if ctx.safe && e.safe ctx.env then some (e.evalI ctx.env) else none

def quadratic (v d m c x : Rat) : Rat := v + d * (x-c) + m * (x-c)^2 / 2

def twoEnded (s : Span) (v0 d0 v1 d1 m : Rat) : Rat := Id.run do
  let q0 := quadratic v0 d0 m s.lo
  let q1 := quadratic v1 d1 m s.hi
  let e0 := q0 s.lo - q1 s.lo
  let e1 := q0 s.hi - q1 s.hi
  let edgeBound := min (max (q0 s.lo) (q1 s.lo)) (max (q0 s.hi) (q1 s.hi))
  if e0 != e1 && decide ((e0 < 0 ∧ 0 < e1) ∨ (e1 < 0 ∧ 0 < e0)) then
    let crossing := s.lo + (s.hi-s.lo) * e0 / (e0-e1)
    return min edgeBound (max (q0 crossing) (q1 crossing))
  else return edgeBound

def transportLoss (dlo dhi deltaMinus deltaPlus : Rat) : Rat :=
  max (deltaPlus * max 0 (-dlo)) (deltaMinus * max 0 dhi)

def logUpper (q : Rat) : Option Rat :=
  let qi := ofRat q
  if 0 < qi.lo then some (hiRat (logI qi)) else none

def evalHull (par : Parameters) (ys ls : Span) (r J Jcap : Rat)
    (midMethod : Bool) (e : Expr) : Option Ival := do
  let spans := halves ys midMethod
  let values ← spans.mapM fun s => eval (context par s ls r J Jcap midMethod) e
  match values with
  | [] => none
  | first :: rest => some (rest.foldl hull first)

def vertexLower (a : Activity) (v : VertexCheck) : Option Rat := do
  let par := parameters a.segment
  let fixed : Span := ⟨a.center,a.center⟩
  let ctx0 := context par ⟨v.spatial.lo,v.spatial.lo⟩ fixed v.r v.J a.Jcap a.useHalves
  let ctx1 := context par ⟨v.spatial.hi,v.spatial.hi⟩ fixed v.r v.J a.Jcap a.useHalves
  let fn := if v.useGamma then fAgamma else fA
  let fnp := if v.useGamma then fAgammap else fAp
  let fnpp := if v.useGamma then fAgammapp else fApp
  let fnd := if v.useGamma then fAgammad else fAd
  let v0 ← eval ctx0 fn
  let d0 ← eval ctx0 fnp
  let v1 ← eval ctx1 fn
  let d1 ← eval ctx1 fnp
  let curv ← evalHull par v.spatial fixed v.r v.J a.Jcap a.useHalves fnpp
  let deriv ← evalHull par v.spatial a.activity v.r v.J a.Jcap a.useHalves fnd
  let dm ← logUpper (a.center/a.activity.lo)
  let dp ← logUpper (a.activity.hi/a.center)
  let beta := twoEnded v.spatial (loRat v0) (loRat d0) (loRat v1) (hiRat d1) (min 0 (loRat curv))
  return beta - transportLoss (loRat deriv) (hiRat deriv) dm dp

def caLower (a : Activity) (v : CACheck) : Option Rat := do
  let par := parameters a.segment
  if v.usePositiveL then
    let ctx := context par v.spatial a.activity 0 0 a.Jcap a.useHalves
    if ctx.safe then return loRat (ctx.env 16) else none
  else
    let center := (v.spatial.lo+v.spatial.hi)/2
    let radius := (v.spatial.hi-v.spatial.lo)/2
    let fixed : Span := ⟨a.center,a.center⟩
    let ctx := context par ⟨center,center⟩ fixed 0 0 a.Jcap a.useHalves
    let val ← eval ctx fC
    let slope ← eval ctx fCp
    let curv ← evalHull par v.spatial fixed 0 0 a.Jcap a.useHalves fCpp
    let deriv ← evalHull par v.spatial a.activity 0 0 a.Jcap a.useHalves fCd
    let dm ← logUpper (a.center/a.activity.lo)
    let dp ← logUpper (a.activity.hi/a.center)
    let beta := loRat val - max (-loRat slope) (hiRat slope) * radius +
      min 0 (loRat curv) * radius^2/2
    return beta - transportLoss (loRat deriv) (hiRat deriv) dm dp

def evalClosed (e : Expr) : Option Ival :=
  if e.safe (fun _ => zeroI) then some (e.evalI (fun _ => zeroI)) else none

def closedRat (q : Rat) : Expr := .rat q

/-- The five source flank bounds, retaining every denominator/sign proviso. -/
def flankBounds (a : Activity) : Option (List Rat) := do
  if a.leftEnd ≤ 0 || 3 < a.leftEnd || a.Jcap < 0 then none else do
    let par := parameters a.segment
    let al := alphaRat par a.activity.lo
    let ah := alphaRat par a.activity.hi
    let gl := gammaRat par a.activity.lo
    let gh := gammaRat par a.activity.hi
    let ad := capARat par a.activity.lo
    let pa := point a.activity.lo a.leftEnd
    let pb := point a.activity.hi 0
    let p3 := point a.activity.hi 3
    if !(pa.safe && pb.safe && p3.safe) then none else do
      let c1 := 1+gh
      let c2 := gl/a.activity.hi
      let logarithm ← evalClosed (.log (.rat (c1/c2)))
      if loRat logarithm < 1 then none else do
        let zlo := gl - a.Jcap*c1*(hiRat logarithm-1)
        let hhi := 1-loRat pa.p + gh*hiRat pa.k
        let nlo := ad - hhi - ah/loRat pb.k
        let t ← evalClosed (.maximum 0 (.log (.rat a.activity.lo) - .log (.exp (.rat a.leftEnd)-1)))
        let num := nlo + al*loRat t
        let ql := gl + a.Jcap*min 0 (gl/a.activity.hi-hhi*a.leftEnd)
        if num < 0 || ql ≤ 0 then none else do
          let left := al/a.activity.hi + num/a.leftEnd - a.Jcap*hhi^2/ql
          let nr := ad-1-gh-ah/loRat p3.k
          let logR ← logUpper ((1+gh)*a.activity.hi/gl)
          let er ← evalClosed (.exp 3)
          let qr := min gl (gl-a.Jcap*max 0 (3*(1+gh)-gl*loRat er/a.activity.hi))
          if 0 ≤ nr || 3 < logR || qr ≤ 0 then none else do
            let right := al*loRat er/a.activity.hi + nr/3 - (1+gh)^2*a.Jcap/qr
            let c0 := gl/a.activity.hi - (1+gh)/500
            let c3 := gl*loRat er/a.activity.hi - 3*(1+gh)
            return [zlo,left,right,c0,c3]

def allPositive (xs : List Rat) : Bool := xs.all fun x => decide (0 < x)
def optionPositive : Option Rat → Bool
  | none => false
  | some x => decide (0 < x)

def activityOK (a : Activity) : Bool :=
  decide (a.segment ≤ 5) && decide (0 < a.activity.lo) &&
  decide (a.activity.lo ≤ a.center ∧ a.center ≤ a.activity.hi) &&
  decide (a.activity.hi ≤ a.polygonActivity) &&
  a.vertexChecks.all (fun v => optionPositive (vertexLower a v)) &&
  a.caChecks.all (fun v => optionPositive (caLower a v)) &&
  match flankBounds a with | none => false | some xs => allPositive xs

def polygonLower (p : PolygonCheck) : Option Rat := do
  let par := parameters 1
  let center := (p.spatial.lo+p.spatial.hi)/2
  let radius := (p.spatial.hi-p.spatial.lo)/2
  let ls : Span := ⟨p.activity,p.activity⟩
  let fixLine := fun (ctx : Context) =>
    { ctx with env := fun i => if i == 19 then ofRat p.slope else
      if i == 20 then ofRat p.intercept else ctx.env i }
  -- These child expressions do not use theta: the general enclosure is valid
  -- at every positive polygon activity including the five upper segments.
  let atCenter := fixLine (rawContext par ⟨center,center⟩ ls 0 0 0 false)
  let onSpan := fixLine (rawContext par p.spatial ls 0 0 0 false)
  let val ← eval atCenter fpolygon
  let slope ← eval atCenter fpolygonp
  let second ← eval onSpan fpolygonpp
  return p.intercept - (hiRat val + max (-loRat slope) (hiRat slope)*radius +
    max 0 (hiRat second)*radius^2/2)

def chainLower (c : ChainCheck) : Option Rat := do
  let pa := point c.activity c.left
  let pb := match c.right with | none => zeroI | some t => (point c.activity t).p
  let rightSafe := match c.right with
    | none => true
    | some t => (point c.activity t).safe && decide (c.left < t)
  if !(pa.safe && rightSafe && decide (0 < c.left) && decide (0 ≤ pb.lo)) then none else do
    let term ← evalClosed (1 / .rat c.left + 1 / (1 + .rat (loRat pb)/2) - 2 + 2*.rat (hiRat pa.p))
    return -hiRat term

def polygonOK (p : Polygon) : Bool :=
  p.checks.all (fun c => optionPositive (polygonLower c)) &&
  p.chain.all (fun c => optionPositive (chainLower c))

def baseLower (b : BaseCheck) : Option Rat := do
  let par := parameters b.segment
  let center := (b.activity.lo+b.activity.hi)/2
  -- Base intervals may cross 1. Always use the rectangular, valid QQ bound.
  let atCenter := rawContext par ⟨0,0⟩ ⟨center,center⟩ 0 0 0 false
  let val ← eval atCenter fbase
  let ds ← (halves b.activity b.useHalves).mapM fun ls =>
    eval (rawContext par ⟨0,0⟩ ls 0 0 0 false) fbased
  let deriv := ds.foldl hull (ofRat 0)
  let dm ← logUpper (center/b.activity.lo)
  let dp ← logUpper (b.activity.hi/center)
  return loRat val - transportLoss (loRat deriv) (hiRat deriv) dm dp

end Erdos993Lean.Analytic.HandVariance.Compute
