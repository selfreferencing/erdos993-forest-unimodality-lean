import Erdos993Lean.Analytic.HandVariance.Compute.Formulas

/-!
# Interval environments for Appendix N.4's explicit formulas

Source: corrected `two_gen_transport/scripts/verify_final.py` (mid),
`multiplier_curve/scripts/transport_certificate.py` (other segments).
The mid theta and activity-derivative corner restrictions are explicit guards.
Mean-value intersections for the other segments retain both original bounds.
Soundness of these environments is a separate proof obligation.
-/

namespace Erdos993Lean.Analytic.HandVariance.Compute

open Erdos993Lean.Analytic.TailCert.Compute

structure Parameters where
  D : Rat
  a : Rat
  g : Rat
  deriving Repr

def parameters : Nat → Parameters
  | 0 => ⟨6/5, 11/25, 21/2⟩
  | 1 => ⟨6/5, 23/50, 13⟩
  | 2 => ⟨7/5, 9/20, 23/2⟩
  | 3 => ⟨8/5, 47/100, 43/4⟩
  | 4 => ⟨9/5, 1/2, 41/4⟩
  | _ => ⟨21/10, 57/100, 39/4⟩

def ratSpan (a b : Rat) : Ival := ⟨(ofRat a).lo, (ofRat b).hi⟩
def hull (a b : Ival) : Ival := ⟨min a.lo b.lo, max a.hi b.hi⟩
def intersection (a b : Ival) : Ival := ⟨max a.lo b.lo, min a.hi b.hi⟩
def zeroI : Ival := pt 0
def oneI : Ival := pt one

/-- Exact endpoint/quarter enclosure of `p(1-p)`, as in the source `pp_of`. -/
def parabolaRange (p : Ival) : Ival := Id.run do
  let a : Rat := (p.lo : Rat) / (one : Rat)
  let b : Rat := (p.hi : Rat) / (one : Rat)
  let va := a * (1 - a)
  let vb := b * (1 - b)
  let high := if a ≤ 1/2 ∧ 1/2 ≤ b then 1/4 else max va vb
  return ratSpan (min va vb) high

structure Point where
  e : Ival
  p : Ival
  phi : Ival
  k : Ival
  theta : Ival
  safe : Bool
  deriving Repr

def point (lam Y : Rat) : Point := Id.run do
  let li := ofRat lam
  let r := mul li (expI (ofRat (-Y)))
  let den := add oneI r
  let p := div r den
  let phi := logI den
  let k := div p phi
  return ⟨div (expI (ofRat Y)) li, p, phi, k, sub (add k p) oneI,
    decide (0 < li.lo) && decide (0 < den.lo) && decide (0 < phi.lo)⟩

structure Context where
  env : Nat → Ival
  safe : Bool

def qRat (lam : Rat) : Rat := lam / (1 + lam)
def alphaRat (par : Parameters) (lam : Rat) : Rat := par.a * qRat lam
def gammaRat (par : Parameters) (lam : Rat) : Rat := lam * (3 + lam) / par.g
def capARat (par : Parameters) (lam : Rat) : Rat := 1 + (par.D - 1) * qRat lam
def gammaDotRat (par : Parameters) (lam : Rat) : Rat := lam * (3 + 2 * lam) / par.g

/-- The directly evaluated, source-exact primitive environment. -/
def rawContext (par : Parameters) (ys ls : Span) (r J Jcap : Rat)
    (cornerTheta : Bool) : Context := Id.run do
  let pa := point ls.hi ys.lo
  let pb := point ls.lo ys.hi
  let e : Ival := ⟨pa.e.lo, pb.e.hi⟩
  let p : Ival := ⟨pb.p.lo, pa.p.hi⟩
  let phi : Ival := ⟨pb.phi.lo, pa.phi.hi⟩
  let k : Ival := ⟨pa.k.lo, pb.k.hi⟩
  let theta : Ival := if cornerTheta then ⟨pb.theta.lo, pa.theta.hi⟩
    else sub (add k p) oneI
  let qq : Ival := if cornerTheta then
      hull (ofRat (ls.lo / (1 + ls.lo) ^ 2)) (ofRat (ls.hi / (1 + ls.hi) ^ 2))
    else ratSpan (ls.lo / (1 + ls.hi) ^ 2) (ls.hi / (1 + ls.lo) ^ 2)
  let env : Nat → Ival := fun i => match i with
    | 0 => ratSpan ys.lo ys.hi
    | 1 => e
    | 2 => p
    | 3 => k
    | 4 => theta
    | 5 => ratSpan (alphaRat par ls.lo) (alphaRat par ls.hi)
    | 6 => ratSpan (gammaRat par ls.lo) (gammaRat par ls.hi)
    | 7 => ratSpan (capARat par ls.lo) (capARat par ls.hi)
    | 8 => mul (ofRat par.a) qq
    | 9 => ratSpan (gammaDotRat par ls.lo) (gammaDotRat par ls.hi)
    | 10 => mul (ofRat (par.D - 1)) qq
    | 11 => ofRat r
    | 12 => ofRat J
    | 13 => logI (ratSpan ls.lo ls.hi)
    | 14 => expI (ratSpan ys.lo ys.hi)
    | 15 => ofRat Jcap
    | 18 => phi
    | 21 => ratSpan (qRat ls.lo) (qRat ls.hi)
    | 22 => logI (add oneI (ratSpan ls.lo ls.hi))
    | 23 => ofRat par.D
    | 24 => parabolaRange p
    | 25 => qq
    | _ => zeroI
  let l := fLdirect.evalI env
  let lp := fLpdirect.evalI env
  let env' : Nat → Ival := fun i => if i == 16 then l else if i == 17 then lp else env i
  let safe := pa.safe && pb.safe && decide (ys.lo ≤ ys.hi) && decide (ls.lo ≤ ls.hi) &&
    decide (0 < ls.lo) && decide (0 < par.a) && decide (0 < par.g) && decide (1 ≤ par.D) &&
    fLdirect.safe env && fLpdirect.safe env &&
    (!cornerTheta || (decide (0 ≤ ys.lo) && decide (ls.hi ≤ 263/200) &&
      decide (ls.hi ≤ 1 ∨ 1 ≤ ls.lo)))
  return ⟨env', safe⟩

/-- The additional mean-value intersections used only by the five non-mid segments. -/
def context (par : Parameters) (ys ls : Span) (r J Jcap : Rat) (midMethod : Bool) : Context := Id.run do
  let raw := rawContext par ys ls r J Jcap midMethod
  if midMethod then return raw
  let center := (ys.lo + ys.hi) / 2
  let radius := (ys.hi - ys.lo) / 2
  let atCenter := rawContext par ⟨center, center⟩ ls r J Jcap false
  let delta := ratSpan (-radius) radius
  let lp := intersection (raw.env 17) (add (atCenter.env 17) (mul delta (fLpp.evalI raw.env)))
  let l := intersection (raw.env 16) (add (atCenter.env 16) (mul delta lp))
  let env : Nat → Ival := fun i => if i == 16 then l else if i == 17 then lp else raw.env i
  return ⟨env, raw.safe && atCenter.safe && fLpp.safe raw.env &&
    decide (l.lo ≤ l.hi) && decide (lp.lo ≤ lp.hi)⟩

def loRat (a : Ival) : Rat := (a.lo : Rat) / (one : Rat)
def hiRat (a : Ival) : Rat := (a.hi : Rat) / (one : Rat)

def halves (s : Span) (useHalves : Bool) : List Span :=
  if useHalves then
    [⟨s.lo, (s.lo + s.hi)/2⟩, ⟨(s.lo + s.hi)/2, s.hi⟩]
  else [s]

end Erdos993Lean.Analytic.HandVariance.Compute
