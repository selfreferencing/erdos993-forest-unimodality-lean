import Erdos993Lean.Analytic.HandVariance.Compute.Source

/-!
# Explicit formulas of the hand variance finite checks

Source: TWIN v1.8 Appendix N.4, `tgt:lem:dY`, `tgt:lem:dmu`,
the child-polygon paragraph and `mc:lem:base`. The environment retains
Y,e,p,k,theta,alpha,gamma,A, their activity derivatives, the polygon point,
log activity, exp Y, cap J, Lbar and Lbar', phi, and the leaf quantities.
-/

namespace Erdos993Lean.Analytic.HandVariance.Compute

instance : Add Expr := ⟨Expr.add⟩
instance : Sub Expr := ⟨Expr.sub⟩
instance : Neg Expr := ⟨Expr.neg⟩
instance : Mul Expr := ⟨Expr.mul⟩
instance : Div Expr := ⟨Expr.div⟩
instance (n : Nat) : OfNat Expr n := ⟨.rat n⟩

def fY : Expr := .var 0
def fe : Expr := .var 1
def fp : Expr := .var 2
def fk : Expr := .var 3
def fw : Expr := .var 4
def fa : Expr := .var 5
def fg : Expr := .var 6
def fAD : Expr := .var 7
def fad : Expr := .var 8
def fgd : Expr := .var 9
def fADd : Expr := .var 10
def fr : Expr := .var 11
def fJ : Expr := .var 12
def fmu : Expr := .var 13
def fexpY : Expr := .var 14
def fJcap : Expr := .var 15
def fL : Expr := .var 16
def fLp : Expr := .var 17
def fphi : Expr := .var 18
def fslope : Expr := .var 19
def fintercept : Expr := .var 20
def fq : Expr := .var 21
def fbarphi : Expr := .var 22
def fD : Expr := .var 23
def fpp : Expr := .var 24
def fqq : Expr := .var 25

def fh : Expr := 1 - fp + fg * fk
def fhp : Expr := fpp + fg * fk * fw
def fhpp : Expr := -fpp * (1 - 2 * fp) + fg * fk * (.sq fw + fk * fw - fpp)
def fN : Expr := fAD - fh - fa / fk
def fNp : Expr := -fhp + fa * fw / fk
def fNpp : Expr := -fhpp + fa * (fw - fpp / fk - .sq fw / fk)
def fLdirect : Expr := fg * fe - fh * fY
def fLpdirect : Expr := fg * fe - fh - fhp * fY
def fLpp : Expr := fg * fe - 2 * fhp - fhpp * fY
def fZ : Expr := fg + fJ * fL
def fZp : Expr := fJ * fLp
def fZpp : Expr := fJ * fLpp
def fNoverYpp : Expr := (fNpp * .sq fY - 2 * fNp * fY + 2 * fN) / (.sq fY * fY)
def fGpp : Expr := fJ * ((2 * .sq fhp + 2 * fh * fhpp) / fZ -
  4 * fh * fhp * fZp / .sq fZ - .sq fh * fZpp / .sq fZ +
  2 * .sq fh * .sq fZp / (.sq fZ * fZ))
def fA : Expr := fa * fe + fN / fY + fa * fr - fJ * .sq fh / fZ
def fAgamma : Expr := fa * fe + fN / fY + fa * fr - fJ * .sq fh / fg
def fAp : Expr := fa * fe + (fNp * fY - fN) / .sq fY -
  fJ * (2 * fh * fhp * fZ - .sq fh * fZp) / .sq fZ
def fAgammap : Expr := fa * fe + (fNp * fY - fN) / .sq fY - 2 * fJ * fh * fhp / fg
def fApp : Expr := fa * fe + fNoverYpp - fGpp
def fAgammapp : Expr := fa * fe + fNoverYpp - fJ * (2 * .sq fhp + 2 * fh * fhpp) / fg
def fhd : Expr := -fpp - fg * fk * fw + fgd * fk
def fNd : Expr := fADd - fhd - fad / fk - fa * fw / fk
def fZd : Expr := fgd + fJ * (fgd * fe - fg * fe - fhd * fY)
def fAd : Expr := (fad - fa) * fe + fNd / fY + fad * fr -
  fJ * (2 * fh * fhd * fZ - .sq fh * fZd) / .sq fZ
def fAgammad : Expr := (fad - fa) * fe + fNd / fY + fad * fr -
  fJ * (2 * fh * fhd / fg - .sq fh * fgd / .sq fg)

def fn : Expr := fmu - .log (fexpY - 1) - 1 / fk
def fnp : Expr := -fexpY / (fexpY - 1) + fw / fk
def fnpp : Expr := fexpY / .sq (fexpY - 1) + fw - fpp / fk - .sq fw / fk
def fEminus : Expr := fe + fn / fY
def fEminusp : Expr := fe + (fnp * fY - fn) / .sq fY
def fEminuspp : Expr := fe + (fnpp * .sq fY - 2 * fnp * fY + 2 * fn) / (.sq fY * fY)
def flHat : Expr := -fL
def flHatp : Expr := -fLp
def flHatpp : Expr := -fLpp
def fDen : Expr := fg - fJcap * flHat
def fC : Expr := fa * fEminus - fg * flHat / fDen
def fCp : Expr := fa * fEminusp - .sq fg / .sq fDen * flHatp
def fCpp : Expr := fa * fEminuspp -
  (2 * fJcap * .sq fg / (.sq fDen * fDen)) * .sq flHatp - .sq fg / .sq fDen * flHatpp
def fCd : Expr := fad * fEminus + fa * (-fe + (1 - fw / fk) / fY) +
  (fgd * fJcap * .sq flHat - .sq fg * (fhd * fY - fgd * fe + fg * fe)) / .sq fDen

/-- Source-exact product/inverse jet evaluation for the polygon checks.
Algebraically expanding these jets can widen dependency intervals. -/
structure ExprJet where
  value : Expr
  first : Expr
  second : Expr

def ExprJet.mul (a b : ExprJet) : ExprJet :=
  ⟨a.value*b.value, a.first*b.value+a.value*b.first,
    a.second*b.value+2*a.first*b.first+a.value*b.second⟩

def ExprJet.inv (a : ExprJet) : ExprJet :=
  let iv : Expr := 1/a.value
  ⟨iv, -a.first*.sq iv, (2*.sq a.first-a.value*a.second)*.sq iv*iv⟩

def childMassJet : ExprJet := ⟨fphi, -fp, fp*(1-fp)⟩
def childMsgJet : ExprJet := ⟨fp, -(fp*(1-fp)), fp*(1-fp)*(1-2*fp)⟩
def childRJet : ExprJet := (ExprJet.mk fY 1 0).mul childMassJet.inv
def childJJet : ExprJet := (childMsgJet.mul childMsgJet).mul childRJet

def fchildR : Expr := childRJet.value
def fchildRp : Expr := childRJet.first
def fchildRpp : Expr := childRJet.second
def fchildJ : Expr := childJJet.value
def fchildJp : Expr := childJJet.first
def fchildJpp : Expr := childJJet.second
def fpolygon : Expr := fchildJ - fchildR*fslope
def fpolygonp : Expr := fchildJp - fchildRp*fslope
def fpolygonpp : Expr := fchildJpp - fchildRpp*fslope

def fbase : Expr := fD * .sq fq - fa * fbarphi - fg * .sq fq / fbarphi
def fbased : Expr := 2 * fD * fq * fqq - fad * fbarphi - fa * fq -
  fgd * .sq fq / fbarphi - 2 * fg * fq * fqq / fbarphi +
  fg * .sq fq * fq / .sq fbarphi

end Erdos993Lean.Analytic.HandVariance.Compute
