import Erdos993Lean.Analytic.HandVariance.ContextSound
import Erdos993Lean.Analytic.HandVariance.FeasibleDerivatives
import Erdos993Lean.Analytic.HandVariance.Child

/-!
# The real meaning of the finite-check formulas

Source: TWIN v1.8 Appendix N.4, normalized vertex functions and their jets,
feasible CA lower function, child polygon and selected-leaf base. The
retained real environment supplies the exact activity, parent mass and
polygon point; these identities assert no signs or interval covering.
-/
namespace Erdos993Lean.Analytic.HandVariance.Compute
open Real Reserve

variable (par : Parameters) (lam Y r J Jcap : ℝ)

/-- Source: `tgt:lem:dY`, ĥ. -/
theorem eval_fh : fh.evalR (realEnv par lam Y r J Jcap) = hHat par.asBand lam Y := by
  dsimp [fh, fp, fg, fk, Expr.evalR, realEnv, hHat, Reserve.Cert.hF, parentK]
  norm_num
/-- Source: `tgt:lem:dY`, ĥ′. -/
theorem eval_fhp : fhp.evalR (realEnv par lam Y r J Jcap) = hPrime par.asBand lam Y := by rfl
/-- Source: `tgt:lem:dY`, ĥ″. -/
theorem eval_fhpp : fhpp.evalR (realEnv par lam Y r J Jcap) = hSecond par.asBand lam Y := by
  dsimp [fhpp, fpp, fp, fg, fk, fw, Expr.evalR, realEnv, hSecond]
  ring
/-- Source: `hand:var:set`, N. -/
theorem eval_fN : fN.evalR (realEnv par lam Y r J Jcap) = nTerm par.asBand lam Y := by
  simp only [fN, Expr.evalR, eval_fh]
  rfl
/-- Source: `tgt:lem:dY`, N′. -/
theorem eval_fNp : fNp.evalR (realEnv par lam Y r J Jcap) = nPrime par.asBand lam Y := by rfl
/-- Source: `tgt:lem:dY`, N″. -/
theorem eval_fNpp : fNpp.evalR (realEnv par lam Y r J Jcap) = nSecond par.asBand lam Y := by
  dsimp [fNpp, fhpp, fpp, fp, fg, fk, fw, fa, Expr.evalR, realEnv, nSecond, hSecond]
  ring
/-- Source: `hand:var:set`, L̄. -/
theorem eval_fLdirect : fLdirect.evalR (realEnv par lam Y r J Jcap) = lBar par.asBand lam Y := by
  simp only [fLdirect, Expr.evalR, eval_fh]
  rfl
/-- Source: `tgt:lem:dY`, L̄′. -/
theorem eval_fLpdirect : fLpdirect.evalR (realEnv par lam Y r J Jcap) = lPrime par.asBand lam Y := by
  simp only [fLpdirect, Expr.evalR, eval_fh, eval_fhp]
  rfl
/-- Source: `tgt:lem:dY`, L̄″. -/
theorem eval_fLpp : fLpp.evalR (realEnv par lam Y r J Jcap) = lSecond par.asBand lam Y := by
  dsimp [fLpp, fe, fY, fg, fhp, fhpp, fpp, fp, fk, fw, Expr.evalR, realEnv, lSecond, hPrime, hSecond]
  ring
/-- Source: `hand:var:set`, Z̄ at the retained J. -/
theorem eval_fZ : fZ.evalR (realEnv par lam Y r J Jcap) = zBar par.asBand lam Y J := by rfl
/-- Source: `hand:var:set`, normalized AC at the retained polygon point. -/
theorem eval_fA : fA.evalR (realEnv par lam Y r J Jcap) = vertexA par.asBand lam Y r J := by
  simp only [fA, Expr.evalR, eval_fN, eval_fh, eval_fZ]
  rfl
/-- Source: `arc:eq:maj`, the gamma-denominator comparison. -/
theorem eval_fAgamma : fAgamma.evalR (realEnv par lam Y r J Jcap) = vertexAgamma par.asBand lam Y r J := by
  simp only [fAgamma, Expr.evalR, eval_fN, eval_fh]
  rfl
/-- Source: `tgt:lem:dY`, AC first derivative. -/
theorem eval_fAp : fAp.evalR (realEnv par lam Y r J Jcap) = vertexAPrime par.asBand lam Y r J := by
  simp only [fAp, Expr.evalR, eval_fNp, eval_fN, eval_fh, eval_fhp, eval_fZ]
  dsimp [fa, fe, fY, fJ, fZp, fLp, Expr.evalR, realEnv, vertexAPrime, nOverYPrime, gPrime]
  norm_num
/-- Source: `tgt:lem:dY`, AC second derivative. -/
theorem eval_fApp : fApp.evalR (realEnv par lam Y r J Jcap) = vertexASecond par.asBand lam Y r J := by
  dsimp [fApp, fa, fe, fJ, fNoverYpp, fGpp, fNpp, fNp, fN, fAD, fh, fhp, fhpp, fpp, fp, fg, fk, fw, fY, fZ, fZp, fZpp, fL, fLp, fLpp, Expr.evalR, realEnv, vertexASecond, nOverYSecond, gSecond, nTerm, nPrime, nSecond, hHat, Reserve.Cert.hF, hPrime, hSecond, lSecond, zBar, parentK]
  simp only [pow_succ, pow_zero]
  ring
/-- Source: `tgt:lem:dY`, majorant first derivative. -/
theorem eval_fAgammap : fAgammap.evalR (realEnv par lam Y r J Jcap) = vertexAgammaPrime par.asBand lam Y r J := by
  simp only [fAgammap, Expr.evalR, eval_fNp, eval_fN, eval_fh, eval_fhp]
  dsimp [fa, fe, fY, fJ, fg, Expr.evalR, realEnv, vertexAgammaPrime, nOverYPrime]
  norm_num
/-- Source: `tgt:lem:dY`, majorant second derivative. -/
theorem eval_fAgammapp : fAgammapp.evalR (realEnv par lam Y r J Jcap) = vertexAgammaSecond par.asBand lam Y r J := by
  dsimp [fAgammapp, fa, fe, fJ, fNoverYpp, fNpp, fNp, fN, fAD, fh, fhp, fhpp, fpp, fp, fg, fk, fw, fY, Expr.evalR, realEnv, vertexAgammaSecond, nOverYSecond, nTerm, nPrime, nSecond, hHat, Reserve.Cert.hF, hPrime, hSecond, parentK]
  simp only [pow_succ, pow_zero]
  ring
/-- Source: `tgt:lem:feas`, exact E₋. -/
theorem eval_fEminus : fEminus.evalR (realEnv par lam Y r J Jcap) = eMinus lam Y := by
  norm_num [fEminus, fn, fe, fY, fmu, fexpY, fk, Expr.evalR, realEnv, eMinus]
/-- Source: `tgt:lem:dY`, E₋′. -/
theorem eval_fEminusp : fEminusp.evalR (realEnv par lam Y r J Jcap) = eMinusPrime lam Y := by
  norm_num [fEminusp, fnp, fn, fe, fY, fmu, fexpY, fk, fw, Expr.evalR, realEnv,
    eMinusPrime, eNumeratorPrime, eNumerator]
/-- Source: `tgt:lem:dY`, E₋″. -/
theorem eval_fEminuspp : fEminuspp.evalR (realEnv par lam Y r J Jcap) = eMinusSecond lam Y := by
  dsimp [fEminuspp, fe, fnpp, fnp, fn, fexpY, fw, fk, fp, fpp, fY, fmu, Expr.evalR, realEnv, eMinusSecond, eNumerator, eNumeratorPrime, eNumeratorSecond]
  simp only [pow_succ, pow_zero]
  ring
/-- Source: `tgt:lem:feas`, exact C at the retained child cap. -/
theorem eval_fC : fC.evalR (realEnv par lam Y r J Jcap) = cLower par.asBand lam Y Jcap := by
  simp only [fC, Expr.evalR, eval_fEminus]
  rfl
/-- Source: `tgt:lem:dY`, C′ with the denominator sign retained separately. -/
theorem eval_fCp : fCp.evalR (realEnv par lam Y r J Jcap) = cLowerPrime par.asBand lam Y Jcap := by
  dsimp [fCp, fa, fEminusp, fnp, fn, fe, fexpY, fw, fk, fY, fmu, fg,
    fDen, fJcap, flHat, flHatp, fL, fLp, Expr.evalR, realEnv,
    cLowerPrime, eMinusPrime, eNumeratorPrime, eNumerator]
  simp only [mul_neg, sub_neg_eq_add]
  ring
/-- Source: `tgt:lem:dY`, C″ with the denominator sign retained separately. -/
theorem eval_fCpp : fCpp.evalR (realEnv par lam Y r J Jcap) = cLowerSecond par.asBand lam Y Jcap := by
  dsimp [fCpp, fa, fEminuspp, fnpp, fnp, fn, fe, fexpY, fw, fk, fp, fpp,
    fY, fmu, fg, fDen, fJcap, flHat, flHatp, flHatpp, fL, fLp, fLpp,
    fhp, fhpp, fh, Expr.evalR, realEnv, cLowerSecond, eMinusSecond,
    eNumeratorSecond, eNumeratorPrime, eNumerator, lSecond, hPrime, hSecond]
  simp only [mul_neg, sub_neg_eq_add]
  simp only [pow_succ, pow_zero]
  ring

/-- Source: `tgt:lem:dmu`, α̇ as the retained activity variance. -/
theorem eval_fad (hlam : 0 < lam) :
    fad.evalR (realEnv par lam Y r J Jcap) = alphaDot par.asBand lam := by
  dsimp [fad, Expr.evalR, realEnv, alphaDot, Parameters.asBand]
  rw [activityVariance_eq hlam]
  ring
/-- Source: `tgt:lem:dmu`, γ̇. -/
theorem eval_fgd : fgd.evalR (realEnv par lam Y r J Jcap) = HandVariance.gammaDot par.asBand lam := by rfl
/-- Source: `tgt:lem:dmu`, Ȧ. -/
theorem eval_fADd (hlam : 0 < lam) :
    fADd.evalR (realEnv par lam Y r J Jcap) = capADot par.asBand lam := by
  dsimp [fADd, Expr.evalR, realEnv, capADot, Parameters.asBand]
  rw [activityVariance_eq hlam]
  ring
/-- Source: `tgt:lem:dmu`, ĥ dot. -/
theorem eval_fhd : fhd.evalR (realEnv par lam Y r J Jcap) = hDot par.asBand lam Y := by
  dsimp [fhd, fpp, fp, fg, fk, fw, fgd, Expr.evalR, realEnv, hDot, gammaDot, HandVariance.gammaDot, Parameters.asBand]
  ring
/-- Source: `tgt:lem:dmu`, N dot. -/
theorem eval_fNd (hlam : 0 < lam) :
    fNd.evalR (realEnv par lam Y r J Jcap) = nDot par.asBand lam Y := by
  simp only [fNd, Expr.evalR, eval_fADd par lam Y r J Jcap hlam,
    eval_fhd, eval_fad par lam Y r J Jcap hlam]
  rfl
/-- Source: `tgt:lem:dmu`, Z̄ dot. -/
theorem eval_fZd : fZd.evalR (realEnv par lam Y r J Jcap) = zDot par.asBand lam Y J := by
  dsimp [fZd, fg, fJ, fY, fe, fhd, fpp, fp, fk, fw, fgd, Expr.evalR, realEnv, zDot, lDot, hDot, gammaDot, HandVariance.gammaDot, Parameters.asBand]
  ring
/-- Source: `tgt:lem:dmu`, AC dot. -/
theorem eval_fAd (hlam : 0 < lam) :
    fAd.evalR (realEnv par lam Y r J Jcap) = vertexADot par.asBand lam Y r J := by
  simp only [fAd, Expr.evalR, eval_fNd par lam Y r J Jcap hlam,
    eval_fad par lam Y r J Jcap hlam, eval_fh, eval_fhd, eval_fZd]
  rfl
/-- Source: `tgt:lem:dmu`, majorant dot. -/
theorem eval_fAgammad (hlam : 0 < lam) :
    fAgammad.evalR (realEnv par lam Y r J Jcap) = vertexAgammaDot par.asBand lam Y r J := by
  simp only [fAgammad, Expr.evalR, eval_fNd par lam Y r J Jcap hlam,
    eval_fad par lam Y r J Jcap hlam, eval_fh, eval_fhd, eval_fgd]
  rfl

/-- Source: `tgt:lem:dmu`, CA lower-function transport. -/
theorem eval_fCd (hlam : 0 < lam) :
    fCd.evalR (realEnv par lam Y r J Jcap) = cLowerDot par.asBand lam Y Jcap := by
  simp only [fCd, Expr.evalR, eval_fad par lam Y r J Jcap hlam, eval_fEminus]
  dsimp [fa, fe, fw, fk, fY, fgd, fJcap, flHat, fL, fg, fhd, fpp, fp,
    fDen, Expr.evalR, realEnv, cLowerDot, eMinusDot, lDot, hDot, gammaDot, HandVariance.gammaDot, Parameters.asBand]
  simp only [mul_neg, sub_neg_eq_add]
  ring

/-- Source: the child-polygon paragraph, source-exact reciprocal/product jet. -/
theorem eval_fchildR : fchildR.evalR (realEnv par lam Y r J Jcap) = childR lam Y := by
  dsimp [fchildR, childRJet, ExprJet.mul, ExprJet.inv, childMassJet,
    fY, fphi, Expr.evalR, realEnv, childR]
  ring

/-- Source: the child-polygon paragraph, first child jet. -/
theorem eval_fchildRp (hlam : 0 < lam) :
    fchildRp.evalR (realEnv par lam Y r J Jcap) = childRPrime lam Y := by
  have hphi := (Reserve.lmass_pos hlam Y).ne'
  dsimp [fchildRp, childRJet, ExprJet.mul, ExprJet.inv, childMassJet,
    fY, fp, fphi, Expr.evalR, realEnv, childRPrime]
  field_simp [hphi]
  ring

/-- Source: the child-polygon paragraph, second child jet. -/
theorem eval_fchildRpp (hlam : 0 < lam) :
    fchildRpp.evalR (realEnv par lam Y r J Jcap) = childRSecond lam Y := by
  have hphi := (Reserve.lmass_pos hlam Y).ne'
  dsimp [fchildRpp, childRJet, ExprJet.mul, ExprJet.inv, childMassJet,
    fY, fp, fphi, Expr.evalR, realEnv, childRSecond]
  field_simp [hphi]
  ring

/-- Source: the child-polygon paragraph, the actual J = p² r. -/
theorem eval_fchildJ : fchildJ.evalR (realEnv par lam Y r J Jcap) = coefJ lam Y := by
  dsimp [fchildJ, childJJet, childRJet, ExprJet.mul, ExprJet.inv, childMassJet,
    childMsgJet, fY, fp, fphi, Expr.evalR, realEnv, coefJ]
  ring

/-- Source: the child-polygon paragraph, first J jet. -/
theorem eval_fchildJp (hlam : 0 < lam) :
    fchildJp.evalR (realEnv par lam Y r J Jcap) = coefJPrime lam Y := by
  have hphi := (Reserve.lmass_pos hlam Y).ne'
  dsimp [fchildJp, childJJet, childRJet, ExprJet.mul, ExprJet.inv, childMassJet,
    childMsgJet, fY, fp, fphi, Expr.evalR, realEnv, coefJPrime, childR, childRPrime]
  field_simp [hphi]
  ring

/-- Source: the child-polygon paragraph, second J jet. -/
theorem eval_fchildJpp (hlam : 0 < lam) :
    fchildJpp.evalR (realEnv par lam Y r J Jcap) = coefJSecond lam Y := by
  have hphi := (Reserve.lmass_pos hlam Y).ne'
  dsimp [fchildJpp, childJJet, childRJet, ExprJet.mul, ExprJet.inv, childMassJet,
    childMsgJet, fY, fp, fphi, Expr.evalR, realEnv, coefJSecond, childR, childRPrime,
    childRSecond]
  field_simp [hphi]
  ring

/-- Source: exact retained line identity in the child polygon checks. -/
noncomputable def lineEnv (par : Parameters) (lam Y slope intercept : ℝ) : Nat → ℝ :=
  fun i => if i == 19 then slope else if i == 20 then intercept else realEnv par lam Y 0 0 0 i

/-- Source: the child-polygon paragraph, line slack J − b r. -/
theorem eval_fpolygon (slope intercept : ℝ) :
    fpolygon.evalR (lineEnv par lam Y slope intercept) = coefJ lam Y-slope*childR lam Y := by
  dsimp [fpolygon, fchildJ, fchildR, childJJet, childRJet, ExprJet.mul, ExprJet.inv,
    childMassJet, childMsgJet, fY, fp, fphi, fslope, Expr.evalR, lineEnv, realEnv,
    coefJ, childR]
  ring

/-- Source: the child-polygon paragraph, first line-slack derivative. -/
theorem eval_fpolygonp (slope intercept : ℝ) (hlam : 0 < lam) :
    fpolygonp.evalR (lineEnv par lam Y slope intercept) =
      coefJPrime lam Y-slope*childRPrime lam Y := by
  have hphi := (Reserve.lmass_pos hlam Y).ne'
  dsimp [fpolygonp, fchildJp, fchildRp, childJJet, childRJet, ExprJet.mul,
    ExprJet.inv, childMassJet, childMsgJet, fY, fp, fphi, fslope, Expr.evalR,
    lineEnv, realEnv, coefJPrime, childR, childRPrime]
  field_simp [hphi]
  ring

/-- Source: the child-polygon paragraph, second line-slack derivative. -/
theorem eval_fpolygonpp (slope intercept : ℝ) (hlam : 0 < lam) :
    fpolygonpp.evalR (lineEnv par lam Y slope intercept) =
      coefJSecond lam Y-slope*childRSecond lam Y := by
  have hphi := (Reserve.lmass_pos hlam Y).ne'
  dsimp [fpolygonpp, fchildJpp, fchildRpp, childJJet, childRJet, ExprJet.mul,
    ExprJet.inv, childMassJet, childMsgJet, fY, fp, fphi, fslope, Expr.evalR,
    lineEnv, realEnv, coefJSecond, childR, childRPrime, childRSecond]
  field_simp [hphi]
  ring

/-- Source: `mc:lem:base`, the selected-leaf slack. -/
theorem eval_fbase : fbase.evalR (realEnv par lam Y r J Jcap) = baseSlack par.asBand lam := by rfl
/-- Source: `mc:lem:base`, leaf slack dot. -/
theorem eval_fbased (hlam : 0 < lam) :
    fbased.evalR (realEnv par lam Y r J Jcap) = baseSlackDot par.asBand lam := by
  dsimp [fbased, fD, fq, fqq, fad, fa, fg, fgd, fbarphi, Expr.evalR,
    realEnv, baseSlackDot]
  rw [activityVariance_eq hlam]
  dsimp [alphaDot, HandVariance.gammaDot, gammaDot, Parameters.asBand]
  ring

end Erdos993Lean.Analytic.HandVariance.Compute

#print axioms Erdos993Lean.Analytic.HandVariance.Compute.eval_fApp
#print axioms Erdos993Lean.Analytic.HandVariance.Compute.eval_fCpp
#print axioms Erdos993Lean.Analytic.HandVariance.Compute.eval_fCd
#print axioms Erdos993Lean.Analytic.HandVariance.Compute.eval_fpolygonpp
