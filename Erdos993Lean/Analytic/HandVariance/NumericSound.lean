import Erdos993Lean.Analytic.HandVariance.FormulaMeaning
import Erdos993Lean.Analytic.HandVariance.EvalSound
import Erdos993Lean.Analytic.HandVariance.NumericPrinciples

/-!
# Soundness of the AC and CA finite checks

Source: TWIN v1.8 Appendix N.4, proof of `tgt:thm`, `mc:thm:step`,
and `tgt:lem:dY`/`tgt:lem:dmu`. Each result refers to the actual retained
activity and spatial box. Global denominator positivity is supplied by
the separately checked flank certificate.
-/
namespace Erdos993Lean.Analytic.HandVariance.Compute
open Real Reserve Set Erdos993Lean.Analytic.TailCert.Compute

/-- Source: the two denominator tags in the AC checks. -/
noncomputable def taggedVertex (tag : Bool) (c : Band) (r J lam Y : ℝ) : ℝ :=
  if tag then vertexAgamma c lam Y r J else vertexA c lam Y r J
/-- Source: `tgt:lem:dY`, first derivative for the same retained tag. -/
noncomputable def taggedVertexPrime (tag : Bool) (c : Band) (r J lam Y : ℝ) : ℝ :=
  if tag then vertexAgammaPrime c lam Y r J else vertexAPrime c lam Y r J
/-- Source: `tgt:lem:dY`, second derivative for the same retained tag. -/
noncomputable def taggedVertexSecond (tag : Bool) (c : Band) (r J lam Y : ℝ) : ℝ :=
  if tag then vertexAgammaSecond c lam Y r J else vertexASecond c lam Y r J
/-- Source: `tgt:lem:dmu`, activity derivative for the same retained tag. -/
noncomputable def taggedVertexDot (tag : Bool) (c : Band) (r J lam Y : ℝ) : ℝ :=
  if tag then vertexAgammaDot c lam Y r J else vertexADot c lam Y r J

/-- Source: `tgt:lem:dY`, retained-tag spatial derivative. -/
theorem hasDerivAt_taggedVertex_Y (tag : Bool) (c : Band) (r J : ℝ)
    {lam Y : ℝ} (hlam : 0 < lam) (hY : Y ≠ 0) (hZ : zBar c lam Y J ≠ 0) :
    HasDerivAt (taggedVertex tag c r J lam) (taggedVertexPrime tag c r J lam Y) Y := by
  cases tag with
  | false => exact hasDerivAt_vertexA_Y c r J hlam hY hZ
  | true => exact hasDerivAt_vertexAgamma_Y c r J hlam hY

/-- Source: `tgt:lem:dY`, retained-tag second derivative. -/
theorem hasDerivAt_taggedVertexPrime_Y (tag : Bool) (c : Band) (r J : ℝ)
    {lam Y : ℝ} (hlam : 0 < lam) (hY : Y ≠ 0) (hZ : zBar c lam Y J ≠ 0) :
    HasDerivAt (taggedVertexPrime tag c r J lam) (taggedVertexSecond tag c r J lam Y) Y := by
  cases tag with
  | false => exact hasDerivAt_vertexAPrime_Y c r J hlam hY hZ
  | true => exact hasDerivAt_vertexAgammaPrime_Y c r J hlam hY

/-- Source: `tgt:lem:dmu`, retained-tag activity derivative. -/
theorem hasDerivAt_taggedVertex_mu (tag : Bool) (c : Band) (r J Y mu : ℝ)
    (hZ : zBar c (exp mu) Y J ≠ 0) (hg : gamma c (exp mu) ≠ 0) :
    HasDerivAt (fun t => taggedVertex tag c r J (exp t) Y)
      (taggedVertexDot tag c r J (exp mu) Y) mu := by
  cases tag with
  | false => exact hasDerivAt_vertexA_mu c Y r J mu hZ
  | true => exact hasDerivAt_vertexAgamma_mu c Y r J mu hg

/-- Source: the retained tag of the vertex function expression. -/
theorem eval_taggedVertex (tag : Bool) (par : Parameters) (lam Y r J cap : ℝ) :
    (if tag then fAgamma else fA).evalR (realEnv par lam Y r J cap) =
      taggedVertex tag par.asBand r J lam Y := by
  cases tag <;> first | exact eval_fA par lam Y r J cap | exact eval_fAgamma par lam Y r J cap
/-- Source: the retained tag of the vertex first derivative expression. -/
theorem eval_taggedVertexPrime (tag : Bool) (par : Parameters) (lam Y r J cap : ℝ) :
    (if tag then fAgammap else fAp).evalR (realEnv par lam Y r J cap) =
      taggedVertexPrime tag par.asBand r J lam Y := by
  cases tag <;> first | exact eval_fAp par lam Y r J cap | exact eval_fAgammap par lam Y r J cap
/-- Source: the retained tag of the vertex second derivative expression. -/
theorem eval_taggedVertexSecond (tag : Bool) (par : Parameters) (lam Y r J cap : ℝ) :
    (if tag then fAgammapp else fApp).evalR (realEnv par lam Y r J cap) =
      taggedVertexSecond tag par.asBand r J lam Y := by
  cases tag <;> first | exact eval_fApp par lam Y r J cap | exact eval_fAgammapp par lam Y r J cap
/-- Source: the retained tag of the vertex activity derivative expression. -/
theorem eval_taggedVertexDot (tag : Bool) (par : Parameters) (lam Y r J cap : ℝ)
    (hlam : 0 < lam) :
    (if tag then fAgammad else fAd).evalR (realEnv par lam Y r J cap) =
      taggedVertexDot tag par.asBand r J lam Y := by
  cases tag <;> first | exact eval_fAd par lam Y r J cap hlam | exact eval_fAgammad par lam Y r J cap hlam

/-- Source: `tgt:thm`; a successful endpoint and transport recipe supplies
its rational lower bound to its exact retained vertex function. -/
theorem vertexLower_sound (a : Activity) (v : VertexCheck) {beta : Rat}
    (hcheck : vertexLower a v = some beta)
    (hlo : 0 < (a.activity.lo : ℝ))
    (hc : (a.center : ℝ) ∈ Icc (a.activity.lo : ℝ) (a.activity.hi : ℝ))
    (hYpos : 0 < (v.spatial.lo : ℝ))
    (hZ : ∀ lam ∈ Icc (a.activity.lo : ℝ) (a.activity.hi : ℝ),
      ∀ Y ∈ Icc (v.spatial.lo : ℝ) (v.spatial.hi : ℝ),
      zBar (parameters a.segment).asBand lam Y v.J ≠ 0)
    (hg : ∀ lam ∈ Icc (a.activity.lo : ℝ) (a.activity.hi : ℝ),
      gamma (parameters a.segment).asBand lam ≠ 0)
    {lam Y : ℝ} (hlam : lam ∈ Icc (a.activity.lo : ℝ) (a.activity.hi : ℝ))
    (hY : Y ∈ Icc (v.spatial.lo : ℝ) (v.spatial.hi : ℝ)) :
    (beta : ℝ) ≤ taggedVertex v.useGamma (parameters a.segment).asBand v.r v.J lam Y := by
  simp only [vertexLower, Bind.bind, Option.bind_eq_some_iff, pure,
    Option.some.injEq] at hcheck
  obtain ⟨v0, hv0, d0, hd0, v1, hv1, d1, hd1, curv, hcurv,
    deriv, hderiv, dm, hdm, dp, hdp, hbeta⟩ := hcheck
  subst beta
  have hcpos := hlo.trans_le hc.1
  have hsp : (v.spatial.lo : ℝ) ≤ v.spatial.hi := hY.1.trans hY.2
  have hmem0 := eval_context_mem (parameters a.segment)
    ⟨v.spatial.lo,v.spatial.lo⟩ ⟨a.center,a.center⟩ v.r v.J a.Jcap a.useHalves _ hv0
    (lam := (a.center : ℝ)) (Y := (v.spatial.lo : ℝ)) le_rfl le_rfl le_rfl le_rfl
  have hmemd0 := eval_context_mem (parameters a.segment)
    ⟨v.spatial.lo,v.spatial.lo⟩ ⟨a.center,a.center⟩ v.r v.J a.Jcap a.useHalves _ hd0
    (lam := (a.center : ℝ)) (Y := (v.spatial.lo : ℝ)) le_rfl le_rfl le_rfl le_rfl
  have hmem1 := eval_context_mem (parameters a.segment)
    ⟨v.spatial.hi,v.spatial.hi⟩ ⟨a.center,a.center⟩ v.r v.J a.Jcap a.useHalves _ hv1
    (lam := (a.center : ℝ)) (Y := (v.spatial.hi : ℝ)) le_rfl le_rfl le_rfl le_rfl
  have hmemd1 := eval_context_mem (parameters a.segment)
    ⟨v.spatial.hi,v.spatial.hi⟩ ⟨a.center,a.center⟩ v.r v.J a.Jcap a.useHalves _ hd1
    (lam := (a.center : ℝ)) (Y := (v.spatial.hi : ℝ)) le_rfl le_rfl le_rfl le_rfl
  simp only [eval_taggedVertex, eval_taggedVertexPrime] at hmem0 hmemd0 hmem1 hmemd1
  apply endpointTransport_lower v.spatial a.activity a.center
    (loRat v0) (loRat d0) (loRat v1) (hiRat d1) (loRat curv)
    (loRat deriv) (hiRat deriv) dm dp
    (taggedVertex v.useGamma (parameters a.segment).asBand v.r v.J)
    (taggedVertexPrime v.useGamma (parameters a.segment).asBand v.r v.J)
    (taggedVertexSecond v.useGamma (parameters a.segment).asBand v.r v.J)
    (taggedVertexDot v.useGamma (parameters a.segment).asBand v.r v.J)
    hlo hc
  · intro y hy
    exact hasDerivAt_taggedVertex_Y _ _ _ _ hcpos (hYpos.trans_le hy.1).ne' (hZ _ hc _ hy)
  · intro y hy
    have hy' := interior_subset hy
    exact hasDerivAt_taggedVertexPrime_Y _ _ _ _ hcpos (hYpos.trans_le hy'.1).ne' (hZ _ hc _ hy')
  · intro y hy
    have hm := evalHull_mem (parameters a.segment) v.spatial ⟨a.center,a.center⟩
      v.r v.J a.Jcap a.useHalves _ hcurv
      (lam := (a.center : ℝ)) (Y := y) le_rfl le_rfl (interior_subset hy).1 (interior_subset hy).2
    rw [eval_taggedVertexSecond] at hm
    exact mem_loRat hm
  · exact mem_loRat hmem0
  · exact mem_loRat hmemd0
  · exact mem_loRat hmem1
  · exact mem_hiRat hmemd1
  · intro y hy mu hmu
    have hm := exp_mem_log_Icc hlo (hc.1.trans hc.2) hmu
    exact hasDerivAt_taggedVertex_mu _ _ _ _ _ _ (hZ _ hm _ hy) (hg _ hm)
  · intro y hy mu hmu
    have hm := exp_mem_log_Icc hlo (hc.1.trans hc.2) hmu
    have hen := evalHull_mem (parameters a.segment) v.spatial a.activity
      v.r v.J a.Jcap a.useHalves _ hderiv hm.1 hm.2 hy.1 hy.2
    rw [eval_taggedVertexDot _ _ _ _ _ _ _ (exp_pos mu)] at hen
    exact ⟨mem_loRat hen, mem_hiRat hen⟩
  · simpa only [Rat.cast_div] using logUpper_sound hdm (by simpa only [Rat.cast_div] using div_pos hcpos hlo)
  · simpa only [Rat.cast_div] using logUpper_sound hdp (by simpa only [Rat.cast_div] using div_pos (hcpos.trans_le hc.2) hcpos)
  · exact hlam
  · exact hY

/-- Source: `tgt:thm`; a successful CA row retains its positive-L
method or its complete real Taylor/transport lower bound. -/
theorem caLower_sound (a : Activity) (v : CACheck) {beta : Rat}
    (hcheck : caLower a v = some beta)
    (hlo : 0 < (a.activity.lo : ℝ))
    (hc : (a.center : ℝ) ∈ Icc (a.activity.lo : ℝ) (a.activity.hi : ℝ))
    (hYpos : 0 < (v.spatial.lo : ℝ))
    (hZ : ∀ lam ∈ Icc (a.activity.lo : ℝ) (a.activity.hi : ℝ),
      ∀ Y ∈ Icc (v.spatial.lo : ℝ) (v.spatial.hi : ℝ),
      zBar (parameters a.segment).asBand lam Y a.Jcap ≠ 0)
    {lam Y : ℝ} (hlam : lam ∈ Icc (a.activity.lo : ℝ) (a.activity.hi : ℝ))
    (hY : Y ∈ Icc (v.spatial.lo : ℝ) (v.spatial.hi : ℝ)) :
    if v.usePositiveL then (beta : ℝ) ≤ lBar (parameters a.segment).asBand lam Y
    else (beta : ℝ) ≤ cLower (parameters a.segment).asBand lam Y a.Jcap := by
  cases htag : v.usePositiveL with
  | true =>
      simp only [caLower, htag, Bool.coe_true, if_true] at hcheck ⊢
      split_ifs at hcheck with hs
      cases Option.some.inj hcheck
      have hm := context_mem (parameters a.segment) v.spatial a.activity 0 0 a.Jcap a.useHalves
        hs hlam.1 hlam.2 hY.1 hY.2 16
      exact mem_loRat hm
  | false =>
      simp only [caLower, htag, Bool.false_eq_true, if_false,
        Bind.bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hcheck ⊢
      obtain ⟨val, hval, slope, hslope, curv, hcurv, deriv, hderiv,
        dm, hdm, dp, hdp, hbeta⟩ := hcheck
      subst beta
      let ycenter : Rat := (v.spatial.lo+v.spatial.hi)/2
      have hcpos := hlo.trans_le hc.1
      have hmemv := eval_context_mem (parameters a.segment)
        ⟨ycenter,ycenter⟩ ⟨a.center,a.center⟩ 0 0 a.Jcap a.useHalves fC hval
        (lam := (a.center : ℝ)) (Y := (ycenter : ℝ)) le_rfl le_rfl le_rfl le_rfl
      have hmems := eval_context_mem (parameters a.segment)
        ⟨ycenter,ycenter⟩ ⟨a.center,a.center⟩ 0 0 a.Jcap a.useHalves fCp hslope
        (lam := (a.center : ℝ)) (Y := (ycenter : ℝ)) le_rfl le_rfl le_rfl le_rfl
      rw [eval_fC] at hmemv
      rw [eval_fCp] at hmems
      apply midpointTransport_lower v.spatial a.activity a.center
        (loRat val) (loRat slope) (hiRat slope) (loRat curv)
        (loRat deriv) (hiRat deriv) dm dp
        (fun l y => cLower (parameters a.segment).asBand l y a.Jcap)
        (fun l y => cLowerPrime (parameters a.segment).asBand l y a.Jcap)
        (fun l y => cLowerSecond (parameters a.segment).asBand l y a.Jcap)
        (fun l y => cLowerDot (parameters a.segment).asBand l y a.Jcap)
        hlo hc
      · intro y hy
        exact hasDerivAt_cLower_Y _ _ hcpos (hYpos.trans_le hy.1) (hZ _ hc _ hy)
      · intro y hy
        have hy' := interior_subset hy
        exact hasDerivAt_cLowerPrime_Y _ _ hcpos (hYpos.trans_le hy'.1) (hZ _ hc _ hy')
      · intro y hy
        have hm := evalHull_mem (parameters a.segment) v.spatial ⟨a.center,a.center⟩
          0 0 a.Jcap a.useHalves fCpp hcurv
          (lam := (a.center : ℝ)) (Y := y) le_rfl le_rfl (interior_subset hy).1 (interior_subset hy).2
        rw [eval_fCpp] at hm
        exact mem_loRat hm
      · exact mem_loRat hmemv
      · exact ⟨mem_loRat hmems, mem_hiRat hmems⟩
      · intro y hy mu hmu
        have hm := exp_mem_log_Icc hlo (hc.1.trans hc.2) hmu
        have hz := hZ _ hm _ hy
        apply hasDerivAt_cLower_mu
        simpa only [zBar, mul_neg, sub_neg_eq_add] using hz
      · intro y hy mu hmu
        have hm := exp_mem_log_Icc hlo (hc.1.trans hc.2) hmu
        have hen := evalHull_mem (parameters a.segment) v.spatial a.activity
          0 0 a.Jcap a.useHalves fCd hderiv hm.1 hm.2 hy.1 hy.2
        rw [eval_fCd _ _ _ _ _ _ (exp_pos mu)] at hen
        exact ⟨mem_loRat hen, mem_hiRat hen⟩
      · simpa only [Rat.cast_div] using logUpper_sound hdm
          (by simpa only [Rat.cast_div] using div_pos hcpos hlo)
      · simpa only [Rat.cast_div] using logUpper_sound hdp
          (by simpa only [Rat.cast_div] using div_pos (hcpos.trans_le hc.2) hcpos)
      · exact hlam
      · exact hY

/-- Source: every strictly positive finite AC bound implies the pointwise
nonnegative comparison consumed by the polygon's checked vertex argument. -/
theorem vertexLower_positive (a : Activity) (v : VertexCheck)
    (hcheck : optionPositive (vertexLower a v) = true)
    (hlo : 0 < (a.activity.lo : ℝ))
    (hc : (a.center : ℝ) ∈ Icc (a.activity.lo : ℝ) (a.activity.hi : ℝ))
    (hYpos : 0 < (v.spatial.lo : ℝ))
    (hZ : ∀ lam ∈ Icc (a.activity.lo : ℝ) (a.activity.hi : ℝ),
      ∀ Y ∈ Icc (v.spatial.lo : ℝ) (v.spatial.hi : ℝ),
      zBar (parameters a.segment).asBand lam Y v.J ≠ 0)
    (hg : ∀ lam ∈ Icc (a.activity.lo : ℝ) (a.activity.hi : ℝ),
      gamma (parameters a.segment).asBand lam ≠ 0)
    {lam Y : ℝ} (hlam : lam ∈ Icc (a.activity.lo : ℝ) (a.activity.hi : ℝ))
    (hY : Y ∈ Icc (v.spatial.lo : ℝ) (v.spatial.hi : ℝ)) :
    0 ≤ taggedVertex v.useGamma (parameters a.segment).asBand v.r v.J lam Y := by
  cases he : vertexLower a v with
  | none => simp only [he, optionPositive, Bool.false_eq_true] at hcheck
  | some beta =>
      have hp : (0 : Rat) < beta := by simpa only [he, optionPositive, decide_eq_true_eq] using hcheck
      have hpR : (0 : ℝ) ≤ beta := by exact_mod_cast hp.le
      exact hpR.trans (vertexLower_sound a v he hlo hc hYpos hZ hg hlam hY)

/-- Source: every strictly positive CA row yields either positive Lbar
or the real feasible lower comparison C at the retained activity and mass. -/
theorem caLower_positive (a : Activity) (v : CACheck)
    (hcheck : optionPositive (caLower a v) = true)
    (hlo : 0 < (a.activity.lo : ℝ))
    (hc : (a.center : ℝ) ∈ Icc (a.activity.lo : ℝ) (a.activity.hi : ℝ))
    (hYpos : 0 < (v.spatial.lo : ℝ))
    (hZ : ∀ lam ∈ Icc (a.activity.lo : ℝ) (a.activity.hi : ℝ),
      ∀ Y ∈ Icc (v.spatial.lo : ℝ) (v.spatial.hi : ℝ),
      zBar (parameters a.segment).asBand lam Y a.Jcap ≠ 0)
    {lam Y : ℝ} (hlam : lam ∈ Icc (a.activity.lo : ℝ) (a.activity.hi : ℝ))
    (hY : Y ∈ Icc (v.spatial.lo : ℝ) (v.spatial.hi : ℝ)) :
    0 ≤ lBar (parameters a.segment).asBand lam Y ∨
      0 ≤ cLower (parameters a.segment).asBand lam Y a.Jcap := by
  cases he : caLower a v with
  | none => simp only [he, optionPositive, Bool.false_eq_true] at hcheck
  | some beta =>
      have hp : (0 : Rat) < beta := by simpa only [he, optionPositive, decide_eq_true_eq] using hcheck
      have hnum := caLower_sound a v he hlo hc hYpos hZ hlam hY
      have hpR : (0 : ℝ) ≤ beta := by exact_mod_cast hp.le
      cases htag : v.usePositiveL
      · right
        exact hpR.trans (by simpa only [htag, Bool.false_eq_true, if_false] using hnum)
      · left
        exact hpR.trans (by simpa only [htag, Bool.coe_true, if_true] using hnum)

end Erdos993Lean.Analytic.HandVariance.Compute
