import Erdos993Lean.Analytic.HandVariance.ActivityDerivatives

/-!
# Derivatives of the feasible CA lower function

Source: TWIN v1.8 Appendix N.4, `tgt:lem:dY` and `tgt:lem:dmu`.
Positive parent log-mass and nonzero cap denominator are retained.
-/

namespace Erdos993Lean.Analytic.HandVariance
open Real Reserve

/-- Source: `tgt:lem:dY`, numerator n in the entropy lower function. -/
noncomputable def eNumerator (lam Y : ℝ) : ℝ :=
  log lam-log (exp Y-1)-1/parentK lam Y
/-- Source: `tgt:lem:dY`, derivative n′. -/
noncomputable def eNumeratorPrime (lam Y : ℝ) : ℝ :=
  -exp Y/(exp Y-1)+parentTheta lam Y/parentK lam Y
/-- Source: `tgt:lem:dY`, derivative n″. -/
noncomputable def eNumeratorSecond (lam Y : ℝ) : ℝ :=
  exp Y/(exp Y-1)^2+parentTheta lam Y-
  msg lam Y*(1-msg lam Y)/parentK lam Y-(parentTheta lam Y)^2/parentK lam Y

/-- Source: `tgt:lem:dY`, differentiating the feasibility numerator. -/
theorem hasDerivAt_eNumerator_Y {lam Y : ℝ} (hlam : 0 < lam) (hY : 0 < Y) :
    HasDerivAt (eNumerator lam) (eNumeratorPrime lam Y) Y := by
  have he : exp Y-1 ≠ 0 := (sub_pos.mpr (Real.one_lt_exp_iff.mpr hY)).ne'
  have hk := (parentK_pos hlam Y).ne'
  have h := ((hasDerivAt_const Y (log lam)).sub
    (((Real.hasDerivAt_exp Y).sub_const 1).log he)).sub
    ((hasDerivAt_const Y (1:ℝ)).div (hasDerivAt_parentK_Y hlam) hk)
  convert h using 1
  dsimp [eNumeratorPrime]
  field_simp
  ring

/-- Source: `tgt:lem:dY`, differentiating n′ exactly. -/
theorem hasDerivAt_eNumeratorPrime_Y {lam Y : ℝ} (hlam : 0 < lam) (hY : 0 < Y) :
    HasDerivAt (eNumeratorPrime lam) (eNumeratorSecond lam Y) Y := by
  have he : exp Y-1 ≠ 0 := (sub_pos.mpr (Real.one_lt_exp_iff.mpr hY)).ne'
  have hk := (parentK_pos hlam Y).ne'
  have h := (((Real.hasDerivAt_exp Y).neg).div
    ((Real.hasDerivAt_exp Y).sub_const 1) he).add
    ((hasDerivAt_parentTheta_Y hlam).div (hasDerivAt_parentK_Y hlam) hk)
  convert h using 1
  dsimp [eNumeratorSecond]
  field_simp
  ring

/-- Source: `tgt:lem:dY`, E₋′. -/
noncomputable def eMinusPrime (lam Y : ℝ) : ℝ :=
  parentE lam Y+(eNumeratorPrime lam Y*Y-eNumerator lam Y)/Y^2
/-- Source: `tgt:lem:dY`, E₋″. -/
noncomputable def eMinusSecond (lam Y : ℝ) : ℝ :=
  parentE lam Y+(eNumeratorSecond lam Y*Y^2-2*eNumeratorPrime lam Y*Y+
    2*eNumerator lam Y)/Y^3

/-- Source: `tgt:lem:dY`, derivative of E₋ at its actual activity. -/
theorem hasDerivAt_eMinus_Y {lam Y : ℝ} (hlam : 0 < lam) (hY : 0 < Y) :
    HasDerivAt (eMinus lam) (eMinusPrime lam Y) Y := by
  simpa only [eMinus, eMinusPrime, eNumerator, id_eq, mul_one] using
    (hasDerivAt_parentE_Y lam Y).add
      ((hasDerivAt_eNumerator_Y hlam hY).div (hasDerivAt_id Y) hY.ne')

/-- Source: `tgt:lem:dY`, second derivative used in every CA curvature enclosure. -/
theorem hasDerivAt_eMinusPrime_Y {lam Y : ℝ} (hlam : 0 < lam) (hY : 0 < Y) :
    HasDerivAt (eMinusPrime lam) (eMinusSecond lam Y) Y := by
  have hq := hasDerivAt_quotientJet1 (g := id) (g₁ := fun _ => 1) (g₂ := fun _ => 0)
    (hasDerivAt_eNumerator_Y hlam hY)
    (hasDerivAt_eNumeratorPrime_Y hlam hY) (hasDerivAt_id Y)
    (hasDerivAt_const Y (1:ℝ)) hY.ne'
  simp only [quotientJet1, id_eq, mul_one] at hq
  have h := (hasDerivAt_parentE_Y lam Y).add hq
  convert h using 1
  unfold eMinusSecond quotientJet2
  field_simp
  ring

/-- Source: `tgt:lem:dY`, exact first derivative of C. -/
noncomputable def cLowerPrime (c : Band) (lam Y Jcap : ℝ) : ℝ :=
  alpha c lam*eMinusPrime lam Y+
    (gamma c lam)^2*lPrime c lam Y/(gamma c lam+Jcap*lBar c lam Y)^2
/-- Source: `tgt:lem:dY`, exact second derivative of C. -/
noncomputable def cLowerSecond (c : Band) (lam Y Jcap : ℝ) : ℝ :=
  alpha c lam*eMinusSecond lam Y-
    2*Jcap*(gamma c lam)^2*(lPrime c lam Y)^2/(gamma c lam+Jcap*lBar c lam Y)^3+
    (gamma c lam)^2*lSecond c lam Y/(gamma c lam+Jcap*lBar c lam Y)^2

/-- Source: `tgt:lem:dY`, first CA lower-function derivative. -/
theorem hasDerivAt_cLower_Y (c : Band) (Jcap : ℝ) {lam Y : ℝ}
    (hlam : 0 < lam) (hY : 0 < Y) (hZ : gamma c lam+Jcap*lBar c lam Y ≠ 0) :
    HasDerivAt (fun y => cLower c lam y Jcap) (cLowerPrime c lam Y Jcap) Y := by
  have hz : gamma c lam-Jcap*(-lBar c lam Y) ≠ 0 := by simpa using hZ
  have h := ((hasDerivAt_eMinus_Y hlam hY).const_mul (alpha c lam)).sub
    ((((hasDerivAt_lBar_Y c hlam).neg).const_mul (gamma c lam)).div
      ((hasDerivAt_const Y (gamma c lam)).sub
        (((hasDerivAt_lBar_Y c hlam).neg).const_mul Jcap)) hz)
  convert h using 1
  dsimp [cLowerPrime]
  simp only [mul_neg, sub_neg_eq_add, neg_neg]
  generalize hzEq : gamma c lam + Jcap*lBar c lam Y = z at hZ ⊢
  field_simp [hZ]
  rw [← hzEq]
  ring

/-- Source: `tgt:lem:dY`, second CA lower-function derivative. -/
theorem hasDerivAt_cLowerPrime_Y (c : Band) (Jcap : ℝ) {lam Y : ℝ}
    (hlam : 0 < lam) (hY : 0 < Y) (hZ : gamma c lam+Jcap*lBar c lam Y ≠ 0) :
    HasDerivAt (fun y => cLowerPrime c lam y Jcap) (cLowerSecond c lam Y Jcap) Y := by
  have hd := ((hasDerivAt_lBar_Y c (Y := Y) hlam).const_mul Jcap).const_add (gamma c lam)
  have h := ((hasDerivAt_eMinusPrime_Y hlam hY).const_mul (alpha c lam)).add
    (((hasDerivAt_lPrime_Y c hlam).const_mul ((gamma c lam)^2)).div
      (hd.pow 2) (pow_ne_zero 2 hZ))
  convert h using 1
  dsimp [cLowerSecond]
  generalize hzEq : gamma c lam + Jcap*lBar c lam Y = z at hZ ⊢
  field_simp [hZ]
  rw [← hzEq]
  ring

/-- Source: `tgt:lem:dmu`, the signed activity derivative of E₋. -/
noncomputable def eMinusDot (lam Y : ℝ) : ℝ :=
  -parentE lam Y+(1-parentTheta lam Y/parentK lam Y)/Y

/-- Source: `tgt:lem:dmu`, exact E₋ activity derivative. -/
theorem hasDerivAt_eMinus_mu (Y mu : ℝ) :
    HasDerivAt (fun x => eMinus (exp x) Y) (eMinusDot (exp mu) Y) mu := by
  have hk := (parentK_pos (exp_pos mu) Y).ne'
  have hn := ((hasDerivAt_id mu).sub_const (log (exp Y-1))).sub
    ((hasDerivAt_const mu (1:ℝ)).div (hasDerivAt_parentK_mu Y mu) hk)
  have h := (hasDerivAt_parentE_mu Y mu).add (hn.div_const Y)
  convert h using 1
  · funext x
    dsimp [eMinus]
    rw [Real.log_exp]
  · unfold eMinusDot
    field_simp
    ring

/-- Source: `tgt:lem:dmu`, the signed activity derivative used by CA transport. -/
noncomputable def cLowerDot (c : Band) (lam Y Jcap : ℝ) : ℝ :=
  alphaDot c lam*eMinus lam Y+alpha c lam*eMinusDot lam Y+
    (gammaDot c lam*Jcap*(-lBar c lam Y)^2-(gamma c lam)^2*(-lDot c lam Y))/
      (gamma c lam-Jcap*(-lBar c lam Y))^2

/-- Source: `tgt:lem:dmu`, exact activity derivative of C. -/
theorem hasDerivAt_cLower_mu (c : Band) (Y Jcap mu : ℝ)
    (hZ : gamma c (exp mu)-Jcap*(-lBar c (exp mu) Y) ≠ 0) :
    HasDerivAt (fun x => cLower c (exp x) Y Jcap) (cLowerDot c (exp mu) Y Jcap) mu := by
  have hg := hasDerivAt_gamma_mu c mu
  have hl := (hasDerivAt_lBar_mu c Y mu).neg
  have h := ((hasDerivAt_alpha_mu c mu).mul (hasDerivAt_eMinus_mu Y mu)).sub
    ((hg.mul hl).div (hg.sub (hl.const_mul Jcap)) hZ)
  convert h using 1
  dsimp [cLowerDot]
  ring

end Erdos993Lean.Analytic.HandVariance

#print axioms Erdos993Lean.Analytic.HandVariance.hasDerivAt_cLowerPrime_Y
#print axioms Erdos993Lean.Analytic.HandVariance.hasDerivAt_cLower_mu
