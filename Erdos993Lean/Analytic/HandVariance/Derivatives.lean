import Erdos993Lean.Analytic.HandVariance.Calculus
import Erdos993Lean.Analytic.HandVariance.Normalized

/-!
# Parent derivatives in the hand variance proof

Source: `for_tong/TWIN_v1.8/apx_hand.tex`, Lemma `tgt:lem:dY`,
in `ProofRuns/2026-09-28_analytic_large_n/LEAN`. Derivative formulas
retain the exact activity and parent log-mass; no sign comparison is assumed.
-/

namespace Erdos993Lean.Analytic.HandVariance

open Real Reserve

/-- Source: `tgt:lem:dY`, `e_λ' = e_λ`. -/
theorem hasDerivAt_parentE_Y (lam Y : ℝ) :
    HasDerivAt (parentE lam) (parentE lam Y) Y := by
  exact (Real.hasDerivAt_exp Y).div_const lam

/-- Source: `tgt:lem:dY`, `k' = k ϑ`. -/
theorem hasDerivAt_parentK_Y {lam Y : ℝ} (hlam : 0 < lam) :
    HasDerivAt (parentK lam) (parentK lam Y * parentTheta lam Y) Y := by
  have hphi : lmass lam Y ≠ 0 := (Reserve.lmass_pos hlam Y).ne'
  convert (hasDerivAt_msg_Y hlam).div (hasDerivAt_lmass_Y hlam) hphi using 1
  dsimp [parentK, parentTheta]
  field_simp <;> ring

/-- Source: `tgt:lem:dY`, `ϑ' = k ϑ - p(1-p)`. -/
theorem hasDerivAt_parentTheta_Y {lam Y : ℝ} (hlam : 0 < lam) :
    HasDerivAt (parentTheta lam)
      (parentK lam Y * parentTheta lam Y - msg lam Y * (1 - msg lam Y)) Y := by
  convert ((hasDerivAt_parentK_Y hlam).add (hasDerivAt_msg_Y hlam)).sub_const 1 using 1
  ring

/-- Source: `tgt:lem:dY`, `ϑ > 0`, from `log(1+R) < R` for `R>0`. -/
theorem parentTheta_pos {lam Y : ℝ} (hlam : 0 < lam) : 0 < parentTheta lam Y := by
  let R : ℝ := lam * exp (-Y)
  have hR : 0 < R := mul_pos hlam (exp_pos _)
  have hd : 0 < 1 + R := by linarith
  have hl : log (1 + R) < R := by
    have := Real.log_lt_sub_one_of_pos hd (show 1 + R ≠ 1 by linarith)
    linarith
  have hphi : 0 < log (1 + R) := Real.log_pos (by linarith)
  have hk : 1 - msg lam Y < parentK lam Y := by
    unfold parentK
    rw [lt_div_iff₀ (Reserve.lmass_pos hlam Y)]
    change (1 - R / (1 + R)) * log (1 + R) < R / (1 + R)
    field_simp
    nlinarith
  unfold parentTheta
  linarith

/-- Source: `tgt:lem:dY`, formula for `ĥ'`. -/
noncomputable def hPrime (c : Band) (lam Y : ℝ) : ℝ :=
  msg lam Y * (1 - msg lam Y) + gamma c lam * parentK lam Y * parentTheta lam Y

/-- Source: `tgt:lem:dY`, formula for `ĥ''`. -/
noncomputable def hSecond (c : Band) (lam Y : ℝ) : ℝ :=
  -msg lam Y * (1 - msg lam Y) * (1 - 2 * msg lam Y) +
  gamma c lam * parentK lam Y *
    (parentTheta lam Y ^ 2 + parentK lam Y * parentTheta lam Y - msg lam Y * (1 - msg lam Y))

/-- Source: `tgt:lem:dY`, first derivative of `ĥ`. -/
theorem hasDerivAt_hHat_Y (c : Band) {lam Y : ℝ} (hlam : 0 < lam) :
    HasDerivAt (hHat c lam) (hPrime c lam Y) Y := by
  have h := ((hasDerivAt_const Y (1 : ℝ)).sub (hasDerivAt_msg_Y hlam)).add
    ((hasDerivAt_parentK_Y hlam).const_mul (gamma c lam))
  convert h using 1
  unfold hPrime
  ring

/-- Source: `tgt:lem:dY`, second derivative of `ĥ`. -/
theorem hasDerivAt_hPrime_Y (c : Band) {lam Y : ℝ} (hlam : 0 < lam) :
    HasDerivAt (hPrime c lam) (hSecond c lam Y) Y := by
  have hp := hasDerivAt_msg_Y (Y := Y) hlam
  have hk := hasDerivAt_parentK_Y (Y := Y) hlam
  have ht := hasDerivAt_parentTheta_Y (Y := Y) hlam
  have h := (hp.mul ((hasDerivAt_const Y (1 : ℝ)).sub hp)).add
    (((hk.const_mul (gamma c lam)).mul ht))
  convert h using 1
  dsimp [hSecond]
  ring

/-- Source: `tgt:lem:dY`, formula for `N'`. -/
noncomputable def nPrime (c : Band) (lam Y : ℝ) : ℝ :=
  -hPrime c lam Y + alpha c lam * parentTheta lam Y / parentK lam Y

/-- Source: `tgt:lem:dY`, formula for `N''`. -/
noncomputable def nSecond (c : Band) (lam Y : ℝ) : ℝ :=
  -hSecond c lam Y + alpha c lam *
    (parentTheta lam Y - msg lam Y * (1 - msg lam Y) / parentK lam Y -
      parentTheta lam Y ^ 2 / parentK lam Y)

/-- Source: `tgt:lem:dY`, first derivative of `N`. -/
theorem hasDerivAt_nTerm_Y (c : Band) {lam Y : ℝ} (hlam : 0 < lam) :
    HasDerivAt (nTerm c lam) (nPrime c lam Y) Y := by
  have hk : parentK lam Y ≠ 0 :=
    (div_pos (Reserve.msg_pos hlam Y) (Reserve.lmass_pos hlam Y)).ne'
  have h := ((hasDerivAt_const Y (capA c lam)).sub (hasDerivAt_hHat_Y c hlam)).sub
    ((hasDerivAt_const Y (alpha c lam)).div (hasDerivAt_parentK_Y hlam) hk)
  convert h using 1
  unfold nPrime
  field_simp
  ring

/-- Source: `tgt:lem:dY`, second derivative of `N`. -/
theorem hasDerivAt_nPrime_Y (c : Band) {lam Y : ℝ} (hlam : 0 < lam) :
    HasDerivAt (nPrime c lam) (nSecond c lam Y) Y := by
  have hk : parentK lam Y ≠ 0 :=
    (div_pos (Reserve.msg_pos hlam Y) (Reserve.lmass_pos hlam Y)).ne'
  have h := (hasDerivAt_hPrime_Y c hlam).neg.add
    (((hasDerivAt_parentTheta_Y hlam).const_mul (alpha c lam)).div
      (hasDerivAt_parentK_Y hlam) hk)
  convert h using 1
  dsimp [nSecond]
  field_simp

/-- Source: `tgt:lem:dY`, formula for `L̄'`. -/
noncomputable def lPrime (c : Band) (lam Y : ℝ) : ℝ :=
  gamma c lam * parentE lam Y - hHat c lam Y - hPrime c lam Y * Y

/-- Source: `tgt:lem:dY`, formula for `L̄''`. -/
noncomputable def lSecond (c : Band) (lam Y : ℝ) : ℝ :=
  gamma c lam * parentE lam Y - 2 * hPrime c lam Y - hSecond c lam Y * Y

/-- Source: `tgt:lem:dY`, first derivative of `L̄`. -/
theorem hasDerivAt_lBar_Y (c : Band) {lam Y : ℝ} (hlam : 0 < lam) :
    HasDerivAt (lBar c lam) (lPrime c lam Y) Y := by
  have h := ((hasDerivAt_parentE_Y lam Y).const_mul (gamma c lam)).sub
    ((hasDerivAt_hHat_Y c hlam).mul (hasDerivAt_id Y))
  convert h using 1
  dsimp [lPrime]
  ring

/-- Source: `tgt:lem:dY`, second derivative of `L̄`. -/
theorem hasDerivAt_lPrime_Y (c : Band) {lam Y : ℝ} (hlam : 0 < lam) :
    HasDerivAt (lPrime c lam) (lSecond c lam Y) Y := by
  have h := (((hasDerivAt_parentE_Y lam Y).const_mul (gamma c lam)).sub
    (hasDerivAt_hHat_Y c hlam)).sub ((hasDerivAt_hPrime_Y c hlam).mul (hasDerivAt_id Y))
  convert h using 1
  dsimp [lSecond]
  ring

/-- Source: `tgt:lem:dY`, `Z̄' = J L̄'` at fixed child coordinate. -/
theorem hasDerivAt_zBar_Y (c : Band) (J : ℝ) {lam Y : ℝ} (hlam : 0 < lam) :
    HasDerivAt (fun x => zBar c lam x J) (J * lPrime c lam Y) Y := by
  exact ((hasDerivAt_lBar_Y c hlam).const_mul J).const_add (gamma c lam)


/-- Source: `tgt:lem:dY`, quotient-rule jet, used for `N/Y` and `Jh²/Z`. -/
noncomputable def quotientJet1 (u u₁ v v₁ : ℝ) : ℝ := (u₁*v-u*v₁)/v^2

/-- Source: `tgt:lem:dY`, second quotient-rule jet. -/
noncomputable def quotientJet2 (u u₁ u₂ v v₁ v₂ : ℝ) : ℝ :=
  u₂/v - (2*u₁*v₁+u*v₂)/v^2 + 2*u*v₁^2/v^3

/-- Source: `tgt:lem:dY`, quotient rule with its nonzero denominator retained. -/
theorem hasDerivAt_quotientJet1 {f f₁ f₂ g g₁ g₂ : ℝ → ℝ} {x : ℝ}
    (hf : HasDerivAt f (f₁ x) x) (hf₁ : HasDerivAt f₁ (f₂ x) x)
    (hg : HasDerivAt g (g₁ x) x) (hg₁ : HasDerivAt g₁ (g₂ x) x)
    (hgz : g x ≠ 0) :
    HasDerivAt (fun t => quotientJet1 (f t) (f₁ t) (g t) (g₁ t))
      (quotientJet2 (f x) (f₁ x) (f₂ x) (g x) (g₁ x) (g₂ x)) x := by
  have h := ((hf₁.mul hg).sub (hf.mul hg₁)).div (hg.pow 2) (pow_ne_zero 2 hgz)
  convert h using 1
  dsimp [quotientJet1, quotientJet2]
  field_simp [hgz] <;> ring

/-- Source: `tgt:lem:dY`, the first derivative of `N/Y`. -/
noncomputable def nOverYPrime (c : Band) (lam Y : ℝ) : ℝ :=
  (nPrime c lam Y * Y - nTerm c lam Y)/Y^2

/-- Source: `tgt:lem:dY`, the second derivative of `N/Y`. -/
noncomputable def nOverYSecond (c : Band) (lam Y : ℝ) : ℝ :=
  (nSecond c lam Y*Y^2-2*nPrime c lam Y*Y+2*nTerm c lam Y)/Y^3

/-- Source: `tgt:lem:dY`, quotient-rule derivative of `N/Y`. -/
theorem hasDerivAt_nOverY (c : Band) {lam Y : ℝ} (hlam : 0 < lam) (hY : Y ≠ 0) :
    HasDerivAt (fun y => nTerm c lam y/y) (nOverYPrime c lam Y) Y := by
  simpa only [nOverYPrime, id_eq, mul_one] using
    (hasDerivAt_nTerm_Y c hlam).div (hasDerivAt_id Y) hY

/-- Source: `tgt:lem:dY`, exact second derivative of `N/Y`. -/
theorem hasDerivAt_nOverYPrime (c : Band) {lam Y : ℝ} (hlam : 0 < lam) (hY : Y ≠ 0) :
    HasDerivAt (nOverYPrime c lam) (nOverYSecond c lam Y) Y := by
  have h := hasDerivAt_quotientJet1 (g := id) (g₁ := fun _ => 1) (g₂ := fun _ => 0)
    (hasDerivAt_nTerm_Y c hlam)
    (hasDerivAt_nPrime_Y c hlam) (hasDerivAt_id Y) (hasDerivAt_const Y (1:ℝ)) hY
  simp only [quotientJet1, id_eq, mul_one] at h
  convert h using 1
  dsimp [quotientJet2, nOverYSecond]
  field_simp [hY]
  ring

/-- Source: `tgt:lem:dY`, the derivative of `J ĥ²/Z̄` at fixed J. -/
noncomputable def gPrime (c : Band) (lam Y J : ℝ) : ℝ :=
  J*(2*hHat c lam Y*hPrime c lam Y*zBar c lam Y J -
    hHat c lam Y^2*(J*lPrime c lam Y))/(zBar c lam Y J)^2

/-- Source: `tgt:lem:dY`, the exact second derivative of `J ĥ²/Z̄`. -/
noncomputable def gSecond (c : Band) (lam Y J : ℝ) : ℝ :=
  J*((2*(hPrime c lam Y)^2+2*hHat c lam Y*hSecond c lam Y)/zBar c lam Y J -
    4*hHat c lam Y*hPrime c lam Y*(J*lPrime c lam Y)/(zBar c lam Y J)^2 -
    (hHat c lam Y)^2*(J*lSecond c lam Y)/(zBar c lam Y J)^2 +
    2*(hHat c lam Y)^2*(J*lPrime c lam Y)^2/(zBar c lam Y J)^3)

/-- Source: `tgt:lem:dY`, quotient rule for the reserve correction. -/
theorem hasDerivAt_gTerm (c : Band) (J : ℝ) {lam Y : ℝ} (hlam : 0 < lam)
    (hZ : zBar c lam Y J ≠ 0) :
    HasDerivAt (fun y => J*(hHat c lam y)^2/zBar c lam y J) (gPrime c lam Y J) Y := by
  have h := (((hasDerivAt_hHat_Y c hlam).pow 2).const_mul J).div
    (hasDerivAt_zBar_Y c J hlam) hZ
  convert h using 1
  dsimp [gPrime]
  ring

/-- Source: `tgt:lem:dY`, second quotient rule for the reserve correction. -/
theorem hasDerivAt_gPrime (c : Band) (J : ℝ) {lam Y : ℝ} (hlam : 0 < lam)
    (hZ : zBar c lam Y J ≠ 0) :
    HasDerivAt (fun y => gPrime c lam y J) (gSecond c lam Y J) Y := by
  let u := fun y => J*(hHat c lam y)^2
  let u₁ := fun y => 2*J*hHat c lam y*hPrime c lam y
  let u₂ := fun y => 2*J*((hPrime c lam y)^2+hHat c lam y*hSecond c lam y)
  have hu : HasDerivAt u (u₁ Y) Y := by
    convert ((hasDerivAt_hHat_Y c hlam).pow 2).const_mul J using 1
    dsimp [u₁]
    ring
  have hu₁ : HasDerivAt u₁ (u₂ Y) Y := by
    convert ((hasDerivAt_hHat_Y c hlam).mul (hasDerivAt_hPrime_Y c hlam)).const_mul (2*J) using 1
    · funext y
      dsimp [u₁]
      ring
    · dsimp [u₂]
      ring
  have hz₁ : HasDerivAt (fun y => J*lPrime c lam y) (J*lSecond c lam Y) Y :=
    (hasDerivAt_lPrime_Y c hlam).const_mul J
  have h := hasDerivAt_quotientJet1 (g := fun y => zBar c lam y J)
    (g₁ := fun y => J*lPrime c lam y) (g₂ := fun y => J*lSecond c lam y)
    hu hu₁ (hasDerivAt_zBar_Y c J hlam) hz₁ hZ
  convert h using 1
  · dsimp [gPrime, quotientJet1, u, u₁]
    funext y
    ring
  · dsimp [gSecond, quotientJet2, u, u₁, u₂]
    field_simp [hZ] <;> ring

/-- Source: `tgt:lem:dY`, exact first derivative of the vertex function. -/
noncomputable def vertexAPrime (c : Band) (lam Y r J : ℝ) : ℝ :=
  alpha c lam*parentE lam Y+nOverYPrime c lam Y-gPrime c lam Y J

/-- Source: `tgt:lem:dY`, exact second derivative of the vertex function. -/
noncomputable def vertexASecond (c : Band) (lam Y r J : ℝ) : ℝ :=
  alpha c lam*parentE lam Y+nOverYSecond c lam Y-gSecond c lam Y J

/-- Source: `tgt:lem:dY`, first derivative used in each AC endpoint check. -/
theorem hasDerivAt_vertexA_Y (c : Band) (r J : ℝ) {lam Y : ℝ} (hlam : 0 < lam)
    (hY : Y ≠ 0) (hZ : zBar c lam Y J ≠ 0) :
    HasDerivAt (fun y => vertexA c lam y r J) (vertexAPrime c lam Y r J) Y := by
  exact ((((hasDerivAt_parentE_Y lam Y).const_mul (alpha c lam)).add
    (hasDerivAt_nOverY c hlam hY)).add_const (alpha c lam*r)).sub
    (hasDerivAt_gTerm c J hlam hZ)

/-- Source: `tgt:lem:dY`, second derivative used in each AC curvature check. -/
theorem hasDerivAt_vertexAPrime_Y (c : Band) (r J : ℝ) {lam Y : ℝ} (hlam : 0 < lam)
    (hY : Y ≠ 0) (hZ : zBar c lam Y J ≠ 0) :
    HasDerivAt (fun y => vertexAPrime c lam y r J) (vertexASecond c lam Y r J) Y := by
  exact (((hasDerivAt_parentE_Y lam Y).const_mul (alpha c lam)).add
    (hasDerivAt_nOverYPrime c hlam hY)).sub (hasDerivAt_gPrime c J hlam hZ)

/-- Source: `tgt:lem:dY`, first derivative of the gamma-denominator function. -/
noncomputable def vertexAgammaPrime (c : Band) (lam Y r J : ℝ) : ℝ :=
  alpha c lam*parentE lam Y+nOverYPrime c lam Y-2*J*hHat c lam Y*hPrime c lam Y/gamma c lam

/-- Source: `tgt:lem:dY`, second derivative of the gamma-denominator function. -/
noncomputable def vertexAgammaSecond (c : Band) (lam Y r J : ℝ) : ℝ :=
  alpha c lam*parentE lam Y+nOverYSecond c lam Y -
    J*(2*(hPrime c lam Y)^2+2*hHat c lam Y*hSecond c lam Y)/gamma c lam

/-- Source: `tgt:lem:dY`, first derivative of the comparison majorant. -/
theorem hasDerivAt_vertexAgamma_Y (c : Band) (r J : ℝ) {lam Y : ℝ}
    (hlam : 0 < lam) (hY : Y ≠ 0) :
    HasDerivAt (fun y => vertexAgamma c lam y r J) (vertexAgammaPrime c lam Y r J) Y := by
  have h := ((((hasDerivAt_parentE_Y lam Y).const_mul (alpha c lam)).add
    (hasDerivAt_nOverY c hlam hY)).add_const (alpha c lam*r)).sub
    ((((hasDerivAt_hHat_Y c hlam).pow 2).const_mul J).div_const (gamma c lam))
  convert h using 1
  unfold vertexAgammaPrime
  ring

/-- Source: `tgt:lem:dY`, second derivative of the comparison majorant. -/
theorem hasDerivAt_vertexAgammaPrime_Y (c : Band) (r J : ℝ) {lam Y : ℝ}
    (hlam : 0 < lam) (hY : Y ≠ 0) :
    HasDerivAt (fun y => vertexAgammaPrime c lam y r J) (vertexAgammaSecond c lam Y r J) Y := by
  have h := (((hasDerivAt_parentE_Y lam Y).const_mul (alpha c lam)).add
    (hasDerivAt_nOverYPrime c hlam hY)).sub
    ((((hasDerivAt_hHat_Y c hlam).mul (hasDerivAt_hPrime_Y c hlam)).const_mul (2*J)).div_const (gamma c lam))
  convert h using 1
  · funext y
    dsimp [vertexAgammaPrime]
    ring
  · dsimp [vertexAgammaSecond]
    ring

end Erdos993Lean.Analytic.HandVariance
