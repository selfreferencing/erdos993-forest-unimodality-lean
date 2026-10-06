import Erdos993Lean.Analytic.V22.Analysis.BonusRangeBounds
import Erdos993Lean.Analytic.V22.Analysis.LinearizedLowerBounds
import Erdos993Lean.Analytic.V22.Analysis.CoefficientMonotonicity

/-!
# Closed lower-range remainder at the actual fiber size

Source: Lemma 4.11(L). The only denominator premise is the stated `betaL>0`.
In particular `ebar<1`, the linearized coefficients and all root comparisons
are derived internally. The lower remainder is the native Proposition4.6
object, not a substitute bound asserted as a final hypothesis.
-/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

theorem closed_template_shift_upper {M : ℕ} {mu M0 : ℝ}
    (hM : 8 ≤ M) (hmu : 0 < mu) (hM0 : 8 ≤ M0) (hM0M : M0 ≤ (M : ℝ))
    (side : ActivityOneSide) :
    activityOneLambda M mu side ≤ V22.lambdaT ((M : ℝ) / mu) + V22.hbar M0 := by
  have hp0 : 0 < M0 := by linarith
  have hk := activityOneK_bounds hM side
  have hbar := template_kbar_antitone hp0 hM0M
  have hden : 0 < (M : ℝ) + 3 := by positivity
  have hnum : 0 ≤ (77 / 20 : ℝ) + 10 / M0 := by positivity
  have hfrac : activityOneK M side / ((M : ℝ) + 3) ≤
      ((77 / 20 : ℝ) + 10 / M0) / (M0 + 3) :=
    (div_le_div_of_nonneg_right (hk.2.trans hbar) hden.le).trans
      (div_le_div_of_nonneg_left hnum (by linarith) (by linarith))
  rw [activityOneLambda_shift (by omega : 1 ≤ M) hmu side]
  unfold V22.lambdaT V22.hbar V22.kbar activityOneLambda_t
  linarith

theorem closed_sigma_comparison {M : ℕ} {r rm mu M0 : ℝ}
    (hM : 8 ≤ M) (hmu : 0 < mu) (hr0 : 0 ≤ r) (hrrm : r ≤ rm)
    (hrmh : rm ≤ 1 / 2) (hM0 : 8 ≤ M0) (hM0M : M0 ≤ (M : ℝ)) :
    max (rootMap (activityOneLambda M mu .L + V22.eL r ((M : ℝ) + 2))) 0 ≤
      V22.sigma0 ((M : ℝ) / mu) M0 + V22.eL r ((M : ℝ) + 2) := by
  have hN : 10 ≤ (M : ℝ) + 2 := by exact_mod_cast (show 10 ≤ M + 2 by omega)
  have he := bonusRange_eL_nonneg (by linarith : 0 < (M : ℝ) + 2) hr0
    (by linarith : r < 1)
  have hTL := closed_template_shift_upper hM hmu hM0 hM0M .L
  have hAdd : activityOneLambda M mu .L + V22.eL r ((M : ℝ) + 2) ≤
      V22.lambdaT ((M : ℝ) / mu) + V22.hbar M0 + V22.eL r ((M : ℝ) + 2) := by linarith
  have hroot := rootMap_monotone hAdd
  have hshift := rootMap_shift_le
    (V22.lambdaT ((M : ℝ) / mu) + V22.hbar M0) (V22.eL r ((M : ℝ) + 2)) he
  have hs0 : 0 ≤ V22.sigma0 ((M : ℝ) / mu) M0 := le_max_right _ _
  have hsbase : rootMap (V22.lambdaT ((M : ℝ) / mu) + V22.hbar M0) ≤
      V22.sigma0 ((M : ℝ) / mu) M0 := by
    unfold V22.sigma0 V22.positivePart
    rw [shared_rootMap_eq]
    exact le_max_left _ _
  exact max_le (by linarith) (add_nonneg hs0 he)

/-- The actual pointwise error lies below the source cap at every `nu<=nu_m`. -/
theorem closed_eL_le_ebar {r rm N nm : ℝ} (hN : 10 ≤ N) (hr0 : 0 ≤ r)
    (hrrm : r ≤ rm) (hrmh : rm ≤ 1 / 2) (hcap : activityNu r N ≤ nm) :
    V22.eL r N ≤ V22.ebar N rm nm := by
  have hnu := activityNu_nonneg (N := N) hr0
  obtain ⟨hA, hB⟩ := coefficient_alpha_nonneg hN (hr0.trans hrrm) hrmh
  have hsq : activityNu r N ^ 2 ≤ nm ^ 2 := (sq_le_sq₀ hnu (hnu.trans hcap)).2 hcap
  have hpoly : V22.alpha1 N rm * activityNu r N + V22.alpha2 N rm * activityNu r N ^ 2 ≤
      V22.alpha1 N rm * nm + V22.alpha2 N rm * nm ^ 2 :=
    add_le_add (mul_le_mul_of_nonneg_left hcap hA) (mul_le_mul_of_nonneg_left hsq hB)
  have hBound := linearized_eL_upper hN hr0 hrrm hrmh
  unfold V22.ebar
  apply (le_div_iff₀ (show 0 < N + 1 by linarith)).2
  nlinarith [hBound.trans hpoly]

/-- Positivity of the printed denominator itself licenses the needed cap. -/
theorem closed_betaL_forces_ebar {t N M0 rm nm : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ rm) (hrmh : rm ≤ 1 / 2) (hnm : 0 ≤ nm)
    (hbeta : 0 < V22.betaL t N M0 rm nm) : V22.ebar N rm nm < 1 := by
  obtain ⟨hA, hB⟩ := coefficient_alpha_nonneg hN hr0 hrmh
  have hn : 0 < N := by linarith
  have hs : 0 ≤ V22.sigma0 t M0 := le_max_right _ _
  have hterm : 0 ≤ (2 * (V22.alpha1 N rm) ^ 2 +
      4 * V22.alpha1 N rm * V22.alpha2 N rm * nm +
      2 * (V22.alpha2 N rm) ^ 2 * nm ^ 2) / (N + 1) := by positivity
  unfold V22.betaL at hbeta
  have hsB := mul_nonneg hs hB
  by_contra! hE
  have hNeg := mul_nonneg (show 0 ≤ N - 1 by linarith)
    (show 0 ≤ V22.ebar N rm nm - 1 by linarith)
  nlinarith

/-- Full source Lemma4.11(L), with its sole stated denominator guard. -/
theorem source_closed_lower_remainder {M : ℕ} {r rm mu M0 nm : ℝ}
    (hM : 8 ≤ M) (hmu : 0 < mu) (hr0 : 0 ≤ r) (hrrm : r ≤ rm)
    (hrmh : rm ≤ 1 / 2) (hM0 : 8 ≤ M0) (hM0M : M0 ≤ (M : ℝ))
    (hcap : activityNu r ((M : ℝ) + 2) ≤ nm)
    (hbeta : 0 < V22.betaL ((M : ℝ) / mu) ((M : ℝ) + 2) M0 rm nm) :
    bonusRangeDL r mu M ≤ V22.dLbar ((M : ℝ) / mu) ((M : ℝ) + 2) M0 rm nm := by
  let N : ℝ := (M : ℝ) + 2
  let t : ℝ := (M : ℝ) / mu
  have hN : 10 ≤ N := by dsimp [N]; exact_mod_cast (show 10 ≤ M + 2 by omega)
  have hnu := activityNu_nonneg (N := N) hr0
  have hnm := hnu.trans hcap
  obtain ⟨hA, hB⟩ := coefficient_alpha_nonneg hN (hr0.trans hrrm) hrmh
  have he := bonusRange_eL_nonneg (by linarith : 0 < N) hr0 (by linarith : r < 1)
  have hs := closed_sigma_comparison hM hmu hr0 hrrm hrmh hM0 hM0M
  have hebar := closed_eL_le_ebar hN hr0 hrrm hrmh hcap
  have hebar1 := (closed_betaL_forces_ebar hN (hr0.trans hrrm) hrmh hnm hbeta).le
  have hbonus := scaled_delta_lower hN (by nlinarith : r ^ 2 < 1)
  have hPoly := lowerRemainder_quadratic_envelope
    (C := N + 1) (d := N - 1) (A := V22.alpha1 N rm) (B := V22.alpha2 N rm)
    (sigma0 := V22.sigma0 t M0) (nu := activityNu r N) (nuM := nm)
    (e := V22.eL r N) (sigma := max (rootMap (activityOneLambda M mu .L + V22.eL r N)) 0)
    (bonus := N * V22.Delta r N) (ebar := V22.ebar N rm nm)
    (by linarith) (by linarith) hA hB (le_max_right _ _) hnu hcap he
    (linearized_eL_upper hN hr0 hrrm hrmh) hs hbonus hebar hebar1
  have hDen : N - 1 - 1 = N - 2 := by ring
  have hbetaEq : (N - 1) * (1 - V22.ebar N rm nm) -
      2 * V22.sigma0 t M0 * V22.alpha2 N rm -
      2 * (V22.alpha1 N rm + V22.alpha2 N rm * nm) ^ 2 / (N + 1) =
      V22.betaL t N M0 rm nm := by
    unfold V22.betaL
    ring
  rw [hbetaEq] at hPoly
  have hQuad : bonusRangeDL r mu M ≤ max
      (2 * V22.sigma0 t M0 * V22.alpha1 N rm * activityNu r N -
        V22.betaL t N M0 rm nm * activityNu r N ^ 2) 0 := by
    simpa only [bonusRangeDL, N, t,
      show ((M : ℝ) + 2) + 1 = (M : ℝ) + 3 by ring] using hPoly
  have hClosed := lowerRemainder_closed_quadratic hbeta hQuad
  exact hClosed

/-- The powers of the actual displacement are capped only on the named
bounded range, retaining every coefficient of `E`. -/
theorem closed_E_capped {nu nm N rm : ℝ} (hN : 10 ≤ N) (hr0 : 0 ≤ rm)
    (hrmh : rm ≤ 1 / 2) (hnu : 0 ≤ nu) (hcap : nu ≤ nm) :
    V22.E N rm nu ≤ 2 * nu + V22.E2 N rm nm * nu ^ 2 := by
  have hnm := hnu.trans hcap
  have hn : 0 < N := by linarith
  have hd := coefficient_one_sub_rm_sq_pos hr0 hrmh
  have he3 : 0 ≤ V22.e3 rm := by unfold V22.e3; positivity
  have he4 : 0 ≤ V22.e4 N rm := by unfold V22.e4; positivity
  have he5 : 0 ≤ V22.e5 rm := by unfold V22.e5; positivity
  have h3 : nu ^ 3 ≤ nm * nu ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right hcap (sq_nonneg nu)]
  have hsq := (sq_le_sq₀ hnu hnm).2 hcap
  have h4 : nu ^ 4 ≤ nm ^ 2 * nu ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg nu)]
  have hcube : nu ^ 3 ≤ nm ^ 3 := by gcongr
  have h5 : nu ^ 5 ≤ nm ^ 3 * nu ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hcube (sq_nonneg nu)]
  have h3s := mul_le_mul_of_nonneg_left h3 he3
  have h4s := mul_le_mul_of_nonneg_left h4 he4
  have h5s := mul_le_mul_of_nonneg_left h5 he5
  unfold V22.E V22.E2
  nlinarith

theorem closed_template_G_upper {M : ℕ} {mu M0 : ℝ}
    (hM : 8 ≤ M) (hmu : 0 < mu) (hM0 : 8 ≤ M0) (hM0M : M0 ≤ (M : ℝ))
    (side : ActivityOneSide) :
    rootG (activityOneLambda M mu side) ≤ V22.Ghat ((M : ℝ) / mu) M0 := by
  have hUpper := closed_template_shift_upper hM hmu hM0 hM0M side
  have hLower : V22.lambdaT ((M : ℝ) / mu) ≤ activityOneLambda M mu side := by
    have hk := (activityOneK_bounds hM side).1
    have hK0 : 0 ≤ activityOneK M side := by linarith
    rw [activityOneLambda_shift (by omega : 1 ≤ M) hmu side]
    unfold V22.lambdaT activityOneLambda_t
    have hfrac : 0 ≤ activityOneK M side / ((M : ℝ) + 3) := by positivity
    linarith
  have hConvex := rootG_convex.le_max_of_mem_Icc
    (mem_univ _) (mem_univ _) ⟨hLower, hUpper⟩
  simpa only [V22.Ghat, shared_G_eq] using hConvex

/-- Full source Lemma4.11(U): the source's two positive denominators and
its actual negative-root condition are the only additional hypotheses. -/
theorem source_closed_upper_remainder {M : ℕ} {r rm mu M0 nm : ℝ}
    (hM : 8 ≤ M) (hmu : 0 < mu) (hr0 : 0 ≤ r) (hrrm : r ≤ rm)
    (hrmh : rm ≤ 1 / 2) (hM0 : 8 ≤ M0) (hM0M : M0 ≤ (M : ℝ))
    (hcap : activityNu r ((M : ℝ) + 2) ≤ nm)
    (hUL : V22.lambdaT ((M : ℝ) / mu) ≤ threeRangeLambdaU r mu M)
    (hUNeg : threeRangeLambdaU r mu M < 0)
    (hbeta : 0 < V22.betaE ((M : ℝ) + 2) rm nm)
    (hden : 0 < (M : ℝ) + 2 - 1 - V22.kappaA ((M : ℝ) + 2) rm *
      V22.Ghat ((M : ℝ) / mu) M0 / V22.rhoStar ((M : ℝ) + 2) rm) :
    bonusRangeDUPrime r mu M ≤ V22.dUbar ((M : ℝ) / mu) ((M : ℝ) + 2) M0 rm nm := by
  let N : ℝ := (M : ℝ) + 2
  let t : ℝ := (M : ℝ) / mu
  let nu := activityNu r N
  let rs := V22.rhoStar N rm
  let Gh := V22.Ghat t M0
  let b1 := N - 1 - V22.kappaA N rm * Gh / rs
  let b2 := V22.betaE N rm nm
  have hN : 10 ≤ N := by dsimp [N]; exact_mod_cast (show 10 ≤ M + 2 by omega)
  have hNp : 0 < N := by linarith
  have hrs : 0 < rs := coefficient_rhoStar_pos hN (hr0.trans hrrm) hrmh
  have hU := bonusRange_rhoU_pos hN hr0 (hrrm.trans hrmh)
  have hUrs := linearized_rhoU_lower hN hr0 hrrm hrmh
  have hnu : 0 ≤ nu := activityNu_nonneg hr0
  have hGh : 0 ≤ Gh := by
    change 0 ≤ V22.Ghat t M0
    simp only [V22.Ghat, shared_G_eq]
    exact (rootG_nonneg (V22.lambdaT t)).trans (le_max_left _ _)
  have hK : 0 ≤ V22.kappaA N rm := (coefficient_remaining_nonneg hN (hr0.trans hrrm) hrmh).1
  have hE : 0 ≤ V22.E N rm nu := by
    have hd := coefficient_one_sub_rm_sq_pos (hr0.trans hrrm) hrmh
    unfold V22.E V22.e2 V22.e3 V22.e4 V22.e5
    positivity
  have hBonus := scaled_delta_lower hN (by nlinarith : r ^ 2 < 1)
  have hRecip := linearized_reciprocal_loss hN hr0 hrrm hrmh
  have hG := closed_template_G_upper hM hmu hM0 hM0M .U
  have hG0 := rootG_nonneg (activityOneLambda M mu .U)
  have hCoef : 0 ≤ (4 * nu + V22.kappaA N rm * nu ^ 2) / rs := by positivity
  have hLoss1 : 2 * N * (1 / V22.rhoU r N - 1 / V22.rho N) *
      rootG (activityOneLambda M mu .U) - N * V22.Delta r N ≤
      (4 * Gh / rs) * nu - b1 * nu ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hRecip hG0
    have h2 := mul_le_mul_of_nonneg_left hG hCoef
    have hEq : (4 * nu + V22.kappaA N rm * nu ^ 2) / rs * Gh -
        (N - 1) * nu ^ 2 = (4 * Gh / rs) * nu - b1 * nu ^ 2 := by
      dsimp [b1]
      ring
    rw [← hEq]
    linarith
  have hEU := linearized_eU_upper hN hr0 hrrm hrmh
  have hCapped := closed_E_capped hN (hr0.trans hrrm) hrmh hnu hcap
  have hLoss2 : 2 * N / V22.rhoU r N * V22.eU r N - N * V22.Delta r N ≤
      (4 / rs) * nu - b2 * nu ^ 2 := by
    have hEU' : N * V22.eU r N ≤ V22.E N rm nu := by
      simpa only [nu] using hEU
    have hBonus' : (N - 1) * nu ^ 2 ≤ N * V22.Delta r N := by
      simpa only [nu] using hBonus
    have h1 : 2 * N / V22.rhoU r N * V22.eU r N ≤
        2 / V22.rhoU r N * V22.E N rm nu := by
      calc
        _ = 2 / V22.rhoU r N * (N * V22.eU r N) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hEU' (by positivity)
    have h2 : 2 / V22.rhoU r N * V22.E N rm nu ≤
        2 / rs * V22.E N rm nu := by
      calc
        _ = (2 * V22.E N rm nu) / V22.rhoU r N := by ring
        _ ≤ (2 * V22.E N rm nu) / rs :=
          div_le_div_of_nonneg_left (by positivity) hrs hUrs
        _ = _ := by ring
    have h3 : 2 / rs * V22.E N rm nu ≤
        2 / rs * (2 * nu + V22.E2 N rm nm * nu ^ 2) :=
      mul_le_mul_of_nonneg_left hCapped (by positivity)
    have hEq : 2 / rs * (2 * nu + V22.E2 N rm nm * nu ^ 2) - (N - 1) * nu ^ 2 =
        (4 / rs) * nu - b2 * nu ^ 2 := by
      dsimp [b2]
      unfold V22.betaE
      ring
    calc
      _ ≤ 2 / rs * (2 * nu + V22.E2 N rm nm * nu ^ 2) - N * V22.Delta r N :=
        sub_le_sub_right (h1.trans (h2.trans h3)) _
      _ ≤ 2 / rs * (2 * nu + V22.E2 N rm nm * nu ^ 2) - (N - 1) * nu ^ 2 :=
        sub_le_sub_left hBonus' _
      _ = _ := hEq
  have hg := abs_nonneg (rootGPrime (threeRangeLambdaU r mu M))
  have hClosed := upperRemainder_closed_quadratics hg hden hbeta hLoss1 hLoss2
  have hSlope : |rootGPrime (threeRangeLambdaU r mu M)| ≤ |V22.G1 (V22.lambdaT t)| := by
    rw [shared_G1_eq]
    exact rootGPrime_abs_antitoneOn_nonpos (hUL.trans hUNeg.le) hUNeg.le hUL
  have hQ2 : 0 ≤ (4 / rs) ^ 2 / (4 * b2) := by positivity
  have hSlopeScaled := mul_le_mul_of_nonneg_right hSlope hQ2
  have hEq1 : (4 * Gh / rs) ^ 2 / (4 * b1) = 4 * Gh ^ 2 / (rs ^ 2 * b1) := by
    field_simp [hrs.ne', (show b1 ≠ 0 from hden.ne')] <;> ring
  have hEq2 : (4 / rs) ^ 2 / (4 * b2) = 4 / (rs ^ 2 * b2) := by
    field_simp [hrs.ne', (show b2 ≠ 0 from hbeta.ne')] <;> ring
  rw [hEq1, hEq2] at hClosed
  rw [hEq2] at hSlopeScaled
  change bonusRangeDUPrime r mu M ≤
    4 * Gh ^ 2 / (rs ^ 2 * b1) +
      |rootGPrime (threeRangeLambdaU r mu M)| * (4 / (rs ^ 2 * b2)) at hClosed
  calc
    bonusRangeDUPrime r mu M ≤ 4 * Gh ^ 2 / (rs ^ 2 * b1) +
        |rootGPrime (threeRangeLambdaU r mu M)| * (4 / (rs ^ 2 * b2)) := hClosed
    _ ≤ 4 * Gh ^ 2 / (rs ^ 2 * b1) +
        |V22.G1 (V22.lambdaT t)| * (4 / (rs ^ 2 * b2)) :=
      add_le_add le_rfl hSlopeScaled
    _ = V22.dUbar ((M : ℝ) / mu) ((M : ℝ) + 2) M0 rm nm := by
      dsimp [V22.dUbar, N, t, Gh, rs, b1, b2]
      ring


end Erdos993Lean.Analytic.V22.Analysis
