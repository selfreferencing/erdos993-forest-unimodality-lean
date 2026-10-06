import Erdos993Lean.Analytic.V22.Analysis.LargeNuUpper
import Erdos993Lean.Analytic.V22.Analysis.BonusRangeBounds
import Erdos993Lean.Analytic.V22.Analysis.LargeTComparison

/-!
# Paper v2.2, Lemma 4.14: the actual large-activity fiber

The final theorem assumes exactly `Checks.largeTConditions`, the original
activity/size domain, and every integer atom. The two radical regimes are
transported by LargeTComparison. The actual upper prefactor is bounded by
the native amplitude theorem, and the exponential tail maximum is proved
from `x*exp(-x)<=exp(-1)`.
-/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set Erdos993Lean.Analytic.NoValley

noncomputable def largeTActualX (r N : ℝ) : ℝ :=
  (N + 1) * V22.cr r + V22.epsilonPrime r N * Real.sqrt (V22.gamma r N) / 2 -
    V22.rhoU r N * V22.gamma r N / 2

/-- The exact radical bound retained by the large-activity proof. -/
theorem largeT_gamma_product_upper {r N : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) :
    largeNuGammaProduct r N ≤ Real.sqrt N * Real.sqrt (1 + activityNu r N ^ 2) := by
  have hn : 0 < N := by linarith
  have hd := coefficient_one_sub_rm_sq_pos hr0 hrh
  have hg : 0 < V22.gamma r N := by
    have hdel := delta_nonneg (by linarith : 1 ≤ N) (show r ^ 2 < 1 by linarith [hd])
    unfold V22.gamma
    linarith
  have hsn := shared_sN_sq hr0 (by linarith : r < 1) hn
  have hgsq := Real.sq_sqrt hg.le
  have hq : (largeNuGammaProduct r N) ^ 2 = N + r ^ 2 * (N - 1) ^ 2 := by
    calc
      _ = 4 * (V22.sN r N) ^ 2 * V22.gamma r N := by
        unfold largeNuGammaProduct
        rw [mul_pow, mul_pow, hgsq]
        ring
      _ = _ := by
        rw [hsn]
        unfold V22.varianceR V22.gamma V22.Delta
        field_simp [hd.ne', hn.ne'] <;> ring
  have hrhs : (Real.sqrt N * Real.sqrt (1 + activityNu r N ^ 2)) ^ 2 =
      N * (1 + r ^ 2 * N) := by
    rw [mul_pow, Real.sq_sqrt hn.le, Real.sq_sqrt (by positivity), activityNu_sq hn.le]
  apply (sq_le_sq₀ (by unfold largeNuGammaProduct V22.sN; positivity) (by positivity)).1
  rw [hq, hrhs]
  have hm : (N - 1) ^ 2 ≤ N ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hm (sq_nonneg r)]

theorem largeT_cr_majorant {r rm N : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hrmh : rm ≤ 1 / 2) :
    (N + 1) * V22.cr r ≤
      (N + 1) * activityNu r N ^ 4 / (12 * N ^ 2 * (1 - rm ^ 2) ^ 2) := by
  have hn : 0 < N := by linarith
  have hrm0 := hr0.trans hrrm
  have hdr := coefficient_one_sub_rm_sq_pos hr0 (hrrm.trans hrmh)
  have hdm := coefficient_one_sub_rm_sq_pos hrm0 hrmh
  have hrsq := (sq_le_sq₀ hr0 hrm0).2 hrrm
  have hd : 1 - rm ^ 2 ≤ 1 - r ^ 2 := by linarith
  have hdsq := (sq_le_sq₀ hdm.le hdr.le).2 hd
  have hcr := shared_cr_quartic_bound hr0 (hrrm.trans hrmh)
  have hbound : V22.cr r ≤ r ^ 4 / (12 * (1 - rm ^ 2) ^ 2) :=
    hcr.trans (div_le_div_of_nonneg_left (pow_nonneg hr0 4) (by positivity)
      (mul_le_mul_of_nonneg_left hdsq (by norm_num)))
  have h := mul_le_mul_of_nonneg_left hbound (show 0 ≤ N + 1 by linarith)
  apply h.trans_eq
  have hnu4 : activityNu r N ^ 4 = r ^ 4 * N ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, activityNu_sq hn.le]
    ring
  rw [hnu4]
  field_simp [hn.ne', hdm.ne'] <;> ring

theorem largeT_epsilon_product_majorant {r rm N : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hrmh : rm ≤ 1 / 2) :
    V22.epsilonPrime r N * Real.sqrt (V22.gamma r N) / 2 ≤
      activityNu r N * Real.sqrt (1 + activityNu r N ^ 2) / (N + 1) *
        (1 + activityNu r N ^ 2 * (N + 1) / (6 * N * (1 - rm ^ 2))) := by
  have hn : 0 < N := by linarith
  have hn1 : 0 < N + 1 := by linarith
  have hrm0 := hr0.trans hrrm
  have hdr := coefficient_one_sub_rm_sq_pos hr0 (hrrm.trans hrmh)
  have hdm := coefficient_one_sub_rm_sq_pos hrm0 hrmh
  have hr1 : r < 1 := by linarith
  have hrsq := (sq_le_sq₀ hr0 hrm0).2 hrrm
  have hy0 := shared_yTilde_nonneg hr0 hr1 hn
  have hQ := largeT_gamma_product_upper hN hr0 (hrrm.trans hrmh)
  have ha := monotone_aHat_scaled hr0 (hrrm.trans hrmh) hN
  rw [activityNu_gap hn] at ha
  have ha' : V22.aHat r * Real.sqrt N ≤
      activityNu r N ^ 3 / (3 * N * (1 - rm ^ 2)) :=
    ha.trans (div_le_div_of_nonneg_left (pow_nonneg (activityNu_nonneg hr0) 3)
      (by positivity) (by nlinarith [mul_nonneg hn.le (sub_nonneg.mpr hrsq)]))
  have hamul := mul_le_mul_of_nonneg_right ha' (show 0 ≤ (N + 1) / 2 by positivity)
  have hy : V22.yTilde r N * Real.sqrt N ≤
      activityNu r N * (1 + activityNu r N ^ 2 * (N + 1) / (6 * N * (1 - rm ^ 2))) := by
    unfold V22.yTilde
    have hid : activityNu r N + (activityNu r N ^ 3 / (3 * N * (1 - rm ^ 2))) * ((N + 1) / 2) =
        activityNu r N * (1 + activityNu r N ^ 2 * (N + 1) / (6 * N * (1 - rm ^ 2))) := by
      field_simp [hn.ne', hdm.ne'] <;> ring
    rw [← hid]
    dsimp [activityNu] at hamul ⊢
    nlinarith only [hamul]
  have hprod := mul_le_mul_of_nonneg_left hQ hy0
  have hys := mul_le_mul_of_nonneg_right hy (Real.sqrt_nonneg (1 + activityNu r N ^ 2))
  have hdiv : V22.yTilde r N * largeNuGammaProduct r N / (N + 1) ≤
      (activityNu r N *
        (1 + activityNu r N ^ 2 * (N + 1) / (6 * N * (1 - rm ^ 2))) *
          Real.sqrt (1 + activityNu r N ^ 2)) / (N + 1) :=
    div_le_div_of_nonneg_right (hprod.trans (by nlinarith only [hys])) hn1.le
  calc
    _ = V22.yTilde r N * largeNuGammaProduct r N / (N + 1) := by
      unfold V22.epsilonPrime largeNuGammaProduct
      ring
    _ ≤ (activityNu r N *
        (1 + activityNu r N ^ 2 * (N + 1) / (6 * N * (1 - rm ^ 2))) *
          Real.sqrt (1 + activityNu r N ^ 2)) / (N + 1) := hdiv
    _ = _ := by ring

/-- The actual upper exponent is bounded by the exact source majorant. -/
theorem largeT_X_majorant {r rm N : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hrmh : rm ≤ 1 / 2) :
    largeTActualX r N ≤ V22.Xbar (activityNu r N) N rm := by
  have hn : 0 < N := by linarith
  have hrm0 := hr0.trans hrrm
  have hd := coefficient_one_sub_rm_sq_pos hr0 (hrrm.trans hrmh)
  have hstar := coefficient_rhoStar_pos hN hrm0 hrmh
  have hU := linearized_rhoU_lower hN hr0 hrrm hrmh
  have hdel := scaled_delta_lower hN (show r ^ 2 < 1 by linarith [hd])
  have hg : 1 + activityNu r N ^ 2 * V22.cCoef N ≤ V22.gamma r N := by
    have hdiv : (N - 1) * activityNu r N ^ 2 / N ≤ V22.Delta r N := by
      apply (div_le_iff₀ hn).2
      nlinarith only [hdel]
    have hid : (N - 1) * activityNu r N ^ 2 / N = activityNu r N ^ 2 * V22.cCoef N := by
      unfold V22.cCoef
      field_simp [hn.ne'] <;> ring
    rw [hid] at hdiv
    unfold V22.gamma
    linarith
  have hc := (coefficient_cCoef_bounds hN).1
  have hc0 : 0 ≤ V22.cCoef N := by linarith
  have hprod := mul_le_mul hU hg
    (show 0 ≤ 1 + activityNu r N ^ 2 * V22.cCoef N by positivity)
    (hstar.trans_le hU).le
  have hcr := largeT_cr_majorant hN hr0 hrrm hrmh
  have heps := largeT_epsilon_product_majorant hN hr0 hrrm hrmh
  unfold largeTActualX V22.Xbar
  nlinarith only [hprod, hcr, heps]

/-- The exponential upper-range tail has its exact closed global maximum. -/
theorem largeT_upper_tail {P B rho gamma w : ℝ} (hP : 0 < P) (hB : 0 < B)
    (hrho : 0 < rho) (hw : gamma ≤ w) :
    B * gamma - (2 * P / rho) * Real.exp (-1 - rho * gamma / 2) ≤
      rootMinorant P B rho gamma w := by
  let x : ℝ := rho * (w - gamma) / 2
  have h := Real.mul_exp_neg_le_exp_neg_one x
  have hmul := mul_le_mul_of_nonneg_left h
    (show 0 ≤ (2 / rho) * Real.exp (-rho * gamma / 2) by positivity)
  have hid : (w - gamma) * Real.exp (-rho * w / 2) =
      ((2 / rho) * Real.exp (-rho * gamma / 2)) * (x * Real.exp (-x)) := by
    have he : -rho * w / 2 = -rho * gamma / 2 + -x := by dsimp [x]; ring
    rw [he, Real.exp_add]
    dsimp [x]
    field_simp [hrho.ne'] <;> ring
  have hid' : ((2 / rho) * Real.exp (-rho * gamma / 2)) * Real.exp (-1) =
      (2 / rho) * Real.exp (-1 - rho * gamma / 2) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [← hid, hid'] at hmul
  have hp := mul_le_mul_of_nonneg_left hmul hP.le
  have hp' : P * (w - gamma) * Real.exp (-rho * w / 2) ≤
      (2 * P / rho) * Real.exp (-1 - rho * gamma / 2) := by
    convert hp using 1 <;> ring
  have hb := mul_le_mul_of_nonneg_left hw hB.le
  have hkernel : P * (gamma - w) * Real.exp (-rho * w / 2) =
      -(P * (w - gamma) * Real.exp (-rho * w / 2)) := by ring
  unfold rootMinorant
  rw [hkernel]
  linarith only [hp', hb]

/-- The actual upper prefactor cost obeys the finite-check amplitude cap. -/
theorem largeT_upper_cost_bound {M : ℕ} {r mu : ℝ} (hN : 10 ≤ M + 2)
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hmu : 0 < mu)
    (ht : (8 / 5 : ℝ) ≤ (M : ℝ) / mu) :
    (2 * threeRangePU r mu M / V22.rhoU r ((M : ℝ) + 2)) *
      Real.exp (-1 - V22.rhoU r ((M : ℝ) + 2) * V22.gamma r ((M : ℝ) + 2) / 2) ≤
      V22.Checks.largeTConstant ((M : ℝ) + 2) /
        V22.rhoU r ((M : ℝ) + 2) * Real.exp (largeTActualX r ((M : ℝ) + 2)) := by
  let N : ℝ := (M : ℝ) + 2
  let B := N / mu
  have hn : 10 ≤ N := by
    have hn' : (10 : ℝ) ≤ ((M + 2 : ℕ) : ℝ) := by exact_mod_cast hN
    simpa only [N, Nat.cast_add, Nat.cast_ofNat] using hn'
  have hpN : 1 < N := by linarith
  have hU := bonusRange_rhoU_pos hn hr0 hrh
  have hB : (8 / 5 : ℝ) ≤ B := by
    have hdiv : (M : ℝ) / mu ≤ ((M : ℝ) + 2) / mu :=
      div_le_div_of_nonneg_right (by linarith : (M : ℝ) ≤ (M : ℝ) + 2) hmu.le
    exact ht.trans hdiv
  have hBp : 0 < B := by linarith
  have hpow := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 8 / 5) hB
    (by norm_num : -(3 / 2 : ℝ) ≤ 0)
  have hAmp := (amplitude_log_bounds hN).1.2
  have hApos := upperAmplitude_pos (by omega : 2 ≤ M + 2)
  have hA : upperAmplitude (M + 2) ≤ Real.exp (3 / (4 * N) + (11 / 10 : ℝ) / N ^ 2) := by
    have he := Real.exp_le_exp.mpr hAmp
    rw [Real.exp_log hApos] at he
    simpa only [Nat.cast_add, Nat.cast_ofNat] using he
  have hc0 : 0 ≤ V22.c0Prime r N := by unfold V22.c0Prime; positivity
  have hExp := Real.exp_le_exp.mpr (show largeTActualX r N - V22.c0Prime r N ≤ largeTActualX r N by linarith)
  have hCoef : 2 * Real.exp (-(1 / 2 : ℝ)) * B ^ (-(3 / 2 : ℝ)) * upperAmplitude (M + 2) ≤
      V22.Checks.largeTConstant N := by
    unfold V22.Checks.largeTConstant
    have hprod := mul_le_mul hpow hA hApos.le (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 8 / 5) _)
    have hs := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 2 * Real.exp (-(1 / 2 : ℝ)) by positivity)
    simpa only [mul_assoc] using hs
  have hCoef0 : 0 ≤ 2 * Real.exp (-(1 / 2 : ℝ)) * B ^ (-(3 / 2 : ℝ)) * upperAmplitude (M + 2) := by positivity
  have hConstant0 : 0 ≤ V22.Checks.largeTConstant N := hCoef0.trans hCoef
  have hCost := mul_le_mul (div_le_div_of_nonneg_right hCoef hU.le) hExp (Real.exp_pos _).le
    (div_nonneg hConstant0 hU.le)
  have hPU : threeRangePU r mu M =
      Real.exp (1 / 2 : ℝ) * B ^ (-(3 / 2 : ℝ)) * upperAmplitude (M + 2) *
        Real.exp ((N + 1) * V22.cr r - V22.c0Prime r N +
          V22.epsilonPrime r N * Real.sqrt (V22.gamma r N) / 2) := by
    unfold threeRangePU
    rw [shapeTemplatePrefactor_normalization hmu hpN (symmetricUpperPrefactor_pos (M + 2))]
    have hAmplitude : shapeAmplitude ((M : ℝ) + 2) (symmetricUpperPrefactor (M + 2)) =
        upperAmplitude (M + 2) := by
      simp only [upperAmplitude, Nat.cast_add, Nat.cast_ofNat]
    rw [hAmplitude]
    change Real.exp (1 / 2 : ℝ) * B ^ (-(3 / 2 : ℝ)) * upperAmplitude (M + 2) *
      Real.exp (((M : ℝ) + 3) * V22.cr r - V22.c0Prime r N +
        V22.epsilonPrime r N * Real.sqrt (V22.gamma r N) / 2) = _
    congr 1
    congr 1
    dsimp [N]
    ring
  have hid : (2 * threeRangePU r mu M / V22.rhoU r N) *
      Real.exp (-1 - V22.rhoU r N * V22.gamma r N / 2) =
      (2 * Real.exp (-(1 / 2 : ℝ)) * B ^ (-(3 / 2 : ℝ)) * upperAmplitude (M + 2) /
        V22.rhoU r N) * Real.exp (largeTActualX r N - V22.c0Prime r N) := by
    rw [hPU]
    calc
      _ = (2 * B ^ (-(3 / 2 : ℝ)) * upperAmplitude (M + 2) / V22.rhoU r N) *
          (Real.exp (1 / 2 : ℝ) * Real.exp ((N + 1) * V22.cr r - V22.c0Prime r N +
            V22.epsilonPrime r N * Real.sqrt (V22.gamma r N) / 2) *
            Real.exp (-1 - V22.rhoU r N * V22.gamma r N / 2)) := by ring
      _ = (2 * B ^ (-(3 / 2 : ℝ)) * upperAmplitude (M + 2) / V22.rhoU r N) *
          Real.exp ((1 / 2 : ℝ) + ((N + 1) * V22.cr r - V22.c0Prime r N +
            V22.epsilonPrime r N * Real.sqrt (V22.gamma r N) / 2) +
            (-1 - V22.rhoU r N * V22.gamma r N / 2)) := by
        rw [← Real.exp_add, ← Real.exp_add]
      _ = (2 * B ^ (-(3 / 2 : ℝ)) * upperAmplitude (M + 2) / V22.rhoU r N) *
          Real.exp (-(1 / 2 : ℝ) + (largeTActualX r N - V22.c0Prime r N)) := by
        congr 2
        unfold largeTActualX
        ring
      _ = _ := by rw [Real.exp_add]; ring
  rw [hid]
  exact hCost

/-- Every atom in the original kernel-positive range has nonnegative fiber. -/
theorem largeT_fiber_inside_nonneg {M : ℕ} {r mu : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hmu : 0 < mu) (j : ℤ)
    (hw : threeRangeW r M j ≤ V22.gamma r ((M : ℝ) + 2)) :
    0 ≤ V22.fiberFunction ((1 + r) / 2) mu M j := by
  rw [threeRange_fiber_eq hr0 (by linarith : r < 1) hmu]
  have hmass : 0 ≤ threeRangeMass r M j := by
    unfold threeRangeMass
    have hb := binom_nonneg (by linarith : 0 ≤ (1 + r) / 2) (by linarith : (1 + r) / 2 ≤ 1) (M := M + 2) (j + 1)
    have hc := (shared_centralAmplitude_pos (M + 2)).le
    positivity
  have hN1 : 1 < (M : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) M]
  have hP := (shapeTemplatePrefactor_pos (N := (M : ℝ) + 2) hmu hN1
    (shared_centralAmplitude_pos (M + 2))).le
  have hw0 : 0 ≤ threeRangeW r M j := sq_nonneg _
  exact add_nonneg (mul_nonneg (mul_nonneg hP hmass) (sub_nonneg.mpr hw)) (by positivity)

/-- The target parabola is strictly negative throughout the large-t domain. -/
theorem largeT_psi_negative {t : ℝ} (ht : (8 / 5 : ℝ) ≤ t) : V22.psi t < 0 := by
  unfold V22.psi
  nlinarith [mul_nonneg (show 0 ≤ t - 8 / 5 by linarith) (show 0 ≤ t + 8 / 5 - 20 / 9 by linarith)]

/-- Paper v2.2, Lemma 4.14, for every genuine fiber and every integer atom.
Exactly the original finite `largeTConditions` are assumed. -/
theorem largeT_fiber_source {M : ℕ} {r rm mu Nstar : ℝ}
    (hc : V22.Checks.largeTConditions rm Nstar) (hrm : 0 < rm) (hrmh : rm ≤ 1 / 2)
    (hNs : 10 ≤ Nstar) (hN : Nstar ≤ (M : ℝ) + 2)
    (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hmu : 0 < mu)
    (ht : (8 / 5 : ℝ) ≤ (M : ℝ) / mu) (j : ℤ) :
    0 ≤ V22.fiberFunction ((1 + r) / 2) mu M j ∧ V22.psi ((M : ℝ) / mu) < 0 := by
  let N : ℝ := (M : ℝ) + 2
  let nu := activityNu r N
  let B := N / mu
  have hn : 10 ≤ N := hNs.trans hN
  have hNN : 10 ≤ M + 2 := by
    have hn' : (10 : ℝ) ≤ ((M + 2 : ℕ) : ℝ) := by
      simpa only [N, Nat.cast_add, Nat.cast_ofNat] using hn
    exact_mod_cast hn'
  have hpN : 0 < N := by linarith
  have hrh := hrrm.trans hrmh
  have hU := bonusRange_rhoU_pos hn hr0 hrh
  have hgamma := threeRange_gamma_ge_one hr0 (by linarith : r < 1) M
  have hgammap : 0 < V22.gamma r N := by linarith
  have hB : (8 / 5 : ℝ) ≤ B := by
    have hdiv : (M : ℝ) / mu ≤ ((M : ℝ) + 2) / mu :=
      div_le_div_of_nonneg_right (by linarith : (M : ℝ) ≤ (M : ℝ) + 2) hmu.le
    exact ht.trans hdiv
  have hBp : 0 < B := by linarith
  refine ⟨?_, largeT_psi_negative ht⟩
  rcases le_total (threeRangeW r M j) (V22.gamma r N) with hw | hw
  · exact largeT_fiber_inside_nonneg hr0 hrh hmu j hw
  · have hF := threeRanges_upper hNN hr0 hrh hmu j hw
    by_cases hlarge : 6 ≤ nu
    · have hl := (largeNu_upper_positive hNN hr0 hrh hlarge hmu
        (ta := (8 / 5 : ℝ)) (by norm_num) ht).2
      have hmin := bonusRange_upper_nonneg (threeRangePU_pos hmu r M) hBp hU hgamma hl.le _ hw
      have hbase : 0 ≤ B * V22.gamma r N := by positivity
      exact hbase.trans (hmin.trans hF)
    · have hnu0 : 0 ≤ nu := activityNu_nonneg hr0
      have hnu6 : nu ≤ 6 := by linarith
      have hcap : nu ^ 2 / rm ^ 2 ≤ N := by
        apply (div_le_iff₀ (sq_pos_of_pos hrm)).2
        dsimp [nu]
        rw [activityNu_sq hpN.le]
        calc
          r ^ 2 * N ≤ rm ^ 2 * N :=
            mul_le_mul_of_nonneg_right ((sq_le_sq₀ hr0 hrm.le).2 hrrm) hpN.le
          _ = N * rm ^ 2 := mul_comm _ _
      have hfinite := largeT_comparison_at_actual_N hc hrm hrmh hNs hN hnu0 hnu6 hcap
      have hX := largeT_X_majorant hn hr0 hrrm hrmh
      have hstar := coefficient_rhoStar_pos hn hrm.le hrmh
      have hUstar := linearized_rhoU_lower hn hr0 hrrm hrmh
      have hLog : Real.log ((257 / 100 : ℝ) * V22.rhoStar N rm) ≤
          Real.log ((257 / 100 : ℝ) * V22.rhoU r N) := by
        apply Real.log_le_log (by positivity)
        nlinarith only [hUstar]
      have hXLog : largeTActualX r N ≤ Real.log ((257 / 100 : ℝ) * V22.rhoU r N) :=
        hX.trans (hfinite.trans hLog)
      have hExp := Real.exp_le_exp.mpr hXLog
      rw [Real.exp_log (by positivity : 0 < (257 / 100 : ℝ) * V22.rhoU r N)] at hExp
      have hConstant := hc.2.2 N hN
      have hCost := largeT_upper_cost_bound hNN hr0 hrh hmu ht
      have hComp := mul_le_mul (div_le_div_of_nonneg_right hConstant hU.le) hExp
        (Real.exp_pos _).le (by positivity : 0 ≤ (249 / 400 : ℝ) / V22.rhoU r N)
      have hNum : ((249 / 400 : ℝ) / V22.rhoU r N) * ((257 / 100 : ℝ) * V22.rhoU r N) =
          (63993 / 40000 : ℝ) := by field_simp [hU.ne'] <;> norm_num
      rw [hNum] at hComp
      have hcostcap : (2 * threeRangePU r mu M / V22.rhoU r N) *
          Real.exp (-1 - V22.rhoU r N * V22.gamma r N / 2) ≤ (8 / 5 : ℝ) := by
        exact hCost.trans (hComp.trans (by norm_num))
      have hTail := largeT_upper_tail (threeRangePU_pos hmu r M) hBp hU hw
      have hBG : (8 / 5 : ℝ) ≤ B * V22.gamma r N := by
        have h := mul_le_mul hB hgamma (by norm_num : (0 : ℝ) ≤ 1) hBp.le
        norm_num at h
        exact h
      exact le_trans (by linarith only [hBG, hcostcap, hTail]) hF

end Erdos993Lean.Analytic.V22.Analysis
