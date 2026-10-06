import Erdos993Lean.Analytic.V22.Analysis.LargeNu

/-!
# Paper v2.2, Lemma 4.12(a): closed upper gain

The geometric epsilon estimates use the exact identity
`(2*sN*sqrt(gamma))²=N+r²*(N-1)²`. All numerical constants are rational.
The public source theorem consumes the actual native upper template and
assumes only its original domain. Compilation belongs to the root lane.
-/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

noncomputable def largeNuGammaProduct (r N : ℝ) : ℝ :=
  2 * V22.sN r N * Real.sqrt (V22.gamma r N)

theorem largeNu_gamma_product_bounds {r N : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) :
    r * (N - 1) ≤ largeNuGammaProduct r N ∧
    largeNuGammaProduct r N ≤ Real.sqrt N + r * (N - 1) := by
  have hn : 0 < N := by linarith
  have hd := coefficient_one_sub_rm_sq_pos hr0 hrh
  have hr1 : r < 1 := by linarith
  have hg : 0 < V22.gamma r N := by
    have hdel := delta_nonneg (by linarith : 1 ≤ N)
      (show r ^ 2 < 1 by linarith [hd])
    unfold V22.gamma
    linarith
  have hsn := shared_sN_sq hr0 hr1 hn
  have hgsq := Real.sq_sqrt hg.le
  have hsN := Real.sq_sqrt hn.le
  have hq0 : 0 ≤ largeNuGammaProduct r N := by
    unfold largeNuGammaProduct V22.sN
    positivity
  have hq : (largeNuGammaProduct r N) ^ 2 = N + r ^ 2 * (N - 1) ^ 2 := by
    calc
      (largeNuGammaProduct r N) ^ 2 = 4 * (V22.sN r N) ^ 2 * V22.gamma r N := by
        unfold largeNuGammaProduct
        rw [mul_pow, mul_pow, hgsq]
        ring
      _ = N + r ^ 2 * (N - 1) ^ 2 := by
        rw [hsn]
        unfold V22.varianceR V22.gamma V22.Delta
        field_simp [hd.ne', hn.ne'] <;> ring
  have hrNm : 0 ≤ r * (N - 1) := mul_nonneg hr0 (by linarith)
  constructor
  · have hsq : (r * (N - 1)) ^ 2 ≤ (largeNuGammaProduct r N) ^ 2 := by
      rw [hq]
      nlinarith
    exact (sq_le_sq₀ hrNm hq0).1 hsq
  · have hsq : (largeNuGammaProduct r N) ^ 2 ≤ (Real.sqrt N + r * (N - 1)) ^ 2 := by
      rw [hq]
      nlinarith [mul_nonneg (Real.sqrt_nonneg N) hrNm]
    exact (sq_le_sq₀ hq0 (add_nonneg (Real.sqrt_nonneg N) hrNm)).1 hsq

/-- The exact geometric ratio in the source proof, before numerical bounding. -/
theorem largeNu_epsilon_ratio_formula_bound {r N : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hrp : 0 < r) :
    V22.epsilonPrime r N / Real.sqrt (V22.gamma r N) ≤
      2 * (1 - r ^ 2) * N / (N ^ 2 - 1) + r ^ 2 * N / (3 * (N - 1)) := by
  have hn : 0 < N := by linarith
  have hn1 : 0 < N + 1 := by linarith
  have hnm : 0 < N - 1 := by linarith
  have hd := coefficient_one_sub_rm_sq_pos hr0 hrh
  have hr1 : r < 1 := by linarith
  have hdel := delta_nonneg (by linarith : 1 ≤ N) (show r ^ 2 < 1 by linarith [hd])
  have hg : 0 < V22.gamma r N := by unfold V22.gamma; linarith
  have hsg := Real.sqrt_pos.2 hg
  have hs0 : 0 ≤ V22.sN r N := Real.sqrt_nonneg _
  have hsn := shared_sN_sq hr0 hr1 hn
  have hq := (largeNu_gamma_product_bounds hN hr0 hrh).1
  have hmul := mul_le_mul_of_nonneg_right hq (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hs0)
  have hsratio : V22.sN r N / Real.sqrt (V22.gamma r N) ≤
      (1 - r ^ 2) * N / (2 * r * (N - 1)) := by
    apply (div_le_div_iff₀ hsg (by positivity : 0 < 2 * r * (N - 1))).2
    unfold largeNuGammaProduct at hmul
    have hmul' : 2 * r * (N - 1) * V22.sN r N ≤
        4 * (V22.sN r N) ^ 2 * Real.sqrt (V22.gamma r N) := by nlinarith only [hmul]
    rw [hsn] at hmul'
    unfold V22.varianceR at hmul'
    nlinarith only [hmul']
  have hy0 := shared_yTilde_nonneg hr0 hr1 hn
  have hy : V22.yTilde r N ≤ r + r ^ 3 * (N + 1) / (6 * (1 - r ^ 2)) := by
    have ha := mul_le_mul_of_nonneg_right (sharedAHat_bounds hr0 hr1).2 hn1.le
    calc
      V22.yTilde r N = r + V22.aHat r * (N + 1) / 2 := rfl
      _ ≤ r + (r ^ 3 / (3 * (1 - r ^ 2)) * (N + 1)) / 2 := by linarith
      _ = _ := by field_simp [hd.ne'] <;> ring
  have hratio0 : 0 ≤ (1 - r ^ 2) * N / (2 * r * (N - 1)) := by positivity
  calc
    V22.epsilonPrime r N / Real.sqrt (V22.gamma r N) =
        (4 * V22.yTilde r N / (N + 1)) *
          (V22.sN r N / Real.sqrt (V22.gamma r N)) := by unfold V22.epsilonPrime; ring
    _ ≤ (4 * V22.yTilde r N / (N + 1)) *
        ((1 - r ^ 2) * N / (2 * r * (N - 1))) :=
      mul_le_mul_of_nonneg_left hsratio (by positivity)
    _ ≤ (4 * (r + r ^ 3 * (N + 1) / (6 * (1 - r ^ 2))) / (N + 1)) *
        ((1 - r ^ 2) * N / (2 * r * (N - 1))) := by
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hy (by norm_num)) hn1.le) hratio0
    _ = 2 * (1 - r ^ 2) * N / (N ^ 2 - 1) + r ^ 2 * N / (3 * (N - 1)) := by
      field_simp [hd.ne', hrp.ne', hnm.ne', hn1.ne',
        (show N ^ 2 - 1 ≠ 0 by nlinarith)] <;> ring

theorem largeNu_epsilon_ratio_upper {r N : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hnu : 6 ≤ activityNu r N) :
    V22.epsilonPrime r N / Real.sqrt (V22.gamma r N) ≤ (49 / 500 : ℝ) := by
  obtain ⟨hrp, _, hN144⟩ := largeNu_domains hN hr0 hrh hnu
  have hrsq := (coefficient_rm_sq_bounds hr0 hrh).2.1
  have hd := coefficient_one_sub_rm_sq_pos hr0 hrh
  have hn : 0 < N := by linarith
  have hfirst : N / (N ^ 2 - 1) ≤ (144 / 20735 : ℝ) := by
    apply (div_le_iff₀ (show 0 < N ^ 2 - 1 by nlinarith)).2
    nlinarith [mul_nonneg (show 0 ≤ N - 144 by linarith) (show 0 ≤ 144 * N + 1 by linarith)]
  have hsecond : N / (N - 1) ≤ (144 / 143 : ℝ) := by
    apply (div_le_iff₀ (show 0 < N - 1 by linarith)).2
    linarith
  have hfirst' : 2 * (1 - r ^ 2) * N / (N ^ 2 - 1) ≤ (288 / 20735 : ℝ) := by
    have hprod := mul_le_mul (show 1 - r ^ 2 ≤ 1 by nlinarith [sq_nonneg r]) hfirst
      (div_nonneg hn.le (by nlinarith : 0 ≤ N ^ 2 - 1)) (by norm_num : (0 : ℝ) ≤ 1)
    have hmul := mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 2)
    convert hmul using 1 <;> ring
  have hsecond' : r ^ 2 * N / (3 * (N - 1)) ≤ (12 / 143 : ℝ) := by
    have hprod := mul_le_mul hrsq hsecond
      (div_nonneg hn.le (by linarith : 0 ≤ N - 1)) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have heq : r ^ 2 * N / (3 * (N - 1)) = (r ^ 2 * (N / (N - 1))) / 3 := by
      field_simp [(show 0 < N - 1 by linarith).ne'] <;> ring
    rw [heq]
    nlinarith
  have hbound := largeNu_epsilon_ratio_formula_bound hN hr0 hrh hrp
  linarith

theorem largeNu_rhoU_lower {r N : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hnu : 6 ≤ activityNu r N) :
    (16 / 25 : ℝ) ≤ V22.rhoU r N := by
  have hN144 := (largeNu_domains hN hr0 hrh hnu).2.2
  have hratio := largeNu_epsilon_ratio_upper hN hr0 hrh hnu
  have hdlo := (coefficient_rm_sq_bounds hr0 hrh).2.2
  have hrho : (144 / 145 : ℝ) ≤ V22.rho N := by
    have h := coefficient_rho_monotone (N := 144) (M := N) (by norm_num) hN144
    norm_num [V22.rho] at h
    exact h
  have hprod := mul_le_mul hdlo hrho (by norm_num : (0 : ℝ) ≤ 144 / 145)
    (by linarith : 0 ≤ 1 - r ^ 2)
  unfold V22.rhoU
  linarith

/-- The product estimate retains all four exact source contributions. -/
theorem largeNu_epsilon_product_upper {r N : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hnu : 6 ≤ activityNu r N) :
    V22.epsilonPrime r N * Real.sqrt (V22.gamma r N) ≤
      (1 / 12 : ℝ) + 1 / 2 + activityNu r N / 9 + activityNu r N ^ 2 / 9 := by
  obtain ⟨_, hfour, hN144⟩ := largeNu_domains hN hr0 hrh hnu
  have hn : 0 < N := by linarith
  have hn1 : 0 < N + 1 := by linarith
  have hd := coefficient_one_sub_rm_sq_pos hr0 hrh
  have hdlo := (coefficient_rm_sq_bounds hr0 hrh).2.2
  have hrsq := (coefficient_rm_sq_bounds hr0 hrh).2.1
  have hr1 : r < 1 := by linarith
  have hy0 := shared_yTilde_nonneg hr0 hr1 hn
  have hnu0 : 0 ≤ activityNu r N := by linarith
  have hNm1 : 0 ≤ N - 1 := by linarith
  have hy : V22.yTilde r N ≤ r + r ^ 3 * (N + 1) / (6 * (1 - r ^ 2)) := by
    have ha := mul_le_mul_of_nonneg_right (sharedAHat_bounds hr0 hr1).2 hn1.le
    calc
      V22.yTilde r N = r + V22.aHat r * (N + 1) / 2 := rfl
      _ ≤ r + (r ^ 3 / (3 * (1 - r ^ 2)) * (N + 1)) / 2 := by linarith
      _ = _ := by field_simp [hd.ne'] <;> ring
  have hq := (largeNu_gamma_product_bounds hN hr0 hrh).2
  have hprod : V22.epsilonPrime r N * Real.sqrt (V22.gamma r N) ≤
      (2 * (r + r ^ 3 * (N + 1) / (6 * (1 - r ^ 2))) / (N + 1)) *
        (Real.sqrt N + r * (N - 1)) := by
    calc
      V22.epsilonPrime r N * Real.sqrt (V22.gamma r N) =
          (2 * V22.yTilde r N / (N + 1)) * largeNuGammaProduct r N := by
        unfold V22.epsilonPrime largeNuGammaProduct
        ring
      _ ≤ (2 * V22.yTilde r N / (N + 1)) * (Real.sqrt N + r * (N - 1)) :=
        mul_le_mul_of_nonneg_left hq (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hy (by norm_num)) hn1.le)
        (by positivity)
  have hexp : (2 * (r + r ^ 3 * (N + 1) / (6 * (1 - r ^ 2))) / (N + 1)) *
      (Real.sqrt N + r * (N - 1)) =
      2 * activityNu r N / (N + 1) + 2 * r ^ 2 * (N - 1) / (N + 1) +
        r ^ 2 * activityNu r N / (3 * (1 - r ^ 2)) +
        r ^ 4 * (N - 1) / (3 * (1 - r ^ 2)) := by
    unfold activityNu
    field_simp [hd.ne', hn1.ne'] <;> ring
  have hsmall : 2 * activityNu r N / (N + 1) ≤ (1 / 12 : ℝ) := by
    apply (div_le_iff₀ hn1).2
    nlinarith [mul_nonneg hnu0 (show 0 ≤ activityNu r N - 6 by linarith)]
  have hhalf : 2 * r ^ 2 * (N - 1) / (N + 1) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hn1).2
    nlinarith [mul_le_mul_of_nonneg_right hrsq (show 0 ≤ N - 1 by linarith)]
  have hthird : r ^ 2 * activityNu r N / (3 * (1 - r ^ 2)) ≤ activityNu r N / 9 := by
    apply (div_le_iff₀ (by positivity : 0 < 3 * (1 - r ^ 2))).2
    have h := mul_le_mul_of_nonneg_right (show 3 * r ^ 2 ≤ 1 - r ^ 2 by nlinarith) hnu0
    nlinarith
  have hlast : r ^ 4 * (N - 1) / (3 * (1 - r ^ 2)) ≤ activityNu r N ^ 2 / 9 := by
    apply (div_le_iff₀ (by positivity : 0 < 3 * (1 - r ^ 2))).2
    have h := mul_le_mul_of_nonneg_right (show 3 * r ^ 2 ≤ 1 - r ^ 2 by nlinarith)
      (mul_nonneg (sq_nonneg r) hn.le)
    rw [activityNu_sq hn.le]
    nlinarith [pow_nonneg hr0 4]
  rw [hexp] at hprod
  linarith

/-- The strict quartic estimate with the exact source rational constant. -/
theorem largeNu_cr_upper {r N : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hnu : 6 ≤ activityNu r N) :
    (N + 1) * V22.cr r ≤ (373 / 10000 : ℝ) * activityNu r N ^ 2 := by
  have hN144 := (largeNu_domains hN hr0 hrh hnu).2.2
  have hn : 0 < N := by linarith
  have hd := coefficient_one_sub_rm_sq_pos hr0 hrh
  have hdlo := (coefficient_rm_sq_bounds hr0 hrh).2.2
  have hrsq := (coefficient_rm_sq_bounds hr0 hrh).2.1
  have hdsq := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 3 / 4) hd.le).2 hdlo
  have hcoef : r ^ 2 / (12 * (1 - r ^ 2) ^ 2) ≤ (1 / 27 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 12 * (1 - r ^ 2) ^ 2)).2
    nlinarith
  have hquot : (N + 1) / N ≤ (145 / 144 : ℝ) := by
    apply (div_le_iff₀ hn).2
    linarith
  have hprod := mul_le_mul hcoef hquot (by positivity : 0 ≤ (N + 1) / N)
    (by norm_num : (0 : ℝ) ≤ 1 / 27)
  have hmul := mul_le_mul_of_nonneg_left hprod (sq_nonneg (activityNu r N))
  have hid : (N + 1) * (r ^ 4 / (12 * (1 - r ^ 2) ^ 2)) =
      activityNu r N ^ 2 * (r ^ 2 / (12 * (1 - r ^ 2) ^ 2) * ((N + 1) / N)) := by
    rw [activityNu_sq hn.le]
    field_simp [hn.ne', hd.ne'] <;> ring
  have hcr := mul_le_mul_of_nonneg_left (shared_cr_quartic_bound hr0 hrh)
    (show 0 ≤ N + 1 by linarith)
  rw [hid] at hcr
  nlinarith [sq_nonneg (activityNu r N)]

theorem largeNu_eU_upper {r N : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hnu : 6 ≤ activityNu r N) :
    V22.eU r N ≤ (29 / 250 : ℝ) * activityNu r N ^ 2 := by
  have hn : 0 < N := by linarith
  have hrsq := (coefficient_rm_sq_bounds hr0 hrh).2.1
  have hrho0 : 0 ≤ V22.rho N := by unfold V22.rho; positivity
  have hrho1 : V22.rho N ≤ 1 := by
    unfold V22.rho
    exact (div_le_one (by linarith : 0 < N + 1)).2 (by linarith)
  have hfirst := mul_le_mul hrsq hrho1 hrho0 (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hratio := largeNu_epsilon_ratio_upper hN hr0 hrh hnu
  have hproduct := largeNu_epsilon_product_upper hN hr0 hrh hnu
  have hcr := largeNu_cr_upper hN hr0 hrh hnu
  have hc0 : 0 ≤ V22.c0Prime r N := by unfold V22.c0Prime; positivity
  have hraw : V22.eU r N ≤ (47 / 100 : ℝ) + activityNu r N / 18 +
      (93 / 1000 : ℝ) * activityNu r N ^ 2 := by
    unfold V22.eU
    have hid : V22.epsilonPrime r N / 2 *
        (Real.sqrt (V22.gamma r N) + 1 / Real.sqrt (V22.gamma r N)) =
        (V22.epsilonPrime r N * Real.sqrt (V22.gamma r N) +
          V22.epsilonPrime r N / Real.sqrt (V22.gamma r N)) / 2 := by ring
    rw [hid]
    nlinarith [sq_nonneg (activityNu r N)]
  have hpoly : (47 / 100 : ℝ) + activityNu r N / 18 +
      (93 / 1000 : ℝ) * activityNu r N ^ 2 ≤ (29 / 250 : ℝ) * activityNu r N ^ 2 := by
    have hnu0 : 0 ≤ activityNu r N := by linarith
    nlinarith [mul_nonneg (show 0 ≤ activityNu r N - 6 by linarith) hnu0]
  exact hraw.trans hpoly

theorem largeNu_delta_fraction_lower {r N : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hnu : 6 ≤ activityNu r N) :
    (143 / 144 : ℝ) * activityNu r N ^ 2 ≤ V22.Delta r N := by
  have hN144 := (largeNu_domains hN hr0 hrh hnu).2.2
  have hd := coefficient_one_sub_rm_sq_pos hr0 hrh
  have hscaled := scaled_delta_lower hN (show r ^ 2 < 1 by linarith [hd])
  have hcoef : (143 / 144 : ℝ) * N ≤ N - 1 := by linarith
  have h := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (activityNu r N))
  have hfinal : N * ((143 / 144 : ℝ) * activityNu r N ^ 2) ≤ N * V22.Delta r N := by
    nlinarith
  exact (mul_le_mul_iff_right₀ (show 0 < N by linarith)).mp hfinal

/-- The genuine template shift supplies its lower log-ratio bound internally. -/
theorem largeNu_template_lower {M : ℕ} {mu : ℝ} (hM : 8 ≤ M) (hmu : 0 < mu)
    (side : ActivityOneSide) :
    V22.lambdaT ((M : ℝ) / mu) ≤ activityOneLambda M mu side := by
  rw [activityOneLambda_shift (by omega : 1 ≤ M) hmu side]
  have hk := (activityOneK_bounds hM side).1
  have hK0 : 0 ≤ activityOneK M side := by linarith
  have hdiv : 0 ≤ activityOneK M side / ((M : ℝ) + 3) := by positivity
  change activityOneLambda_t ((M : ℝ) / mu) ≤
    activityOneLambda_t ((M : ℝ) / mu) + activityOneK M side / ((M : ℝ) + 3)
  linarith

/-- Paper v2.2, Lemma 4.12(a): the native upper log-ratio gains `.19*nu²`
for every positive activity, with no additional analytic assumption. -/
theorem largeNu_upper_source {M : ℕ} {r mu : ℝ} (hN : 10 ≤ M + 2)
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hnu : 6 ≤ activityNu r ((M : ℝ) + 2))
    (hmu : 0 < mu) :
    V22.lambdaT ((M : ℝ) / mu) + (19 / 100 : ℝ) * activityNu r ((M : ℝ) + 2) ^ 2 ≤
      threeRangeLambdaU r mu M := by
  have hn : (10 : ℝ) ≤ (M : ℝ) + 2 := by exact_mod_cast hN
  have hlower := largeNu_template_lower (by omega : 8 ≤ M) hmu ActivityOneSide.U
  have hdel := largeNu_delta_fraction_lower hn hr0 hrh hnu
  have hrho := largeNu_rhoU_lower hn hr0 hrh hnu
  have he := largeNu_eU_upper hn hr0 hrh hnu
  have hprod := mul_le_mul hrho hdel
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 143 / 144) (sq_nonneg (activityNu r ((M : ℝ) + 2))))
    (by linarith : 0 ≤ V22.rhoU r ((M : ℝ) + 2))
  rw [threeRanges_lambdaU_eq hN hr0 hrh hmu]
  change V22.lambdaT ((M : ℝ) / mu) + (19 / 100 : ℝ) * activityNu r ((M : ℝ) + 2) ^ 2 ≤
    activityOneLambda M mu ActivityOneSide.U + V22.rhoU r ((M : ℝ) + 2) / 2 *
      V22.Delta r ((M : ℝ) + 2) - V22.eU r ((M : ℝ) + 2)
  nlinarith [sq_nonneg (activityNu r ((M : ℝ) + 2))]

/-- The exact source positive-log conclusion at every `ta>=.1548`. -/
theorem largeNu_upper_positive {M : ℕ} {r mu ta : ℝ} (hN : 10 ≤ M + 2)
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hnu : 6 ≤ activityNu r ((M : ℝ) + 2))
    (hmu : 0 < mu) (hta : (387 / 2500 : ℝ) ≤ ta) (ht : ta ≤ (M : ℝ) / mu) :
    (5 / 2 : ℝ) * Real.log ta + (19 / 100 : ℝ) * activityNu r ((M : ℝ) + 2) ^ 2 ≤
      threeRangeLambdaU r mu M ∧ 0 < threeRangeLambdaU r mu M := by
  have hta0 : 0 < ta := by linarith
  have hlog := Real.log_le_log hta0 ht
  have hgain := largeNu_upper_source hN hr0 hrh hnu hmu
  unfold V22.lambdaT at hgain
  have hfloor := largeNu_lambda_floor_pos hta hnu
  exact ⟨by linarith, by linarith⟩

end Erdos993Lean.Analytic.V22.Analysis
