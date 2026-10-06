import Erdos993Lean.Analytic.V22.Analysis.LinearizedBounds
import Erdos993Lean.Analytic.V22.Analysis.CoefficientMonotonicity
import Erdos993Lean.Analytic.V22.Analysis.SharedActivity
import Erdos993Lean.Analytic.V22.Analysis.ThreeRanges

/-!
# Paper v2.2, Lemma 4.12: large-offset facts

All numerical logarithm/root facts below use finite rational series, not
precomputed logarithms. The lower-range theorem retains the exact source
chain and zero remainder. The upper-gain algebra is separated from the
geometric error estimates; only a closed theorem is exported as a source
bound. Root owns compilation; this drafting worker runs no Lean/lake.
-/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set Finset

theorem largeNu_domains {r N : ℝ} (hN : 10 ≤ N) (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2)
    (hnu : 6 ≤ activityNu r N) :
    0 < r ∧ 4 * activityNu r N ^ 2 ≤ N ∧ 144 ≤ N := by
  have hn : 0 ≤ N := by linarith
  have hr2 := (coefficient_rm_sq_bounds hr0 hrh).2.1
  have hsq := activityNu_sq (r := r) hn
  have hnub : (36 : ℝ) ≤ activityNu r N ^ 2 :=
    (by simpa only [show (6 : ℝ) ^ 2 = 36 by norm_num] using (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 6)
      (by linarith : 0 ≤ activityNu r N)).2 hnu)
  have hbound : 4 * activityNu r N ^ 2 ≤ N := by
    nlinarith [mul_le_mul_of_nonneg_right hr2 hn]
  have hrp : 0 < r := by
    by_contra! h
    have he : r = 0 := le_antisymm h hr0
    rw [he] at hnu
    norm_num [activityNu] at hnu
  exact ⟨hrp, hbound, by linarith⟩

/-- Exact logarithmic endpoint in the source's positivity calculation. -/
theorem largeNu_log_lower_endpoint :
    -(467 / 250 : ℝ) < Real.log (387 / 2500) := by
  have he := Real.sum_le_exp_of_nonneg (x := (467 / 250 : ℝ)) (by norm_num) 10
  have hs := mul_le_mul_of_nonneg_right he (by norm_num : (0 : ℝ) ≤ 387 / 2500)
  have hrat : (1 : ℝ) <
      (∑ i ∈ range 10, (467 / 250 : ℝ) ^ i / (Nat.factorial i : ℝ)) * (387 / 2500) := by
    norm_num [Finset.sum_range_succ, Nat.factorial_succ]
  apply (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 387 / 2500)).2
  rw [Real.exp_neg, ← one_div]
  apply (div_lt_iff₀ (Real.exp_pos _)).2
  simpa only [mul_comm] using hrat.trans_le hs

theorem largeNu_lambda_floor_pos {ta nu : ℝ} (hta : (387 / 2500 : ℝ) ≤ ta) (hnu : 6 ≤ nu) :
    0 < (5 / 2 : ℝ) * Real.log ta + (19 / 100 : ℝ) * nu ^ 2 := by
  have hta0 : 0 < ta := by linarith
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 387 / 2500) hta
  have hs : (36 : ℝ) ≤ nu ^ 2 :=
    (by simpa only [show (6 : ℝ) ^ 2 = 36 by norm_num] using (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 6) (by linarith : 0 ≤ nu)).2 hnu)
  linarith [largeNu_log_lower_endpoint]

/-- A rational exponential lower sum proves the upper activity logarithm. -/
theorem largeNu_log_upper_endpoint : Real.log (321 / 200 : ℝ) ≤ 19 / 40 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 321 / 200)).2
  refine le_trans ?_ (Real.sum_le_exp_of_nonneg (x := (19 / 40 : ℝ)) (by norm_num) 6)
  norm_num [Finset.sum_range_succ, Nat.factorial_succ]

/-- The six-term negative-log series gives the source's root comparison. -/
theorem largeNu_log_root_endpoint : (71 / 100 : ℝ) ≤ Real.log (51 / 25) := by
  have h := gaussianLambda_le_neg_rootEquation (a := (26 / 51 : ℝ)) (by norm_num) (by norm_num)
  unfold rootEquation at h
  have heq : 1 + -(26 / 51 : ℝ) = (51 / 25 : ℝ)⁻¹ := by norm_num
  rw [heq, Real.log_inv] at h
  norm_num [gaussianLambda] at h
  linarith

theorem largeNu_root_upper_endpoint : rootMap (7 / 4 : ℝ) ≤ 26 / 25 := by
  have he : (7 / 4 : ℝ) ≤ rootEquation (26 / 25) := by
    unfold rootEquation
    norm_num
    linarith [largeNu_log_root_endpoint]
  have h := rootMap_monotone he
  rw [rootMap_eq_of_equation (s := (26 / 25 : ℝ)) (by norm_num) rfl] at h
  exact h

theorem largeNu_Z0_upper {N : ℝ} (hN : 144 ≤ N) : V22.Z0 N ≤ 1 / 12 := by
  have hn : 0 ≤ N := by linarith
  have hN10 : 10 ≤ N := by linarith
  have hs : (V22.Z0 N) ^ 2 ≤ (1 / 12 : ℝ) ^ 2 := by
    rw [coefficient_Z0_sq hN10]
    apply (div_le_iff₀ (sq_pos_of_pos (show 0 < N + 1 by linarith))).2
    nlinarith [mul_nonneg hn (show 0 ≤ N - 144 by linarith)]
  exact (sq_le_sq₀ (coefficient_Z0_pos hN10).le (by norm_num)).1 hs

theorem largeNu_monotonePhi_upper {r N : ℝ} (hN : 144 ≤ N) (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) :
    0 ≤ monotonePhi r N ∧ monotonePhi r N ≤ 13 / 12 := by
  have hn : 0 < N := by linarith
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hn
  have hs12 : (12 : ℝ) ≤ Real.sqrt N := Real.le_sqrt_of_sq_le (by nlinarith)
  have heq : monotonePhi r N = 1 + 2 * r / Real.sqrt N := by
    unfold monotonePhi activityNu
    field_simp [hn.ne', hs.ne'] <;> nlinarith [Real.sq_sqrt hn.le]
  have hdiv : 2 * r / Real.sqrt N ≤ (1 / 12 : ℝ) := by
    apply (div_le_iff₀ hs).2
    linarith
  rw [heq]
  exact ⟨by positivity, by linarith⟩

/-- Both exact quartic ratios are bounded without a finite-check premise. -/
theorem largeNu_Psi_upper {r N : ℝ} (hN : 144 ≤ N) (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) :
    max (monotonePsiL r N) (monotonePsiR r N) ≤ 3 := by
  have hN10 : 10 ≤ N := by linarith
  have hn : 0 < N := by linarith
  have hz0 := (coefficient_Z0_pos hN10).le
  have hz := largeNu_Z0_upper hN
  have hp := largeNu_monotonePhi_upper hN hr0 hrh
  have hd := coefficient_one_sub_rm_sq_pos hr0 hrh
  have hdlo := (coefficient_rm_sq_bounds hr0 hrh).2.2
  have hprod : V22.Z0 N * monotonePhi r N ≤ (13 / 144 : ℝ) := by
    have h := mul_le_mul hz hp.2 hp.1 (by norm_num : (0 : ℝ) ≤ 1 / 12)
    norm_num at h
    exact h
  have hprodSq := (sq_le_sq₀ (mul_nonneg hz0 hp.1)
    (by norm_num : (0 : ℝ) ≤ 13 / 144)).2 hprod
  have hZsq := (sq_le_sq₀ hz0 (by norm_num : (0 : ℝ) ≤ 1 / 12)).2 hz
  have hph4 := pow_le_pow_left₀ hp.1 hp.2 4
  have hX : 1 - (13 / 144 : ℝ) ^ 2 ≤ 1 - (V22.Z0 N) ^ 2 * (monotonePhi r N) ^ 2 := by
    nlinarith
  have hX0 : 0 ≤ 1 - (V22.Z0 N) ^ 2 * (monotonePhi r N) ^ 2 := by nlinarith
  have hdenL := mul_le_mul hX hdlo (by norm_num : (0 : ℝ) ≤ 3 / 4) hX0
  have hnumL := mul_le_mul hph4 (show 1 - (V22.Z0 N) ^ 2 ≤ 1 by nlinarith)
    (show 0 ≤ 1 - (V22.Z0 N) ^ 2 by nlinarith) (by norm_num : (0 : ℝ) ≤ (13 / 12) ^ 4)
  have hsum : r + V22.Z0 N ≤ (7 / 12 : ℝ) := by linarith
  have hsumSq := (sq_le_sq₀ (add_nonneg hr0 hz0)
    (by norm_num : (0 : ℝ) ≤ 7 / 12)).2 hsum
  have hY : 1 - (7 / 12 : ℝ) ^ 2 ≤ 1 - (r + V22.Z0 N) ^ 2 := by nlinarith
  have hdenR := mul_le_mul hY hdlo (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (show 0 ≤ 1 - (r + V22.Z0 N) ^ 2 by nlinarith)
  apply max_le
  · unfold monotonePsiL
    rw [activityNu_quotient hn]
    apply (div_le_iff₀ (show 0 <
      (1 - (V22.Z0 N) ^ 2 * (monotonePhi r N) ^ 2) * (1 - r ^ 2) by nlinarith)).2
    norm_num at hdenL hnumL
    nlinarith
  · rw [monotone_PsiR_ratio hr0 hrh hN10]
    apply (div_le_iff₀ (show 0 < (1 - (r + V22.Z0 N) ^ 2) * (1 - r ^ 2) by nlinarith)).2
    norm_num at hdenR
    nlinarith [sq_nonneg (V22.Z0 N)]

theorem largeNu_eL_bounds {r N : ℝ} (hN : 10 ≤ N) (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2)
    (hnu : 6 ≤ activityNu r N) :
    (N + 1) * V22.eL r N ≤ (123 / 50 : ℝ) * activityNu r N ∧
      V22.eL r N ≤ 103 / 1000 := by
  obtain ⟨_, hfour, hN144⟩ := largeNu_domains hN hr0 hrh hnu
  have hn : 0 < N := by linarith
  have hnu0 : 0 ≤ activityNu r N := by linarith
  have hd := coefficient_one_sub_rm_sq_pos hr0 hrh
  have hrsq := (coefficient_rm_sq_bounds hr0 hrh).2.1
  have hdlo := (coefficient_rm_sq_bounds hr0 hrh).2.2
  have hroot : (200 / 231 : ℝ) ≤ Real.sqrt (1 - r ^ 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have heps : 2 * activityNu r N / Real.sqrt (1 - r ^ 2) ≤
      (231 / 100 : ℝ) * activityNu r N := by
    have hcoef := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (0 : ℝ) < 200 / 231) hroot
    norm_num at hcoef
    have h := mul_le_mul_of_nonneg_right hcoef hnu0
    convert h using 1 <;> ring
  have hc : 2 * activityNu r N ^ 2 / (N - activityNu r N ^ 2) ≤ (2 / 3 : ℝ) := by
    rw [activityNu_gap hn, activityNu_sq hn.le]
    have heq : 2 * (r ^ 2 * N) / (N * (1 - r ^ 2)) = 2 * r ^ 2 / (1 - r ^ 2) := by
      field_simp [hn.ne', hd.ne'] <;> ring
    rw [heq]
    apply (div_le_iff₀ hd).2
    nlinarith
  have hpsi := largeNu_Psi_upper hN144 hr0 hrh
  have hraw := monotone_eL_upper hr0 hrh hN
  rw [activityNu_quotient hn] at hraw
  have hscaled : (N + 1) * V22.eL r N ≤ (123 / 50 : ℝ) * activityNu r N := by
    linarith
  have hquad : (123 / 50 : ℝ) * activityNu r N ≤
      (103 / 1000 : ℝ) * (4 * activityNu r N ^ 2 + 1) := by
    nlinarith [mul_nonneg hnu0 (show 0 ≤ activityNu r N - 6 by linarith)]
  have hgoal : (123 / 50 : ℝ) * activityNu r N ≤ (103 / 1000 : ℝ) * (N + 1) := by
    linarith
  have hfinal : (N + 1) * V22.eL r N ≤ (N + 1) * (103 / 1000 : ℝ) := by
    linarith [hscaled.trans hgoal]
  exact ⟨hscaled, (mul_le_mul_iff_right₀ (show 0 < N + 1 by linarith)).mp
    (by simpa only [mul_comm] using hfinal)⟩

theorem largeNu_hbar_upper {N : ℝ} (hN : 144 ≤ N) : V22.hbar (N - 2) ≤ (393 / 14500 : ℝ) := by
  have hM : 0 < N - 2 := by linarith
  have hk : V22.kbar (N - 2) ≤ (393 / 100 : ℝ) := by
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 10)
      (by norm_num : (0 : ℝ) < 142) (show (142 : ℝ) ≤ N - 2 by linarith)
    unfold V22.kbar
    linarith
  unfold V22.hbar
  have hden : (145 : ℝ) ≤ N - 2 + 3 := by linarith
  have h := div_le_div₀ (by norm_num : (0 : ℝ) ≤ 393 / 100) hk (by norm_num : (0 : ℝ) < 145) hden
  norm_num at h
  exact h

/-- Exact source upper root factor, for every permitted template log-ratio. -/
theorem largeNu_lower_root_factor {r N t lambdaT : ℝ} (hN : 10 ≤ N) (hr0 : 0 ≤ r)
    (hrh : r ≤ 1 / 2) (hnu : 6 ≤ activityNu r N) (ht0 : 0 < t) (ht1 : t ≤ 321 / 200)
    (hlambda : lambdaT ≤ V22.lambdaT t + V22.hbar (N - 2)) :
    V22.positivePart (V22.rootMap (lambdaT + V22.eL r N)) ≤ (26 / 25 : ℝ) := by
  obtain ⟨_, _, hN144⟩ := largeNu_domains hN hr0 hrh hnu
  have he := (largeNu_eL_bounds hN hr0 hrh hnu).2
  have hh := largeNu_hbar_upper hN144
  have hlog := (Real.log_le_log ht0 ht1).trans largeNu_log_upper_endpoint
  have hlam : lambdaT + V22.eL r N ≤ (33 / 25 : ℝ) := by
    unfold V22.lambdaT at hlambda
    linarith
  have hroot := rootMap_monotone (show lambdaT + V22.eL r N ≤ (7 / 4 : ℝ) by linarith)
  rw [shared_rootMap_eq]
  unfold V22.positivePart
  exact max_le (hroot.trans largeNu_root_upper_endpoint) (by norm_num)

noncomputable def largeNuLowerRemainder (r N lambdaT : ℝ) : ℝ :=
  V22.positivePart (2 * (N + 1) * V22.eL r N *
    V22.positivePart (V22.rootMap (lambdaT + V22.eL r N)) - N * V22.Delta r N * (1 - V22.eL r N))

/-- Source Lemma 4.12(b): the two exact bonus comparisons and root-factor
bound, before substituting either genuine U/L template log-ratio. -/
theorem largeNu_lower_chain {r N t lambdaT : ℝ} (hN : 10 ≤ N) (hr0 : 0 ≤ r)
    (hrh : r ≤ 1 / 2) (hnu : 6 ≤ activityNu r N) (ht0 : 0 < t) (ht1 : t ≤ 321 / 200)
    (hlambda : lambdaT ≤ V22.lambdaT t + V22.hbar (N - 2)) :
    (128 : ℝ) * activityNu r N ^ 2 ≤ N * V22.Delta r N * (1 - V22.eL r N) ∧
    (128 / 25 : ℝ) * activityNu r N < 128 * activityNu r N ^ 2 ∧
    2 * (N + 1) * V22.eL r N * V22.positivePart (V22.rootMap (lambdaT + V22.eL r N)) ≤
      (128 / 25 : ℝ) * activityNu r N ∧
    largeNuLowerRemainder r N lambdaT = 0 := by
  obtain ⟨_, _, hN144⟩ := largeNu_domains hN hr0 hrh hnu
  have hnu0 : 0 ≤ activityNu r N := by linarith
  have hrb : r ^ 2 < 1 := by nlinarith [(coefficient_rm_sq_bounds hr0 hrh).2.1]
  have hbonus := scaled_delta_lower hN hrb
  have hbonus143 : (143 : ℝ) * activityNu r N ^ 2 ≤ N * V22.Delta r N := by
    nlinarith [mul_nonneg (show 0 ≤ N - 144 by linarith) (sq_nonneg (activityNu r N))]
  have he := largeNu_eL_bounds hN hr0 hrh hnu
  have hroot := largeNu_lower_root_factor hN hr0 hrh hnu ht0 ht1 hlambda
  have hbonusPay := mul_le_mul hbonus143 (show (897 / 1000 : ℝ) ≤ 1 - V22.eL r N by linarith)
    (by norm_num : (0 : ℝ) ≤ 897 / 1000) (by nlinarith [sq_nonneg (activityNu r N)] : 0 ≤ N * V22.Delta r N)
  have hbonus128 : (128 : ℝ) * activityNu r N ^ 2 ≤ N * V22.Delta r N * (1 - V22.eL r N) := by
    nlinarith [sq_nonneg (activityNu r N)]
  have hstrict : (128 / 25 : ℝ) * activityNu r N < 128 * activityNu r N ^ 2 := by
    nlinarith [mul_nonneg hnu0 (show 0 ≤ activityNu r N - 6 by linarith)]
  have hpp0 : 0 ≤ V22.positivePart (V22.rootMap (lambdaT + V22.eL r N)) := le_max_right _ _
  have hprod := mul_le_mul he.1 hroot hpp0
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 123 / 50) hnu0)
  have hcost : 2 * (N + 1) * V22.eL r N * V22.positivePart (V22.rootMap (lambdaT + V22.eL r N)) ≤
      (128 / 25 : ℝ) * activityNu r N := by
    nlinarith
  refine ⟨hbonus128, hstrict, hcost, ?_⟩
  have hdiff : 2 * (N + 1) * V22.eL r N * V22.positivePart (V22.rootMap (lambdaT + V22.eL r N)) -
      N * V22.Delta r N * (1 - V22.eL r N) ≤ 0 := by linarith
  exact max_eq_right hdiff

/-- The genuine U/L activity-one template shift has the source upper cap;
no template comparison is added as a public premise. -/
theorem largeNu_template_upper {M : ℕ} {mu : ℝ} (hM : 8 ≤ M) (hmu : 0 < mu)
    (side : ActivityOneSide) :
    activityOneLambda M mu side ≤ V22.lambdaT ((M : ℝ) / mu) + V22.hbar (M : ℝ) := by
  rw [activityOneLambda_shift (by omega : 1 ≤ M) hmu side]
  have hk := (activityOneK_bounds hM side).2
  have hdiv := div_le_div_of_nonneg_right hk
    (show 0 ≤ (M : ℝ) + 3 by positivity)
  simpa only [activityOneLambda_t, V22.lambdaT, V22.hbar, V22.kbar] using
    (show activityOneLambda_t ((M : ℝ) / mu) +
      activityOneK M side / ((M : ℝ) + 3) ≤
      activityOneLambda_t ((M : ℝ) / mu) +
      ((77 / 20 : ℝ) + 10 / (M : ℝ)) / ((M : ℝ) + 3) by linarith)

/-- Paper v2.2, Lemma 4.12(b), for each genuine template prefactor.
The exact source bonus chain is retained, and DL is zero. -/
theorem largeNu_lower_source {M : ℕ} {r mu : ℝ} (hN : 10 ≤ M + 2)
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hnu : 6 ≤ activityNu r ((M : ℝ) + 2))
    (hmu : 0 < mu) (ht : (M : ℝ) / mu ≤ 321 / 200) (side : ActivityOneSide) :
    (128 : ℝ) * activityNu r ((M : ℝ) + 2) ^ 2 ≤
      ((M : ℝ) + 2) * V22.Delta r ((M : ℝ) + 2) * (1 - V22.eL r ((M : ℝ) + 2)) ∧
    (128 / 25 : ℝ) * activityNu r ((M : ℝ) + 2) <
      128 * activityNu r ((M : ℝ) + 2) ^ 2 ∧
    2 * ((M : ℝ) + 3) * V22.eL r ((M : ℝ) + 2) *
      V22.positivePart (V22.rootMap (activityOneLambda M mu side +
        V22.eL r ((M : ℝ) + 2))) ≤ (128 / 25 : ℝ) * activityNu r ((M : ℝ) + 2) ∧
    largeNuLowerRemainder r ((M : ℝ) + 2) (activityOneLambda M mu side) = 0 := by
  have hM : 8 ≤ M := by omega
  have hMr : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hn : (10 : ℝ) ≤ (M : ℝ) + 2 := by exact_mod_cast hN
  have hlam := largeNu_template_upper hM hmu side
  have heq : (M : ℝ) + 2 - 2 = (M : ℝ) := by ring
  have hlambda : activityOneLambda M mu side ≤ V22.lambdaT ((M : ℝ) / mu) +
      V22.hbar ((M : ℝ) + 2 - 2) := by simpa only [heq] using hlam
  simpa only [show ((M : ℝ) + 2) + 1 = (M : ℝ) + 3 by ring] using
    (largeNu_lower_chain hn hr0 hrh hnu (div_pos hMr hmu) ht hlambda)

end Erdos993Lean.Analytic.V22.Analysis
