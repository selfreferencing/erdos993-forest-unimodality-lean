import Erdos993Lean.Analytic.V22.Analysis.BonusRangeBounds
import Erdos993Lean.Analytic.V22.Analysis.CappedRemainderMonotonicity
import Erdos993Lean.Analytic.V22.Analysis.LambdaBonus
import Erdos993Lean.Analytic.V22.Analysis.LargeNuUpper
import Erdos993Lean.Analytic.V22.Analysis.FiberInfimum

/-!
# Source spike rays, including retained finite and infinite blocks

Frozen source labels `lem:defL` and `lem:Phi`. The actual integer atom and
the all-integer attained infimum are retained. Finite block coefficients
keep both endpoints, the bounded displacement cap, and the shifted slope
from the source quadratic coefficient. Parent owns all Lean compilation.
-/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

theorem spike_lower_template_negative {M : ℕ} (hM : 8 ≤ M) {mu : ℝ}
    (hmu : 0 < mu) (ht : (M : ℝ) / mu ≤ 69 / 100) :
    activityOneLambda M mu .L < 0 := by
  have hMr : (8 : ℝ) ≤ M := by exact_mod_cast hM
  have ht0 : 0 < (M : ℝ) / mu := div_pos (by linarith) hmu
  have hlog := Real.log_le_sub_one_of_pos ht0
  have hk := (activityOneK_bounds hM ActivityOneSide.L).2
  have hten : (10 : ℝ) / M ≤ 10 / 8 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hMr
  have hnum : activityOneK M .L ≤ (51 / 10 : ℝ) := by linarith
  have hfrac : activityOneK M .L / ((M : ℝ) + 3) ≤ (51 / 110 : ℝ) := by
    calc
      _ ≤ (51 / 10 : ℝ) / ((M : ℝ) + 3) := div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ (51 / 10 : ℝ) / 11 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
      _ = _ := by norm_num
  rw [activityOneLambda_shift (by omega : 1 ≤ M) hmu .L]
  unfold activityOneLambda_t
  linarith

/-- Source Lemma 5.2, for every integer in the actual lower range. -/
theorem source_spike_lower_range {M : ℕ} (hN : 10 ≤ M + 2) {r mu : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hmu : 0 < mu)
    (ht : (M : ℝ) / mu ≤ 69 / 100) (j : ℤ) (hw : threeRangeW r M j ≤ 1) :
    V22.psi ((M : ℝ) / mu) - max
      (-(9 / 2 : ℝ) * ((M : ℝ) / mu - 1) ^ 2 +
        (2 * ((M : ℝ) / mu) / (M : ℝ)) * ((M : ℝ) + 3) * V22.eL r ((M : ℝ) + 2)) 0 ≤
      V22.fiberFunction ((1 + r) / 2) mu M j := by
  let N : ℝ := (M : ℝ) + 2
  let e := V22.eL r N
  let rhoL := threeRangeRhoL r N
  let B : ℝ := N / mu
  have hMr : (8 : ℝ) ≤ M := by exact_mod_cast (show 8 ≤ M by omega)
  have hNr : 10 ≤ N := by dsimp [N]; exact_mod_cast hN
  have hn : 0 < N := by linarith
  have hr1 : r < 1 := by linarith
  have he : 0 ≤ e := bonusRange_eL_nonneg hn hr0 hr1
  have hRhoL : 0 < rhoL := threeRangeRhoL_pos hr0 hr1 M
  have hB : 0 < B := div_pos hn hmu
  have hRho : 0 < V22.rho N := by unfold V22.rho; positivity
  have hRhoLE : V22.rho N ≤ rhoL := by
    have heps := shared_epsilon_nonneg hr0 hr1 hn
    dsimp [rhoL, threeRangeRhoL]
    linarith
  have hTL := spike_lower_template_negative (by omega : 8 ≤ M) hmu ht
  have hF := threeRanges_lower hN hr0 hrh hmu j hw
  have hmin : B * (1 - 2 / rhoL * e) ≤
      rootMinorant (threeRangePL r mu M) B rhoL (V22.gamma r N) (threeRangeW r M j) := by
    by_cases hl : threeRangeLambdaL r mu M ≤ 0
    · have hplain := bonusRange_lower_nonpos (threeRangePL_pos hmu r M) hB hRhoL
        (threeRange_gamma_ge_one hr0 hr1 M) hl _ hw
      have hBe : 0 ≤ B * (2 / rhoL * e) := by positivity
      linarith
    · have hgl := rootG_le_lambda (by linarith : 0 ≤ threeRangeLambdaL r mu M)
      have hlam := threeRanges_lambdaL_upper hN hr0 hrh hmu
      change threeRangeLambdaL r mu M ≤ activityOneLambda M mu .L + rhoL / 2 * V22.Delta r N + e at hlam
      have hscaled := mul_le_mul_of_nonneg_left (hgl.trans (show threeRangeLambdaL r mu M ≤
        rhoL / 2 * V22.Delta r N + e by linarith)) (show 0 ≤ 2 / rhoL by positivity)
      have hident : V22.gamma r N - 2 / rhoL * (rhoL / 2 * V22.Delta r N + e) =
          1 - 2 / rhoL * e := by
        unfold V22.gamma
        field_simp [hRhoL.ne'] <;> ring
      have hglobal := rootMinorant_lower_bound (threeRangePL_pos hmu r M) hB hRhoL
        (V22.gamma r N) (threeRangeW r M j)
      have hpay := mul_le_mul_of_nonneg_left (show 1 - 2 / rhoL * e ≤
        V22.gamma r N - 2 / rhoL * rootG (threeRangeLambdaL r mu M) by linarith) hB.le
      exact hpay.trans hglobal
  have hfin : B * (1 - 2 / rhoL * e) ≤ V22.fiberFunction ((1 + r) / 2) mu M j := hmin.trans hF
  have hinv := one_div_le_one_div_of_le hRho hRhoLE
  have hInvEq : 1 / V22.rho N = (N + 1) / N := by
    unfold V22.rho
    field_simp [hn.ne', (show N + 1 ≠ 0 by linarith)]
  rw [hInvEq] at hinv
  have hscaled := mul_le_mul_of_nonneg_right hinv (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hB.le) he)
  have hraw : V22.psi ((M : ℝ) / mu) - V22.fiberFunction ((1 + r) / 2) mu M j ≤
      -(9 / 2 : ℝ) * ((M : ℝ) / mu - 1) ^ 2 + 2 * (N + 1) * e / mu := by
    have hid : V22.psi ((M : ℝ) / mu) - B =
        -(9 / 2 : ℝ) * ((M : ℝ) / mu - 1) ^ 2 - 2 / mu := by
      dsimp [B, N]
      unfold V22.psi
      ring
    have hloss : ((N + 1) / N) * (2 * B * e) = 2 * (N + 1) * e / mu := by
      dsimp [B]
      field_simp [hn.ne', hmu.ne'] <;> ring
    rw [hloss] at hscaled
    have hfin' : B - (1 / rhoL) * (2 * B * e) ≤
        V22.fiberFunction ((1 + r) / 2) mu M j := by
      convert hfin using 1 <;> ring
    have htwo : 0 < (2 : ℝ) / mu := div_pos (by norm_num) hmu
    linarith only [hfin', hscaled, hid, htwo]
  have hprice : (2 * ((M : ℝ) / mu) / (M : ℝ)) * ((M : ℝ) + 3) * V22.eL r ((M : ℝ) + 2) =
      2 * (N + 1) * e / mu := by
    dsimp [N, e]
    field_simp [hmu.ne', (show (M : ℝ) ≠ 0 by linarith)] <;> ring
  rw [hprice]
  linarith [le_max_left (-(9 / 2 : ℝ) * ((M : ℝ) / mu - 1) ^ 2 + 2 * (N + 1) * e / mu) (0 : ℝ)]

theorem shared_phiWithRemainder_eq (t M D : ℝ) :
    V22.phiWithRemainder t M D = activityOnePhiWithRemainder t M D := by
  simp only [V22.phiWithRemainder, activityOnePhiWithRemainder, activityOneLossMax,
    activityOneLossTerm, V22.positivePart, V22.kbar, shared_gaussianSlack_eq,
    shared_G_eq, shared_G1_eq, shared_G2_eq, activityOneG0, activityOneG1, activityOneG2,
    shared_lambdaT_eq]

theorem spike_template_negative_bound {M t D : ℝ} (hM : 0 ≤ M) :
    -activityOneT t M + D ≤ M * max (-activityOneS t) 0 +
      max (6 * activityOneG0 t - 2 + D + activityOneLossMax t M) 0 := by
  have hslack := mul_le_mul_of_nonneg_left (le_max_left (-activityOneS t) (0 : ℝ)) hM
  have hmax := le_max_left (6 * activityOneG0 t - 2 + D + activityOneLossMax t M) (0 : ℝ)
  have hE1 := le_max_left (activityOneLossTerm t M (71 / 20))
    (activityOneLossTerm t M ((77 / 20 : ℝ) + 10 / M))
  have hE2 := le_max_right (activityOneLossTerm t M (71 / 20))
    (activityOneLossTerm t M ((77 / 20 : ℝ) + 10 / M))
  unfold activityOneT
  rcases le_total (activityOneEndpointValue t M (71 / 20))
    (activityOneEndpointValue t M ((77 / 20 : ℝ) + 10 / M)) with hm | hm
  · rw [min_eq_left hm]
    unfold activityOneEndpointValue
    unfold activityOneLossMax at hmax ⊢
    unfold activityOneLossTerm at hE1 hmax ⊢
    linarith only [hslack, hmax, hE1]
  · rw [min_eq_right hm]
    unfold activityOneEndpointValue
    unfold activityOneLossMax at hmax ⊢
    unfold activityOneLossTerm at hE2 hmax ⊢
    linarith only [hslack, hmax, hE2]

/-- The exact ray formula pays the template deficit for every positive
fiber size, independently of either root-derivative sign. -/
theorem spike_phi_pays_template {M : ℕ} (hM : 1 ≤ M) {mu D : ℝ} (hmu : 0 < mu) :
    -activityOneT ((M : ℝ) / mu) (M : ℝ) + D ≤
      mu * V22.phiWithRemainder ((M : ℝ) / mu) (M : ℝ) D := by
  have h := spike_template_negative_bound (D := D) (t := (M : ℝ) / mu) (Nat.cast_nonneg M)
  have heq : mu * V22.phiWithRemainder ((M : ℝ) / mu) (M : ℝ) D =
      (M : ℝ) * max (-activityOneS ((M : ℝ) / mu)) 0 +
        max (6 * activityOneG0 ((M : ℝ) / mu) - 2 + D + activityOneLossMax ((M : ℝ) / mu) M) 0 := by
    rw [shared_phiWithRemainder_eq]
    unfold activityOnePhiWithRemainder
    field_simp [hmu.ne', (show (M : ℝ) ≠ 0 by exact_mod_cast (by omega : M ≠ 0))]
  rw [heq]
  exact h

theorem spike_phi_nonneg {t M D : ℝ} (ht : 0 ≤ t) (hM : 0 ≤ M) :
    0 ≤ V22.phiWithRemainder t M D := by
  rw [shared_phiWithRemainder_eq]
  unfold activityOnePhiWithRemainder
  exact add_nonneg (mul_nonneg ht (le_max_right _ _))
    (mul_nonneg (div_nonneg ht hM) (le_max_right _ _))

/-- The attained native infimum consumes the three source ranges. The
supplied upper remainder is immediately consumed here; later theorems
instantiate it with the fully proved finite or infinite block formula. -/
theorem spike_ray_deficit_of_upper_remainder {M : ℕ} (hM : 8 ≤ M)
    {r mu rm D : ℝ} (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hrmh : rm ≤ 1 / 2)
    (hmu : 0 < mu) (ht0 : (387 / 2500 : ℝ) ≤ (M : ℝ) / mu)
    (ht1 : (M : ℝ) / mu ≤ 69 / 100)
    (hL : (2 * ((M : ℝ) / mu) / (M : ℝ)) * ((M : ℝ) + 3) * V22.eL r ((M : ℝ) + 2) ≤
      (9 / 2 : ℝ) * ((M : ℝ) / mu - 1) ^ 2)
    (hDU : threeRangeLambdaU r mu M < 0 → activityNu r ((M : ℝ) + 2) < 6 → bonusRangeDUPrime r mu M ≤ D) :
    V22.deficitG ((1 + r) / 2) mu 0 0 M ≤ V22.phiWithRemainder ((M : ℝ) / mu) M D := by
  have hN : 10 ≤ M + 2 := by omega
  have hrh := hrrm.trans hrmh
  have hPhi := spike_phi_nonneg (D := D) (by linarith : 0 ≤ (M : ℝ) / mu) (Nat.cast_nonneg M)
  have hpay := spike_phi_pays_template (D := D) (by omega : 1 ≤ M) hmu
  have hpoint : ∀ j : ℤ, V22.psi ((M : ℝ) / mu) - V22.phiWithRemainder ((M : ℝ) / mu) M D ≤
      V22.fiberFunction ((1 + r) / 2) mu M j := by
    intro j
    by_cases hwl : threeRangeW r M j ≤ 1
    · have hlower := source_spike_lower_range hN hr0 hrh hmu ht1 j hwl
      rw [max_eq_right (by linarith)] at hlower
      linarith
    by_cases hwm : threeRangeW r M j ≤ V22.gamma r ((M : ℝ) + 2)
    · have hmiddle := bonusRange_middle hN hr0 hrh hmu j (by linarith) hwm
      rw [← shared_psi_eq] at hmiddle
      nlinarith
    have hwu : V22.gamma r ((M : ℝ) + 2) ≤ threeRangeW r M j := by linarith
    by_cases hl : 0 ≤ threeRangeLambdaU r mu M
    · have hu := bonusRange_upper_nonnegative_fiber hN hr0 hrh hmu hl j hwu
      rw [← shared_psi_eq] at hu
      nlinarith
    have hneg : threeRangeLambdaU r mu M < 0 := by linarith
    have hnu : activityNu r ((M : ℝ) + 2) < 6 := by
      by_contra hlarge
      have hpos := (largeNu_upper_positive hN hr0 hrh (by linarith) hmu ht0 le_rfl).2
      linarith
    have hdu := hDU hneg hnu
    have hu := bonusRange_upper_negative_fiber hN hr0 hrh hmu hneg j hwu
    rw [← shared_psi_eq] at hu
    nlinarith
  obtain ⟨j, hj, _⟩ := shared_fiberInfimum_attained (mu := mu)
    (by linarith : 0 ≤ (1 + r) / 2) (by linarith : (1 + r) / 2 ≤ 1) M
  have h := hpoint j
  rw [← hj] at h
  unfold V22.deficitG V22.positivePart V22.targetLine
  norm_num only [zero_mul, add_zero]
  exact max_le (by linarith) hPhi

theorem spike_fraction_mono {c x y : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) (hxy : x ≤ y) :
    x / Real.sqrt (1 + c * x ^ 2) ≤ y / Real.sqrt (1 + c * y ^ 2) := by
  have hy := hx.trans hxy
  have hdx : 0 < 1 + c * x ^ 2 := by positivity
  have hdy : 0 < 1 + c * y ^ 2 := by positivity
  have hsx := Real.sqrt_pos.2 hdx
  have hsy := Real.sqrt_pos.2 hdy
  apply (div_le_div_iff₀ hsx hsy).2
  apply (sq_le_sq₀ (mul_nonneg hx hsy.le) (mul_nonneg hy hsx.le)).mp
  have hid : (x * Real.sqrt (1 + c * y ^ 2)) ^ 2 = x ^ 2 * (1 + c * y ^ 2) := by
    rw [mul_pow, Real.sq_sqrt hdy.le]
  have hid' : (y * Real.sqrt (1 + c * x ^ 2)) ^ 2 = y ^ 2 * (1 + c * x ^ 2) := by
    rw [mul_pow, Real.sq_sqrt hdx.le]
  rw [hid, hid']
  nlinarith [(sq_le_sq₀ hx hy).2 hxy]

theorem spike_fraction_c_antitone {c d x : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) (hx : 0 ≤ x) :
    x / Real.sqrt (1 + d * x ^ 2) ≤ x / Real.sqrt (1 + c * x ^ 2) := by
  apply div_le_div_of_nonneg_left hx (Real.sqrt_pos.2 (by positivity))
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x])

theorem spike_cubic_fraction_mono {c x y : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) (hxy : x ≤ y) :
    x ^ 3 / Real.sqrt (1 + c * x ^ 2) ≤ y ^ 3 / Real.sqrt (1 + c * y ^ 2) := by
  have hf := spike_fraction_mono hc hx hxy
  have hs := (sq_le_sq₀ hx (hx.trans hxy)).2 hxy
  have hprod := mul_le_mul hs hf
    (div_nonneg hx (Real.sqrt_nonneg _)) (sq_nonneg y)
  convert hprod using 1 <;> ring

noncomputable def spikeEpsilonCap (N rm nu : ℝ) : ℝ :=
  (2 / (N + 1)) * (nu / Real.sqrt (1 + V22.cCoef N * nu ^ 2)) +
    (1 / (3 * N * (1 - rm ^ 2))) * (nu ^ 3 / Real.sqrt (1 + V22.cCoef N * nu ^ 2))

theorem spikeEpsilonCap_mono {N rm x y : ℝ} (hN : 10 ≤ N) (hr0 : 0 ≤ rm)
    (hrh : rm ≤ 1 / 2) (hx : 0 ≤ x) (hxy : x ≤ y) : spikeEpsilonCap N rm x ≤ spikeEpsilonCap N rm y := by
  have hc : 0 ≤ V22.cCoef N := by linarith [linearized_cCoef_lower hN]
  have hd := coefficient_one_sub_rm_sq_pos hr0 hrh
  unfold spikeEpsilonCap
  exact add_le_add
    (mul_le_mul_of_nonneg_left (spike_fraction_mono hc hx hxy) (by positivity))
    (mul_le_mul_of_nonneg_left (spike_cubic_fraction_mono hc hx hxy) (by positivity))

theorem spikeEpsilonCap_antitone_N {N1 N rm nu : ℝ} (hN1 : 10 ≤ N1) (hNN : N1 ≤ N)
    (hr0 : 0 ≤ rm) (hrh : rm ≤ 1 / 2) (hnu : 0 ≤ nu) : spikeEpsilonCap N rm nu ≤ spikeEpsilonCap N1 rm nu := by
  have hn1 : 0 < N1 := by linarith
  have hn : 0 < N := by linarith
  have hd := coefficient_one_sub_rm_sq_pos hr0 hrh
  have hc : 0 ≤ V22.cCoef N1 := by linarith [linearized_cCoef_lower hN1]
  have hf := spike_fraction_c_antitone hc (coefficient_cCoef_monotone hN1 hNN) hnu
  have hcub : nu ^ 3 / Real.sqrt (1 + V22.cCoef N * nu ^ 2) ≤
      nu ^ 3 / Real.sqrt (1 + V22.cCoef N1 * nu ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hf (sq_nonneg nu)
    convert h using 1 <;> ring
  have ha : (2 : ℝ) / (N + 1) ≤ 2 / (N1 + 1) :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  have hb : (1 : ℝ) / (3 * N * (1 - rm ^ 2)) ≤ 1 / (3 * N1 * (1 - rm ^ 2)) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_right (by linarith : 3 * N1 ≤ 3 * N) hd.le)
  unfold spikeEpsilonCap
  exact add_le_add (mul_le_mul ha hf (by positivity) (by positivity))
    (mul_le_mul hb hcub (by positivity) (by positivity))

theorem spike_epsilon_ratio_cap {r rm N : ℝ} (hN : 10 ≤ N) (hr0 : 0 ≤ r)
    (hrrm : r ≤ rm) (hrmh : rm ≤ 1 / 2) :
    V22.epsilonPrime r N / Real.sqrt (V22.gamma r N) ≤ spikeEpsilonCap N rm (activityNu r N) := by
  have hn : 0 < N := by linarith
  have hrm0 := hr0.trans hrrm
  have hrh := hrrm.trans hrmh
  have hd := coefficient_one_sub_rm_sq_pos hr0 hrh
  have hdm := coefficient_one_sub_rm_sq_pos hrm0 hrmh
  have hnu := activityNu_nonneg (N := N) hr0
  have hc : 0 ≤ V22.cCoef N := by linarith [linearized_cCoef_lower hN]
  have hs : 0 < Real.sqrt (1 + V22.cCoef N * activityNu r N ^ 2) := by positivity
  have ha : activityNu r N ^ 2 < N := by
    rw [activityNu_sq hn.le]
    nlinarith [(coefficient_rm_sq_bounds hr0 hrh).2.1]
  have h := monotone_epsilon_over_gamma hr0 hrh hN ha le_rfl
  have hden : 1 + monotoneDeltaA r N N = 1 + V22.cCoef N * activityNu r N ^ 2 := by
    unfold monotoneDeltaA V22.cCoef
    ring
  rw [hden] at h
  have hsq := (sq_le_sq₀ hr0 hrm0).2 hrrm
  have hreplace : activityNu r N ^ 3 / (3 * N * (1 - r ^ 2)) ≤
      activityNu r N ^ 3 / (3 * N * (1 - rm ^ 2)) :=
    div_le_div_of_nonneg_left (pow_nonneg hnu 3) (by positivity)
      (mul_le_mul_of_nonneg_left (by linarith : 1 - rm ^ 2 ≤ 1 - r ^ 2) (by positivity))
  have hnum : monotoneEpsilonBound r N ≤ 2 * activityNu r N / (N + 1) +
      activityNu r N ^ 3 / (3 * N * (1 - rm ^ 2)) := by
    unfold monotoneEpsilonBound
    rw [activityNu_gap hn]
    simpa only [mul_assoc] using
      add_le_add (le_refl (2 * activityNu r N / (N + 1))) hreplace
  have hdiv := div_le_div_of_nonneg_right hnum hs.le
  have heq : (2 * activityNu r N / (N + 1) + activityNu r N ^ 3 / (3 * N * (1 - rm ^ 2))) /
      Real.sqrt (1 + V22.cCoef N * activityNu r N ^ 2) = spikeEpsilonCap N rm (activityNu r N) := by
    unfold spikeEpsilonCap
    ring
  rw [heq] at hdiv
  exact h.trans hdiv

/-- The original bounded-block `rhoStarBlock`, proved at the actual point
and the lower endpoint `N1`, rather than asserted as an analytic premise. -/
theorem spike_rhoU_block_lower {r rm N1 N nm : ℝ} (hN1 : 10 ≤ N1) (hNN : N1 ≤ N)
    (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hrmh : rm ≤ 1 / 2) (hcap : activityNu r N ≤ nm) :
    V22.rhoStarBlock N1 nm rm ≤ V22.rhoU r N := by
  have hN := hN1.trans hNN
  have hrm0 := hr0.trans hrrm
  have hd := coefficient_one_sub_rm_sq_pos hrm0 hrmh
  have hnu := activityNu_nonneg (N := N) hr0
  have hsq := (sq_le_sq₀ hr0 hrm0).2 hrrm
  have hmain : (1 - rm ^ 2) * V22.rho N1 ≤ (1 - r ^ 2) * V22.rho N :=
    mul_le_mul (by linarith) (coefficient_rho_monotone hN1 hNN)
      (by unfold V22.rho; positivity) (by linarith)
  have heps := (spike_epsilon_ratio_cap hN hr0 hrrm hrmh).trans
    ((spikeEpsilonCap_mono hN hrm0 hrmh hnu hcap).trans
      (spikeEpsilonCap_antitone_N hN1 hNN hrm0 hrmh (hnu.trans hcap)))
  have heq : spikeEpsilonCap N1 rm nm =
      (2 * nm / (N1 + 1) + nm ^ 3 / (3 * N1 * (1 - rm ^ 2))) /
        Real.sqrt (1 + V22.cCoef N1 * nm ^ 2) := by unfold spikeEpsilonCap; ring
  rw [heq] at heps
  unfold V22.rhoStarBlock V22.rhoU
  linarith

theorem spike_kappaABlock_nonneg {N1 rm nm : ℝ} (hN1 : 10 ≤ N1)
    (hr0 : 0 ≤ rm) (hrh : rm ≤ 1 / 2) (hnm : 0 ≤ nm) : 0 ≤ V22.kappaABlock N1 nm rm := by
  have hd := coefficient_one_sub_rm_sq_pos hr0 hrh
  unfold V22.kappaABlock
  positivity

theorem spike_rho_error_block_upper {r rm N1 N nm : ℝ} (hN1 : 10 ≤ N1) (hNN : N1 ≤ N)
    (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hrmh : rm ≤ 1 / 2) (hcap : activityNu r N ≤ nm) :
    2 * (N + 1) * (V22.rho N - V22.rhoU r N) ≤
      4 * activityNu r N + V22.kappaABlock N1 nm rm * activityNu r N ^ 2 := by
  let nu := activityNu r N
  let fc := fun n x : ℝ => x / Real.sqrt (1 + V22.cCoef n * x ^ 2)
  have hN := hN1.trans hNN
  have hn1 : 0 < N1 := by linarith
  have hn : 0 < N := by linarith
  have hrm0 := hr0.trans hrrm
  have hd := coefficient_one_sub_rm_sq_pos hrm0 hrmh
  have hnu : 0 ≤ nu := activityNu_nonneg hr0
  have hnm := hnu.trans hcap
  have hc : 0 ≤ V22.cCoef N1 := by linarith [linearized_cCoef_lower hN1]
  have hcN : 0 ≤ V22.cCoef N := by linarith [linearized_cCoef_lower hN]
  have hf : fc N nu ≤ fc N1 nm :=
    (spike_fraction_c_antitone hc (coefficient_cCoef_monotone hN1 hNN) hnu).trans
      (spike_fraction_mono hc hnu hcap)
  have hfself : fc N nu ≤ nu := linearized_nu_sqrt_fraction_self hcN hnu
  have hratio : (N + 1) / N ≤ (N1 + 1) / N1 := by
    have h := one_div_le_one_div_of_le hn1 hNN
    have heq : (N + 1) / N = 1 + 1 / N := by field_simp [hn.ne'] <;> ring
    have heq1 : (N1 + 1) / N1 = 1 + 1 / N1 := by field_simp [hn1.ne'] <;> ring
    rw [heq, heq1]
    linarith
  have hcoeff : 2 * (N + 1) / (3 * N * (1 - rm ^ 2)) ≤
      2 * (N1 + 1) / (3 * N1 * (1 - rm ^ 2)) := by
    have h := mul_le_mul_of_nonneg_right hratio (show 0 ≤ 2 / (3 * (1 - rm ^ 2)) by positivity)
    convert h using 1 <;> field_simp [hn.ne', hn1.ne', hd.ne'] <;> ring
  have hprod := mul_le_mul hcoeff hf (by dsimp [fc]; positivity) (by positivity)
  have hprodScaled := mul_le_mul_of_nonneg_right hprod (sq_nonneg nu)
  have hfirst := mul_le_mul_of_nonneg_left hfself (by norm_num : (0 : ℝ) ≤ 4)
  have heps := mul_le_mul_of_nonneg_left (spike_epsilon_ratio_cap hN hr0 hrrm hrmh)
    (by linarith : 0 ≤ 2 * (N + 1))
  have hsplit : 2 * (N + 1) * spikeEpsilonCap N rm nu =
      4 * fc N nu + (2 * (N + 1) / (3 * N * (1 - rm ^ 2)) * fc N nu) * nu ^ 2 := by
    unfold spikeEpsilonCap fc
    field_simp [(show N + 1 ≠ 0 by linarith)] <;> ring
  rw [hsplit] at heps
  have hscaled : 2 * (N + 1) * (V22.rho N - V22.rhoU r N) =
      2 * nu ^ 2 + 2 * (N + 1) * (V22.epsilonPrime r N / Real.sqrt (V22.gamma r N)) := by
    dsimp [nu]
    rw [activityNu_sq hn.le]
    unfold V22.rhoU V22.rho
    field_simp [(show N + 1 ≠ 0 by linarith)] <;> ring
  rw [hscaled]
  have hprodScaled' : 2 * (N + 1) / (3 * N * (1 - rm ^ 2)) * fc N nu * nu ^ 2 ≤
      (V22.kappaABlock N1 nm rm - 2) * nu ^ 2 := by
    calc
      _ ≤ 2 * (N1 + 1) / (3 * N1 * (1 - rm ^ 2)) * fc N1 nm * nu ^ 2 := hprodScaled
      _ = _ := by unfold V22.kappaABlock fc; ring
  change 2 * nu ^ 2 + 2 * (N + 1) *
      (V22.epsilonPrime r N / Real.sqrt (V22.gamma r N)) ≤
    4 * nu + V22.kappaABlock N1 nm rm * nu ^ 2
  nlinarith only [heps, hfirst, hprodScaled']

theorem spike_reciprocal_block_loss {r rm N1 N nm : ℝ} (hN1 : 10 ≤ N1) (hNN : N1 ≤ N)
    (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hrmh : rm ≤ 1 / 2) (hcap : activityNu r N ≤ nm)
    (hrs : 0 < V22.rhoStarBlock N1 nm rm) :
    2 * N * (1 / V22.rhoU r N - 1 / V22.rho N) ≤
      (4 * activityNu r N + V22.kappaABlock N1 nm rm * activityNu r N ^ 2) / V22.rhoStarBlock N1 nm rm := by
  have hN := hN1.trans hNN
  have hu := bonusRange_rhoU_pos hN hr0 (hrrm.trans hrmh)
  have hn : 0 < N := by linarith
  have hrho : 0 < V22.rho N := by unfold V22.rho; positivity
  have hrsU := spike_rhoU_block_lower hN1 hNN hr0 hrrm hrmh hcap
  have heq : 2 * N * (1 / V22.rhoU r N - 1 / V22.rho N) =
      (2 * (N + 1) * (V22.rho N - V22.rhoU r N)) / V22.rhoU r N := by
    unfold V22.rho
    field_simp [hn.ne', hu.ne', (show N + 1 ≠ 0 by linarith)]
  rw [heq]
  have hnu := activityNu_nonneg (N := N) hr0
  have hnm := hnu.trans hcap
  have hK := spike_kappaABlock_nonneg hN1 (hr0.trans hrrm) hrmh hnm
  exact (div_le_div_of_nonneg_right (spike_rho_error_block_upper hN1 hNN hr0 hrrm hrmh hcap) hu.le).trans
    (div_le_div_of_nonneg_left (by positivity) hrs hrsU)

theorem spike_block_G_upper {M : ℕ} {mu M1 M2 : ℝ}
    (hM : 8 ≤ M) (hmu : 0 < mu) (hM1 : 8 ≤ M1) (hlo : M1 ≤ (M : ℝ)) (hhi : (M : ℝ) ≤ M2) :
    rootG (activityOneLambda M mu .U) ≤ V22.phiBlockGhat ((M : ℝ) / mu) M1 M2 := by
  have hshift := activityOneLambda_shift (by omega : 1 ≤ M) hmu .U
  have hK := (activityOneK_bounds hM ActivityOneSide.U).1
  have hlow0 := div_le_div_of_nonneg_right hK (by positivity : 0 ≤ (M : ℝ) + 3)
  have hlow1 : (71 / 20 : ℝ) / (M2 + 3) ≤ (71 / 20 : ℝ) / ((M : ℝ) + 3) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have hlow : V22.lambdaT ((M : ℝ) / mu) + (71 / 20 : ℝ) / (M2 + 3) ≤ activityOneLambda M mu .U := by
    change activityOneLambda_t ((M : ℝ) / mu) + _ ≤ _
    linarith
  have hhigh := closed_template_shift_upper hM hmu hM1 hlo .U
  have h := rootG_convex.le_max_of_mem_Icc (mem_univ _) (mem_univ _) ⟨hlow, hhigh⟩
  simpa only [V22.phiBlockGhat, shared_G_eq] using h

theorem spike_phiBlock_cap {M : ℕ} {r rm M2 : ℝ} (hr0 : 0 ≤ r) (hrrm : r ≤ rm)
    (hhi : (M : ℝ) ≤ M2) (hnu6 : activityNu r ((M : ℝ) + 2) ≤ 6) :
    activityNu r ((M : ℝ) + 2) ≤ V22.phiBlockNuMax M2 rm := by
  have hrm0 := hr0.trans hrrm
  unfold V22.phiBlockNuMax activityNu
  exact le_min hnu6 ((mul_le_mul_of_nonneg_right hrrm (Real.sqrt_nonneg _)).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith : (M : ℝ) + 2 ≤ M2 + 2)) hrm0))

/-- The source quadratic shift, retaining the lower endpoint `N1` and
the bounded coefficients. Positivity of `q2` is used only in this branch. -/
theorem spike_block_lambda_lower {M : ℕ} {r rm mu M1 M2 : ℝ}
    (hM : 8 ≤ M) (hmu : 0 < mu) (hM1 : 8 ≤ M1) (hlo : M1 ≤ (M : ℝ)) (hhi : (M : ℝ) ≤ M2)
    (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hrmh : rm ≤ 1 / 2)
    (hcap : activityNu r ((M : ℝ) + 2) ≤ V22.phiBlockNuMax M2 rm)
    (hrs : V22.phiBlockCoefficientsValid M1 M2 rm) (hq2 : 0 < V22.phiBlockQ2 M1 M2 rm) :
    V22.lambdaT ((M : ℝ) / mu) + (71 / 20 : ℝ) / (M2 + 3) -
      1 / ((M1 + 2) ^ 2 * V22.phiBlockQ2 M1 M2 rm) ≤ threeRangeLambdaU r mu M := by
  let N : ℝ := (M : ℝ) + 2
  let N1 : ℝ := M1 + 2
  let nm := V22.phiBlockNuMax M2 rm
  let rs := V22.rhoStarBlock N1 nm rm
  let E0 := V22.E2 N1 rm nm
  let q2 := V22.phiBlockQ2 M1 M2 rm
  let qN := rs * (N - 1) / (2 * N) - E0 / N
  let K := N1 ^ 2 * q2
  let nu := activityNu r N
  have hN1 : 10 ≤ N1 := by dsimp [N1]; linarith
  have hNN : N1 ≤ N := by dsimp [N1, N]; linarith
  have hN := hN1.trans hNN
  have hNNat : 10 ≤ M + 2 := by omega
  have hn1 : 0 < N1 := by linarith
  have hn : 0 < N := by linarith
  have hrs0 : 0 < rs := hrs
  have hK : 0 < K := mul_pos (sq_pos_of_pos hn1) hq2
  have hnu : 0 ≤ nu := activityNu_nonneg hr0
  have hrm0 := hr0.trans hrrm
  have hE0 : 0 ≤ E0 := by
    have hd := coefficient_one_sub_rm_sq_pos hrm0 hrmh
    have hnm := hnu.trans hcap
    dsimp [E0]
    unfold V22.E2 V22.e2 V22.e3 V22.e4 V22.e5
    positivity
  have hqident : N1 * q2 = rs * (N1 - 1) / 2 - E0 := by
    dsimp [q2, rs, E0, N1, nm]
    unfold V22.phiBlockQ2 V22.cCoef
    field_simp [(show M1 + 2 ≠ 0 by linarith)] <;> ring
  have hcoefpos : 0 ≤ rs * (N + N1 - 1) / 2 - E0 := by
    have hpositive : 0 < N1 * q2 := mul_pos hn1 hq2
    have hgrow := mul_nonneg hrs0.le (show 0 ≤ N by linarith)
    nlinarith only [hpositive, hgrow, hqident]
  have hgrow := mul_nonneg (sub_nonneg.mpr hNN) hcoefpos
  have hcoef : K ≤ N ^ 2 * qN := by
    have hid : N ^ 2 * qN - K =
        (N - N1) * (rs * (N + N1 - 1) / 2 - E0) := by
      dsimp [qN, K]
      rw [show N1 ^ 2 * q2 = N1 * (N1 * q2) by ring, hqident]
      field_simp [hn.ne'] <;> ring
    rw [← hid] at hgrow
    linarith
  have hquadCoeff : K / N ^ 2 ≤ qN :=
    (div_le_iff₀ (sq_pos_of_pos hn)).2 (by simpa only [mul_comm] using hcoef)
  have hquadScale := mul_le_mul_of_nonneg_right hquadCoeff (sq_nonneg nu)
  have hcomplete : K / N ^ 2 * nu ^ 2 - 2 * nu / N + 1 / K = (K * nu - N) ^ 2 / (K * N ^ 2) := by
    field_simp [hn.ne', hK.ne'] <;> ring
  have hquad : -(1 / K) ≤ qN * nu ^ 2 - 2 * nu / N := by
    have hsq : 0 ≤ K / N ^ 2 * nu ^ 2 - 2 * nu / N + 1 / K := by
      rw [hcomplete]
      positivity
    linarith only [hquadScale, hsq]
  have hu := spike_rhoU_block_lower hN1 hNN hr0 hrrm hrmh hcap
  have hdel := scaled_delta_lower hN (by nlinarith [(coefficient_rm_sq_bounds hr0 (hrrm.trans hrmh)).2.1] : r ^ 2 < 1)
  have hdlo : (N - 1) / N * nu ^ 2 ≤ V22.Delta r N := by
    have hdiv : (N - 1) * nu ^ 2 / N ≤ V22.Delta r N := by
      apply (div_le_iff₀ hn).2
      simpa only [mul_comm] using hdel
    convert hdiv using 1 <;> ring
  have hdel0 : 0 ≤ (N - 1) / N * nu ^ 2 :=
    mul_nonneg (div_nonneg (by linarith : 0 ≤ N - 1) hn.le) (sq_nonneg nu)
  have hprod := mul_le_mul hu hdlo hdel0 (hrs0.trans_le hu).le
  have hE : N * V22.eU r N ≤ 2 * nu + V22.E2 N rm nm * nu ^ 2 :=
    (linearized_eU_upper hN hr0 hrrm hrmh).trans
    (closed_E_capped hN hrm0 hrmh hnu hcap)
  have heCoef := lambdaBonus_E2_antitone hN1 hNN (rm := rm) (nm := nm)
  have heScale : V22.E2 N rm nm * nu ^ 2 ≤ E0 * nu ^ 2 :=
    mul_le_mul_of_nonneg_right heCoef (sq_nonneg nu)
  have he : V22.eU r N ≤ (2 * nu + E0 * nu ^ 2) / N := by
    apply (le_div_iff₀ hn).2
    linarith only [hE, heScale]
  have htshift := activityOneLambda_shift (by omega : 1 ≤ M) hmu .U
  have hk := (activityOneK_bounds hM ActivityOneSide.U).1
  have hkfrac := div_le_div_of_nonneg_right hk (by positivity : 0 ≤ (M : ℝ) + 3)
  have hkcap : (71 / 20 : ℝ) / (M2 + 3) ≤ (71 / 20 : ℝ) / ((M : ℝ) + 3) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have htbase : V22.lambdaT ((M : ℝ) / mu) + (71 / 20 : ℝ) / (M2 + 3) ≤ activityOneLambda M mu .U := by
    change activityOneLambda_t ((M : ℝ) / mu) + _ ≤ _
    linarith only [htshift, hkfrac, hkcap]
  have hlu := threeRanges_lambdaU_eq hNNat hr0 (hrrm.trans hrmh) hmu
  change threeRangeLambdaU r mu M = activityOneLambda M mu .U + V22.rhoU r N / 2 * V22.Delta r N - V22.eU r N at hlu
  have hpay : V22.lambdaT ((M : ℝ) / mu) + (71 / 20 : ℝ) / (M2 + 3) + qN * nu ^ 2 - 2 * nu / N ≤ threeRangeLambdaU r mu M := by
    have hprodHalf : rs / 2 * ((N - 1) / N * nu ^ 2) ≤
        V22.rhoU r N / 2 * V22.Delta r N := by
      convert mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 1 / 2) using 1 <;> ring
    have hquadExact : qN * nu ^ 2 - 2 * nu / N =
        rs / 2 * ((N - 1) / N * nu ^ 2) - (2 * nu + E0 * nu ^ 2) / N := by
      dsimp [qN]
      field_simp [hn.ne'] <;> ring
    linarith only [hprodHalf, he, htbase, hlu, hquadExact]
  change V22.lambdaT ((M : ℝ) / mu) + (71 / 20 : ℝ) / (M2 + 3) - 1 / K ≤ _
  linarith only [hpay, hquad]

theorem spike_block_slope_upper {M : ℕ} {r rm mu M1 M2 : ℝ}
    (hM : 8 ≤ M) (hmu : 0 < mu) (hM1 : 8 ≤ M1) (hlo : M1 ≤ (M : ℝ)) (hhi : (M : ℝ) ≤ M2)
    (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hrmh : rm ≤ 1 / 2)
    (hcap : activityNu r ((M : ℝ) + 2) ≤ V22.phiBlockNuMax M2 rm)
    (hrs : V22.phiBlockCoefficientsValid M1 M2 rm)
    (hUL : V22.lambdaT ((M : ℝ) / mu) ≤ threeRangeLambdaU r mu M)
    (hNeg : threeRangeLambdaU r mu M < 0) :
    |rootGPrime (threeRangeLambdaU r mu M)| ≤ V22.phiBlockG1Bound ((M : ℝ) / mu) M1 M2 rm := by
  have hsneg := bonusRange_upper_sigma_negative hNeg
  rw [abs_of_neg hsneg]
  unfold V22.phiBlockG1Bound
  dsimp only
  split_ifs with hq
  · have hl := spike_block_lambda_lower hM hmu hM1 hlo hhi hr0 hrrm hrmh hcap hrs hq
    have hmono := rootGPrime_strictMono.monotone hl
    rw [shared_G1_eq]
    exact (neg_le_neg hmono).trans (le_max_left _ _)
  · have hmono := rootGPrime_strictMono.monotone hUL
    rw [shared_G1_eq]
    exact (neg_le_neg hmono).trans (le_max_left _ _)

/-- Finite-block Lemma 5.4: both upper loss brackets use the same original
bounded block coefficients, with separate quadratic suprema. -/
theorem source_spike_block_upper_remainder {M : ℕ} {r rm mu M1 M2 : ℝ}
    (hM : 8 ≤ M) (hmu : 0 < mu) (hM1 : 8 ≤ M1) (hlo : M1 ≤ (M : ℝ)) (hhi : (M : ℝ) ≤ M2)
    (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hrmh : rm ≤ 1 / 2)
    (hrs : V22.phiBlockCoefficientsValid M1 M2 rm)
    (hUL : V22.lambdaT ((M : ℝ) / mu) ≤ threeRangeLambdaU r mu M)
    (hNeg : threeRangeLambdaU r mu M < 0) (hnu6 : activityNu r ((M : ℝ) + 2) ≤ 6) :
    bonusRangeDUPrime r mu M ≤ V22.phiBlockRemainder ((M : ℝ) / mu) M1 M2 rm := by
  let N : ℝ := (M : ℝ) + 2
  let N1 : ℝ := M1 + 2
  let nm := V22.phiBlockNuMax M2 rm
  let nu := activityNu r N
  let rs := V22.rhoStarBlock N1 nm rm
  let ka := V22.kappaABlock N1 nm rm
  let Gh := V22.phiBlockGhat ((M : ℝ) / mu) M1 M2
  let g1 := V22.phiBlockG1Bound ((M : ℝ) / mu) M1 M2 rm
  let b1 := N1 - 1 - ka * Gh / rs
  let b2 := N1 - 1 - 2 / rs * V22.E2 N1 rm nm
  have hN1 : 10 ≤ N1 := by dsimp [N1]; linarith
  have hNN : N1 ≤ N := by dsimp [N1, N]; linarith
  have hN := hN1.trans hNN
  have hn : 0 < N := by linarith
  have hrs0 : 0 < rs := hrs
  have hrm0 := hr0.trans hrrm
  have hcap : nu ≤ nm := spike_phiBlock_cap hr0 hrrm hhi hnu6
  have hnu : 0 ≤ nu := activityNu_nonneg hr0
  have hnm := hnu.trans hcap
  have hU := bonusRange_rhoU_pos hN hr0 (hrrm.trans hrmh)
  have hUrs := spike_rhoU_block_lower hN1 hNN hr0 hrrm hrmh hcap
  have hGh : 0 ≤ Gh := by
    dsimp [Gh, V22.phiBlockGhat]
    rw [shared_G_eq, shared_G_eq]
    exact (rootG_nonneg _).trans (le_max_left _ _)
  have hK : 0 ≤ ka := spike_kappaABlock_nonneg hN1 hrm0 hrmh hnm
  have hRecip := spike_reciprocal_block_loss hN1 hNN hr0 hrrm hrmh hcap hrs0
  have hG := spike_block_G_upper hM hmu hM1 hlo hhi
  have hG0 := rootG_nonneg (activityOneLambda M mu .U)
  have hBonus0 := scaled_delta_lower hN (by nlinarith [(coefficient_rm_sq_bounds hr0 (hrrm.trans hrmh)).2.1] : r ^ 2 < 1)
  have hBonus : (N1 - 1) * nu ^ 2 ≤ N * V22.Delta r N := by
    have hscale := mul_le_mul_of_nonneg_right (show N1 - 1 ≤ N - 1 by linarith) (sq_nonneg nu)
    exact hscale.trans hBonus0
  have hCoef : 0 ≤ (4 * nu + ka * nu ^ 2) / rs := by positivity
  have hLoss1 : 2 * N * (1 / V22.rhoU r N - 1 / V22.rho N) * rootG (activityOneLambda M mu .U) -
      N * V22.Delta r N ≤ (4 * Gh / rs) * nu - b1 * nu ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hRecip hG0
    have h2 := mul_le_mul_of_nonneg_left hG hCoef
    have hid : (4 * nu + ka * nu ^ 2) / rs * Gh - (N1 - 1) * nu ^ 2 =
        (4 * Gh / rs) * nu - b1 * nu ^ 2 := by dsimp [b1]; ring
    rw [← hid]
    linarith
  have hE : 0 ≤ V22.E N rm nu := by
    have hd := coefficient_one_sub_rm_sq_pos hrm0 hrmh
    unfold V22.E V22.e2 V22.e3 V22.e4 V22.e5
    positivity
  have hEU := linearized_eU_upper hN hr0 hrrm hrmh
  have hEc := closed_E_capped hN hrm0 hrmh hnu hcap
  have hEcN := mul_le_mul_of_nonneg_right (lambdaBonus_E2_antitone hN1 hNN (rm := rm) (nm := nm)) (sq_nonneg nu)
  have hEcap : V22.E N rm nu ≤ 2 * nu + V22.E2 N1 rm nm * nu ^ 2 := by linarith
  have hLoss2 : 2 * N / V22.rhoU r N * V22.eU r N - N * V22.Delta r N ≤
      (4 / rs) * nu - b2 * nu ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hEU (show 0 ≤ 2 / V22.rhoU r N by positivity)
    have h2 := div_le_div_of_nonneg_left (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hE) hrs0 hUrs
    have h3 := mul_le_mul_of_nonneg_left hEcap (show 0 ≤ 2 / rs by positivity)
    have hid : 2 / rs * (2 * nu + V22.E2 N1 rm nm * nu ^ 2) - (N1 - 1) * nu ^ 2 =
        (4 / rs) * nu - b2 * nu ^ 2 := by dsimp [b2]; ring
    rw [← hid]
    simp only [div_eq_mul_inv] at h1 h2 h3 ⊢
    nlinarith
  have hslope := spike_block_slope_upper hM hmu hM1 hlo hhi hr0 hrrm hrmh hcap hrs hUL hNeg
  have hQ1 := quadraticBound_nonneg (show 0 ≤ 4 * Gh / rs by positivity) hnm (b := b1)
  have hQ2 := quadraticBound_nonneg (show 0 ≤ 4 / rs by positivity) hnm (b := b2)
  have hBound := upperRemainder_bounded_quadratics (abs_nonneg (rootGPrime (threeRangeLambdaU r mu M)))
    (show 0 ≤ 4 * Gh / rs by positivity) (show 0 ≤ 4 / rs by positivity) hnu hcap hLoss1 hLoss2
  have hslopeQ := mul_le_mul_of_nonneg_right hslope hQ2
  unfold bonusRangeDUPrime V22.phiBlockRemainder V22.dUbarBlock V22.positivePart
  change _ ≤ max (quadraticBound (4 * Gh / rs) b1 nm) 0 + g1 * max (quadraticBound (4 / rs) b2 nm) 0
  rw [max_eq_left hQ1, max_eq_left hQ2]
  linarith

/-- Full native deficit bound of source Lemma 5.4 on a finite block. Only
the source zero-deficit lower-range hypothesis and native `lambdaU>=lambdaT`
assumption accompany the explicitly printed coefficient validity guard. -/
theorem source_spike_finite_block {M : ℕ} {r rm mu M1 M2 : ℝ}
    (hM : 8 ≤ M) (hmu : 0 < mu) (hM1 : 8 ≤ M1) (hlo : M1 ≤ (M : ℝ)) (hhi : (M : ℝ) ≤ M2)
    (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hrmh : rm ≤ 1 / 2)
    (ht0 : (387 / 2500 : ℝ) ≤ (M : ℝ) / mu) (ht1 : (M : ℝ) / mu ≤ 69 / 100)
    (hrs : V22.phiBlockCoefficientsValid M1 M2 rm)
    (hUL : V22.lambdaT ((M : ℝ) / mu) ≤ threeRangeLambdaU r mu M)
    (hL : (2 * ((M : ℝ) / mu) / (M : ℝ)) * ((M : ℝ) + 3) * V22.eL r ((M : ℝ) + 2) ≤
      (9 / 2 : ℝ) * ((M : ℝ) / mu - 1) ^ 2) :
    V22.deficitG ((1 + r) / 2) mu 0 0 M ≤ V22.phiBlock ((M : ℝ) / mu) M M1 M2 rm := by
  apply spike_ray_deficit_of_upper_remainder hM hr0 hrrm hrmh hmu ht0 ht1 hL
  intro hNeg hNu
  exact source_spike_block_upper_remainder hM hmu hM1 hlo hhi hr0 hrrm hrmh hrs hUL hNeg hNu.le

theorem source_spike_finite_block_antitone {t M0 M M1 M2 rm : ℝ}
    (ht : 0 ≤ t) (hM0 : 0 < M0) (hM : M0 ≤ M) :
    V22.phiBlock t M M1 M2 rm ≤ V22.phiBlock t M0 M1 M2 rm := by
  unfold V22.phiBlock
  rw [shared_phiWithRemainder_eq, shared_phiWithRemainder_eq]
  exact activityOnePhiWithRemainder_antitone ht hM0 hM le_rfl

/-- The final infinite block uses the original unbounded AM-GM remainder
at its lower endpoint. The required betaE monotonicity is exactly the
source's separate condition for this block. -/
theorem source_spike_infinite_upper_remainder {M : ℕ} {r rm mu M1 : ℝ}
    (hM : 8 ≤ M) (hmu : 0 < mu) (hM1 : 8 ≤ M1) (hlo : M1 ≤ (M : ℝ))
    (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hrmh : rm ≤ 1 / 2)
    (hvalid : V22.phiInfiniteBlockCoefficientsValid ((M : ℝ) / mu) M1 rm)
    (hBeta : ∀ N : ℝ, M1 + 2 ≤ N →
      V22.betaE (M1 + 2) rm (cappedNu rm (M1 + 2)) ≤ V22.betaE N rm (cappedNu rm N))
    (hUL : V22.lambdaT ((M : ℝ) / mu) ≤ threeRangeLambdaU r mu M)
    (hNeg : threeRangeLambdaU r mu M < 0) (hnu6 : activityNu r ((M : ℝ) + 2) ≤ 6) :
    bonusRangeDUPrime r mu M ≤ V22.phiInfiniteBlockRemainder ((M : ℝ) / mu) M1 rm := by
  let t := (M : ℝ) / mu
  let N1 : ℝ := M1 + 2
  let N : ℝ := (M : ℝ) + 2
  have hN1 : 10 ≤ N1 := by dsimp [N1]; linarith
  have hNN : N1 ≤ N := by dsimp [N1, N]; linarith
  have hN := hN1.trans hNN
  have hrm0 := hr0.trans hrrm
  change 0 < V22.rhoStar N1 rm ∧
    0 < N1 - 1 - V22.kappaA N1 rm * V22.Ghat t M1 / V22.rhoStar N1 rm ∧
    0 < V22.betaE N1 rm (cappedNu rm N1) at hvalid
  obtain ⟨hrs1, hb1, hBeta1⟩ := hvalid
  have hBetaNM := hBeta N hNN
  have hBetaN := hBeta1.trans_le hBetaNM
  have hrsN := coefficient_rhoStar_pos hN hrm0 hrmh
  have hrs := coefficient_rhoStar_monotone hN1 hNN hrm0 hrmh
  have hGh : 0 ≤ V22.Ghat t M1 := by
    unfold V22.Ghat
    rw [shared_G_eq, shared_G_eq]
    exact (rootG_nonneg _).trans (le_max_left _ _)
  have hKap := coefficient_kappaA_antitone hN1 hNN hrm0 hrmh
  have hKap0 := (coefficient_remaining_nonneg hN1 hrm0 hrmh).1
  have hRatio : V22.kappaA N rm * V22.Ghat t M1 / V22.rhoStar N rm ≤
      V22.kappaA N1 rm * V22.Ghat t M1 / V22.rhoStar N1 rm :=
    div_le_div₀ (mul_nonneg hKap0 hGh) (mul_le_mul_of_nonneg_right hKap hGh) hrs1 hrs
  have hbN : 0 < N - 1 - V22.kappaA N rm * V22.Ghat t M1 / V22.rhoStar N rm := by linarith
  have hcap : activityNu r N ≤ cappedNu rm N := by
    unfold cappedNu activityNu
    exact le_min hnu6 (mul_le_mul_of_nonneg_right hrrm (Real.sqrt_nonneg _))
  have hpoint := source_closed_upper_remainder hM hmu hr0 hrrm hrmh hM1 hlo hcap hUL hNeg hBetaN hbN
  have hmono := cappedNu_dUbar_antitone hN1 hNN hrm0 hrmh hBetaNM hBeta1 hb1
  exact hpoint.trans hmono

theorem source_spike_infinite_block {M : ℕ} {r rm mu M1 : ℝ}
    (hM : 8 ≤ M) (hmu : 0 < mu) (hM1 : 8 ≤ M1) (hlo : M1 ≤ (M : ℝ))
    (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hrmh : rm ≤ 1 / 2)
    (ht0 : (387 / 2500 : ℝ) ≤ (M : ℝ) / mu) (ht1 : (M : ℝ) / mu ≤ 69 / 100)
    (hvalid : V22.phiInfiniteBlockCoefficientsValid ((M : ℝ) / mu) M1 rm)
    (hBeta : ∀ N : ℝ, M1 + 2 ≤ N →
      V22.betaE (M1 + 2) rm (cappedNu rm (M1 + 2)) ≤ V22.betaE N rm (cappedNu rm N))
    (hUL : V22.lambdaT ((M : ℝ) / mu) ≤ threeRangeLambdaU r mu M)
    (hL : (2 * ((M : ℝ) / mu) / (M : ℝ)) * ((M : ℝ) + 3) * V22.eL r ((M : ℝ) + 2) ≤
      (9 / 2 : ℝ) * ((M : ℝ) / mu - 1) ^ 2) :
    V22.deficitG ((1 + r) / 2) mu 0 0 M ≤ V22.phiInfiniteBlock ((M : ℝ) / mu) M M1 rm := by
  apply spike_ray_deficit_of_upper_remainder hM hr0 hrrm hrmh hmu ht0 ht1 hL
  intro hNeg hNu
  exact source_spike_infinite_upper_remainder hM hmu hM1 hlo hr0 hrrm hrmh hvalid hBeta hUL hNeg hNu.le

theorem source_spike_infinite_block_antitone {t M0 M M1 rm : ℝ}
    (ht : 0 ≤ t) (hM0 : 0 < M0) (hM : M0 ≤ M) :
    V22.phiInfiniteBlock t M M1 rm ≤ V22.phiInfiniteBlock t M0 M1 rm := by
  unfold V22.phiInfiniteBlock
  rw [shared_phiWithRemainder_eq, shared_phiWithRemainder_eq]
  exact activityOnePhiWithRemainder_antitone ht hM0 hM le_rfl

/-- Algebraic installation of two bounded quadratic payments. The
coefficients are supplied only to this immediately consumed helper. -/
theorem spike_bounded_payment {loss1 loss2 rs ka Gh g1 E0 N nu nm : ℝ}
    (hrs : 0 < rs) (hka : 0 ≤ ka) (hGh : 0 ≤ Gh) (hg1 : 0 ≤ g1)
    (hnu : 0 ≤ nu) (hcap : nu ≤ nm)
    (h1 : loss1 ≤ (4 * Gh / rs) * nu - (N - 1 - ka * Gh / rs) * nu ^ 2)
    (h2 : loss2 ≤ (4 / rs) * nu - (N - 1 - 2 / rs * E0) * nu ^ 2) :
    max loss1 0 + g1 * max loss2 0 ≤
      max (V22.quadraticSupBound (4 * Gh / rs) (N - 1 - ka * Gh / rs) nm) 0 +
      g1 * max (V22.quadraticSupBound (4 / rs) (N - 1 - 2 / rs * E0) nm) 0 := by
  have h := upperRemainder_bounded_quadratics hg1 (by positivity) (by positivity) hnu hcap h1 h2
  have hQ1 := quadraticBound_nonneg (show 0 ≤ 4 * Gh / rs by positivity) (hnu.trans hcap) (b := N - 1 - ka * Gh / rs)
  have hQ2 := quadraticBound_nonneg (show 0 ≤ 4 / rs by positivity) (hnu.trans hcap) (b := N - 1 - 2 / rs * E0)
  change _ ≤ max (quadraticBound (4 * Gh / rs) (N - 1 - ka * Gh / rs) nm) 0 +
    g1 * max (quadraticBound (4 / rs) (N - 1 - 2 / rs * E0) nm) 0
  rw [max_eq_left hQ1, max_eq_left hQ2]
  exact h

/-- The original pointwise Phi coefficients use the all-displacement
rho/kappa bounds and the bounded quadratic suprema at the actual fiber. -/
theorem source_spike_allNu_upper_remainder {M : ℕ} {r rm mu : ℝ}
    (hM : 8 ≤ M) (hmu : 0 < mu) (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hrmh : rm ≤ 1 / 2)
    (hUL : V22.lambdaT ((M : ℝ) / mu) ≤ threeRangeLambdaU r mu M)
    (hNeg : threeRangeLambdaU r mu M < 0) (hnu6 : activityNu r ((M : ℝ) + 2) ≤ 6) :
    bonusRangeDUPrime r mu M ≤
      let t := (M : ℝ) / mu
      let N := (M : ℝ) + 2
      let nm := cappedNu rm N
      let Gh := V22.Ghat t M
      let rs := V22.rhoStar N rm
      let ka := V22.kappaA N rm
      V22.positivePart (V22.quadraticSupBound (4 * Gh / rs) (N - 1 - ka * Gh / rs) nm) +
        |V22.G1 (V22.lambdaT t)| * V22.positivePart
          (V22.quadraticSupBound (4 / rs) (N - 1 - 2 / rs * V22.E2 N rm nm) nm) := by
  let t := (M : ℝ) / mu
  let N : ℝ := (M : ℝ) + 2
  let nu := activityNu r N
  let nm := cappedNu rm N
  let Gh := V22.Ghat t M
  let rs := V22.rhoStar N rm
  let ka := V22.kappaA N rm
  have hN : 10 ≤ N := by dsimp [N]; exact_mod_cast (show 10 ≤ M + 2 by omega)
  have hn : 0 < N := by linarith
  have hrm0 := hr0.trans hrrm
  have hrs := coefficient_rhoStar_pos hN hrm0 hrmh
  have hu := bonusRange_rhoU_pos hN hr0 (hrrm.trans hrmh)
  have hrsU := linearized_rhoU_lower hN hr0 hrrm hrmh
  have hnu : 0 ≤ nu := activityNu_nonneg hr0
  have hcap : nu ≤ nm := by
    unfold nm cappedNu nu activityNu
    exact le_min hnu6 (mul_le_mul_of_nonneg_right hrrm (Real.sqrt_nonneg _))
  have hka := (coefficient_remaining_nonneg hN hrm0 hrmh).1
  have hGh : 0 ≤ Gh := by
    dsimp [Gh, V22.Ghat]
    rw [shared_G_eq, shared_G_eq]
    exact (rootG_nonneg _).trans (le_max_left _ _)
  have hRecip := linearized_reciprocal_loss hN hr0 hrrm hrmh
  have hG := closed_template_G_upper hM hmu (by exact_mod_cast hM : (8 : ℝ) ≤ M) le_rfl .U
  have hG0 := rootG_nonneg (activityOneLambda M mu .U)
  have hbonus := scaled_delta_lower hN (by nlinarith [(coefficient_rm_sq_bounds hr0 (hrrm.trans hrmh)).2.1] : r ^ 2 < 1)
  have hLoss1 : 2 * N * (1 / V22.rhoU r N - 1 / V22.rho N) * rootG (activityOneLambda M mu .U) -
      N * V22.Delta r N ≤ (4 * Gh / rs) * nu - (N - 1 - ka * Gh / rs) * nu ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hRecip hG0
    have h2 := mul_le_mul_of_nonneg_left hG (show 0 ≤ (4 * nu + ka * nu ^ 2) / rs by positivity)
    have hid : (4 * nu + ka * nu ^ 2) / rs * Gh - (N - 1) * nu ^ 2 =
        (4 * Gh / rs) * nu - (N - 1 - ka * Gh / rs) * nu ^ 2 := by ring
    rw [← hid]
    linarith
  have hE : 0 ≤ V22.E N rm nu := by
    have hd := coefficient_one_sub_rm_sq_pos hrm0 hrmh
    unfold V22.E V22.e2 V22.e3 V22.e4 V22.e5
    positivity
  have hEU := linearized_eU_upper hN hr0 hrrm hrmh
  have hEcap := closed_E_capped hN hrm0 hrmh hnu hcap
  have hLoss2 : 2 * N / V22.rhoU r N * V22.eU r N - N * V22.Delta r N ≤
      (4 / rs) * nu - (N - 1 - 2 / rs * V22.E2 N rm nm) * nu ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hEU (show 0 ≤ 2 / V22.rhoU r N by positivity)
    have h2 := div_le_div_of_nonneg_left (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hE) hrs hrsU
    have h3 := mul_le_mul_of_nonneg_left hEcap (show 0 ≤ 2 / rs by positivity)
    have hid : 2 / rs * (2 * nu + V22.E2 N rm nm * nu ^ 2) - (N - 1) * nu ^ 2 =
        (4 / rs) * nu - (N - 1 - 2 / rs * V22.E2 N rm nm) * nu ^ 2 := by ring
    rw [← hid]
    simp only [div_eq_mul_inv] at h1 h2 h3 ⊢
    nlinarith
  have hbound := spike_bounded_payment hrs hka hGh (abs_nonneg (rootGPrime (threeRangeLambdaU r mu M))) hnu hcap hLoss1 hLoss2
  have hslope : |rootGPrime (threeRangeLambdaU r mu M)| ≤ |V22.G1 (V22.lambdaT t)| := by
    rw [shared_G1_eq]
    exact rootGPrime_abs_antitoneOn_nonpos (hUL.trans hNeg.le) hNeg.le hUL
  have hQ2 : 0 ≤ V22.positivePart (V22.quadraticSupBound (4 / rs) (N - 1 - 2 / rs * V22.E2 N rm nm) nm) :=
    le_max_right _ _
  have hslopeQ := mul_le_mul_of_nonneg_right hslope hQ2
  exact hbound.trans (add_le_add le_rfl hslopeQ)

/-- Original pointwise Phi form of source Lemma 5.4, with the actual
bounded cap. It assumes precisely the source lower-range and log-ratio
conditions; no upper remainder inequality is added to the final statement. -/
theorem source_spike_ray_bound {M : ℕ} {r rm mu : ℝ}
    (hM : 8 ≤ M) (hmu : 0 < mu) (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hrmh : rm ≤ 1 / 2)
    (ht0 : (387 / 2500 : ℝ) ≤ (M : ℝ) / mu) (ht1 : (M : ℝ) / mu ≤ 69 / 100)
    (hUL : V22.lambdaT ((M : ℝ) / mu) ≤ threeRangeLambdaU r mu M)
    (hL : (2 * ((M : ℝ) / mu) / (M : ℝ)) * ((M : ℝ) + 3) * V22.eL r ((M : ℝ) + 2) ≤
      (9 / 2 : ℝ) * ((M : ℝ) / mu - 1) ^ 2) :
    V22.deficitG ((1 + r) / 2) mu 0 0 M ≤ V22.Phi ((M : ℝ) / mu) M rm := by
  unfold V22.Phi V22.phiAllNuSpecialization
  apply spike_ray_deficit_of_upper_remainder hM hr0 hrrm hrmh hmu ht0 ht1 hL
  intro hNeg hNu
  exact source_spike_allNu_upper_remainder hM hmu hr0 hrrm hrmh hUL hNeg hNu.le

/-- The source target line costs at most its nonnegative intercept on
spike fibers. Its slope and the actual all-integer infimum are retained. -/
theorem spike_target_deficit_le {q mu b beta : ℝ} {M : ℕ}
    (hb : 0 ≤ b) (hbeta : 0 ≤ beta) (ht : (M : ℝ) / mu ≤ 1) :
    V22.deficitG q mu b beta M ≤ V22.deficitG q mu 0 0 M + b := by
  have hline : beta * ((M : ℝ) / mu - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hbeta (by linarith)
  unfold V22.deficitG V22.positivePart V22.targetLine
  norm_num only [zero_mul, add_zero]
  have hleft := le_max_left (V22.psi ((M : ℝ) / mu) - V22.fiberInfimum q mu M) (0 : ℝ)
  have hright := le_max_right (V22.psi ((M : ℝ) / mu) - V22.fiberInfimum q mu M) (0 : ℝ)
  apply max_le <;> linarith

end Erdos993Lean.Analytic.V22.Analysis
