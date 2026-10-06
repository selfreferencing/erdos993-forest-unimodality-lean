import Erdos993Lean.Analytic.V22.Analysis.CentralAmplitude
import Erdos993Lean.Analytic.V22.Analysis.GaussianComparison
import Erdos993Lean.Analytic.V22.Analysis.GaussianUpper

/-!
# Paper v2.2, Lemma 4.3(b,c): native integer-binomial exponent forms

Source: frozen lane E `SOURCE_V5_note.tex`, SHA256
`c08dbf5837e1fce232f4871dffbade9fa8197bd01e9d8c77fbd8c921e35e4415`,
lines 530--546. The lower theorem discharges support from w<=1 internally;
the upper theorem keeps every integer, including the exterior zero tails.
Consumer: the exact three-range minorants. Draft, no Lean/lake by agent.
-/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set Erdos993Lean.Analytic.NoValley

/-- The source's right width is at most 1/3 on its original N>=10 range.
This rational bound suffices for the cubic absorption used in Lemma 4.3(b). -/
theorem sharedGaussianZR_le_third {r N : ℝ} (hr0 : 0 ≤ r)
    (hrh : r ≤ 1 / 2) (hN : 10 ≤ N) :
    Erdos993Lean.Analytic.V22.ZR r N 1 ≤ 1 / 3 := by
  have hr1 : r < 1 := by linarith
  have hn0 : 0 < N := by linarith
  have hn1 : 0 < N + 1 := by linarith
  have hs := shared_sN_le_half_sqrt hr0 hr1 hn0
  have hsq := Real.sq_sqrt hn0.le
  have hrootSq : (3 * Real.sqrt N) ^ 2 ≤ (N + 1) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hN) hn0.le]
  have hroot : 3 * Real.sqrt N ≤ N + 1 := le_of_sq_le_sq hrootSq (by linarith)
  unfold Erdos993Lean.Analytic.V22.ZR
  norm_num only [Real.sqrt_one, one_mul]
  apply (div_le_iff₀ hn1).2
  linarith

theorem sharedGaussian_right_denominator_lower {r N : ℝ} (hr0 : 0 ≤ r)
    (hrh : r ≤ 1 / 2) (hN : 10 ≤ N) :
    (11 / 36 : ℝ) ≤ 1 - (r + Erdos993Lean.Analytic.V22.ZR r N 1) ^ 2 := by
  have hz := sharedGaussianZR_le_third hr0 hrh hN
  have hz0 := (shared_gaussian_window_domains hr0 hrh hN).2.2.1.le
  have hp : r + Erdos993Lean.Analytic.V22.ZR r N 1 ≤ 5 / 6 := by linarith
  have hp0 : 0 ≤ r + Erdos993Lean.Analytic.V22.ZR r N 1 := add_nonneg hr0 hz0
  nlinarith [mul_nonneg (sub_nonneg.mpr hp) (show 0 ≤ 5 / 6 +
    (r + Erdos993Lean.Analytic.V22.ZR r N 1) by linarith)]

private theorem shared_quartic_ratio_mono {z Z A D : ℝ} (hA : 0 ≤ A)
    (hD : 0 < D) (hz : |z| ≤ Z) :
    A * z ^ 4 / (12 * D) ≤ A * Z ^ 4 / (12 * D) := by
  have hp := pow_le_pow_left₀ (abs_nonneg z) hz 4
  rw [(by decide : Even 4).pow_abs z] at hp
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hA) (by positivity)

/-- The right cubic term is absorbed by the existing two linear epsilon
copies, using only the source width-one conditions. -/
theorem shared_right_cubic_absorption {r N u : ℝ} (hr0 : 0 ≤ r)
    (hrh : r ≤ 1 / 2) (hN : 10 ≤ N) (hu : r ≤ u)
    (huw : u ^ 2 ≤ Erdos993Lean.Analytic.V22.varianceR r * N) :
    (N + 1) * r * (sharedGaussianZ r N u) ^ 3 /
        (3 * ((1 - (r + Erdos993Lean.Analytic.V22.ZR r N 1) ^ 2) * (1 - r ^ 2))) ≤
      2 * r * u / (Erdos993Lean.Analytic.V22.varianceR r * (N + 1)) := by
  have hr1 : r < 1 := by linarith
  have hn0 : 0 < N := by linarith
  have hn1 : 0 < N + 1 := by linarith
  have hv := shared_varianceR_pos hr0 hr1
  have hu0 : 0 ≤ u := le_trans hr0 hu
  let DR : ℝ := 1 - (r + Erdos993Lean.Analytic.V22.ZR r N 1) ^ 2
  let D : ℝ := DR * (1 - r ^ 2)
  have hDRlo : (11 / 36 : ℝ) ≤ DR := sharedGaussian_right_denominator_lower hr0 hrh hN
  have hDR : 0 < DR := by linarith
  have hvr : 1 - r ^ 2 = 4 * Erdos993Lean.Analytic.V22.varianceR r := by
    unfold Erdos993Lean.Analytic.V22.varianceR
    ring
  have hD : 0 < D := by dsimp [D]; rw [hvr]; positivity
  have hz0 : 0 ≤ sharedGaussianZ r N u := by
    unfold sharedGaussianZ
    exact div_nonneg (by linarith) hn1.le
  have hzu : sharedGaussianZ r N u ≤ 2 * u / (N + 1) := by
    unfold sharedGaussianZ
    exact div_le_div_of_nonneg_right (by linarith) hn1.le
  have hz3 := pow_le_pow_left₀ hz0 hzu 3
  have hcube := mul_le_mul_of_nonneg_left hz3
    (show 0 ≤ (N + 1) * r / (3 * D) by positivity)
  have hcubic : (N + 1) * r * (sharedGaussianZ r N u) ^ 3 / (3 * D) ≤
      8 * r * u ^ 3 / (3 * (N + 1) ^ 2 * D) := by
    convert hcube using 1 <;> field_simp [hn1.ne', hD.ne'] <;> ring
  have hvle : Erdos993Lean.Analytic.V22.varianceR r ≤ (1 / 4 : ℝ) := by
    unfold Erdos993Lean.Analytic.V22.varianceR
    nlinarith [sq_nonneg r]
  have hu2 : u ^ 2 ≤ 3 * (N + 1) * DR := by
    have h := mul_le_mul_of_nonneg_right hvle hn0.le
    have hd := mul_le_mul_of_nonneg_left hDRlo hn1.le
    linarith
  have hmul := mul_le_mul_of_nonneg_left hu2
    (show 0 ≤ 8 * r * u * Erdos993Lean.Analytic.V22.varianceR r * (N + 1) by positivity)
  have hfinal : 8 * r * u ^ 3 / (3 * (N + 1) ^ 2 * D) ≤
      2 * r * u / (Erdos993Lean.Analytic.V22.varianceR r * (N + 1)) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 3 * (N + 1) ^ 2 * D)
      (by positivity : 0 < Erdos993Lean.Analytic.V22.varianceR r * (N + 1))).2
    dsimp [D]
    rw [hvr]
    convert hmul using 1 <;> ring
  exact hcubic.trans hfinal

/-- The curvature-to-exponent bound with the original quartic max and the
actual standardized offset. All analytic window conditions are proved here. -/
theorem sharedKLPsi_window_exponent_upper {r N : ℝ} (hr0 : 0 ≤ r)
    (hrh : r ≤ 1 / 2) (hN : 10 ≤ N) (x : ℝ) (hw : x ^ 2 ≤ 1) :
    (N + 1) * sharedKLPsi r (sharedGaussianZ r N (Erdos993Lean.Analytic.V22.sN r N * x)) ≤
      Erdos993Lean.Analytic.V22.rho N / 2 * x ^ 2 +
        Erdos993Lean.Analytic.V22.epsilon r N * |x| +
        Erdos993Lean.Analytic.V22.c0 r N + Erdos993Lean.Analytic.V22.quarticError r N 1 := by
  have hr1 : r < 1 := by linarith
  have hn0 : 0 < N := by linarith
  have hn1 : 0 < N + 1 := by linarith
  have hv := shared_varianceR_pos hr0 hr1
  have hvr := shared_one_sub_sq_pos (by linarith : -1 < r) hr1
  have hs := shared_sN_sq hr0 hr1 hn0
  have hs0 : 0 ≤ Erdos993Lean.Analytic.V22.sN r N := Real.sqrt_nonneg _
  let u : ℝ := Erdos993Lean.Analytic.V22.sN r N * x
  let z : ℝ := sharedGaussianZ r N u
  have hu2 : u ^ 2 ≤ Erdos993Lean.Analytic.V22.varianceR r * N := by
    have h := mul_le_mul_of_nonneg_left hw (sq_nonneg (Erdos993Lean.Analytic.V22.sN r N))
    dsimp [u]
    simpa only [mul_pow, hs, mul_one] using h
  have huabs : |u| ≤ Erdos993Lean.Analytic.V22.sN r N :=
    abs_le_of_sq_le_sq (by rw [hs]; exact hu2) hs0
  obtain ⟨huL, huR⟩ := abs_le.mp huabs
  obtain ⟨hZL0, hZL1, hZR0, hrZR⟩ := shared_gaussian_window_domains hr0 hrh hN
  have hDL : 0 < (1 - (Erdos993Lean.Analytic.V22.ZL r N 1) ^ 2) * (1 - r ^ 2) :=
    mul_pos (shared_one_sub_sq_pos (by linarith : -1 < Erdos993Lean.Analytic.V22.ZL r N 1) hZL1) hvr
  have hDR : 0 < (1 - (r + Erdos993Lean.Analytic.V22.ZR r N 1) ^ 2) * (1 - r ^ 2) :=
    mul_pos (shared_one_sub_sq_pos (by linarith : -1 < r + Erdos993Lean.Analytic.V22.ZR r N 1) hrZR) hvr
  have hquad := shared_lower_exponent_identity hr0 hr1 hn0 x
  have heps := shared_epsilon_nonneg hr0 hr1 hn0
  by_cases hleft : u ≤ r
  · have hz0 : z ≤ 0 := by dsimp [z, sharedGaussianZ]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hn1.le
    have hzL : -Erdos993Lean.Analytic.V22.ZL r N 1 ≤ z := by
      dsimp [z, sharedGaussianZ]
      unfold Erdos993Lean.Analytic.V22.ZL
      norm_num only [Real.sqrt_one, one_mul]
      rw [← neg_div]
      exact div_le_div_of_nonneg_right (by linarith) hn1.le
    have hgauss := mul_le_mul_of_nonneg_left
      (sharedKLPsi_gaussian_left hr0 hr1 hZL0 hZL1 hzL hz0) hn1.le
    have hquartic : (N + 1) * z ^ 4 /
        (12 * ((1 - (Erdos993Lean.Analytic.V22.ZL r N 1) ^ 2) * (1 - r ^ 2))) ≤
        Erdos993Lean.Analytic.V22.quarticError r N 1 := by
      unfold Erdos993Lean.Analytic.V22.quarticError
      apply le_trans ?_ (le_max_left _ _)
      have h := shared_quartic_ratio_mono (z := z)
        (Z := Erdos993Lean.Analytic.V22.ZL r N 1) hn1.le hDL
        (by rw [abs_of_nonpos hz0]; linarith)
      simpa only [mul_assoc] using h
    have hgauss' : (N + 1) * sharedKLPsi r z ≤
        (N + 1) * z ^ 2 / (2 * (1 - r ^ 2)) +
        (N + 1) * z ^ 4 /
          (12 * ((1 - (Erdos993Lean.Analytic.V22.ZL r N 1) ^ 2) * (1 - r ^ 2))) := by
      convert hgauss using 1 <;> ring
    change (N + 1) * z ^ 2 / (2 * (1 - r ^ 2)) = _ at hquad
    rw [hquad] at hgauss'
    have habs := mul_le_mul_of_nonneg_left (neg_le_abs x) heps
    change (N + 1) * sharedKLPsi r z ≤ _
    linarith
  · have hu : r ≤ u := by linarith
    have hz0 : 0 ≤ z := by dsimp [z, sharedGaussianZ]; exact div_nonneg (by linarith) hn1.le
    have hzR : z ≤ Erdos993Lean.Analytic.V22.ZR r N 1 := by
      dsimp [z, sharedGaussianZ]
      unfold Erdos993Lean.Analytic.V22.ZR
      norm_num only [Real.sqrt_one, one_mul]
      exact div_le_div_of_nonneg_right (by linarith) hn1.le
    have hgauss := mul_le_mul_of_nonneg_left
      (sharedKLPsi_gaussian_right hr0 hr1 hZR0 hrZR hz0 hzR) hn1.le
    have hquartic : (N + 1) * z ^ 4 /
        (12 * ((1 - (r + Erdos993Lean.Analytic.V22.ZR r N 1) ^ 2) * (1 - r ^ 2))) ≤
        Erdos993Lean.Analytic.V22.quarticError r N 1 := by
      unfold Erdos993Lean.Analytic.V22.quarticError
      apply le_trans ?_ (le_max_right _ _)
      have h := shared_quartic_ratio_mono (z := z)
        (Z := Erdos993Lean.Analytic.V22.ZR r N 1) hn1.le hDR
        (by rw [abs_of_nonneg hz0]; exact hzR)
      simpa only [mul_assoc] using h
    have hcubic := shared_right_cubic_absorption hr0 hrh hN hu hu2
    have hlin : 2 * Erdos993Lean.Analytic.V22.epsilon r N * x =
        2 * r * u / (Erdos993Lean.Analytic.V22.varianceR r * (N + 1)) := by
      rw [shared_epsilon_eq hr0 hr1 hn0]
      dsimp [u]
      ring
    rw [← hlin] at hcubic
    have hgauss' : (N + 1) * sharedKLPsi r z ≤
        (N + 1) * z ^ 2 / (2 * (1 - r ^ 2)) +
        (N + 1) * r * z ^ 3 /
          (3 * ((1 - (r + Erdos993Lean.Analytic.V22.ZR r N 1) ^ 2) * (1 - r ^ 2))) +
        (N + 1) * z ^ 4 /
          (12 * ((1 - (r + Erdos993Lean.Analytic.V22.ZR r N 1) ^ 2) * (1 - r ^ 2))) := by
      convert hgauss using 1 <;> field_simp [hDR.ne'] <;> ring
    change (N + 1) * z ^ 2 / (2 * (1 - r ^ 2)) = _ at hquad
    rw [hquad] at hgauss'
    have habs := mul_le_mul_of_nonneg_left (le_abs_self x) heps
    change (N + 1) * sharedKLPsi r z ≤ _
    change (N + 1) * r * z ^ 3 /
      (3 * ((1 - (r + Erdos993Lean.Analytic.V22.ZR r N 1) ^ 2) * (1 - r ^ 2))) ≤
      2 * Erdos993Lean.Analytic.V22.epsilon r N * x at hcubic
    linarith

/-- The exact w<=1 hypothesis forces support, rather than assuming it in the
final lower exponent statement. -/
theorem sharedGaussianX_support {N : ℕ} (hN : 10 ≤ N) {r : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (J : ℤ)
    (hw : (sharedGaussianX r N J) ^ 2 ≤ 1) : 0 ≤ J ∧ J ≤ (N : ℤ) := by
  have hNr : (10 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hr1 : r < 1 := by linarith
  have hn : 0 < (N : ℝ) := by linarith
  have hs : 0 < Erdos993Lean.Analytic.V22.sN r N :=
    Real.sqrt_pos.2 (mul_pos (shared_varianceR_pos hr0 hr1) hn)
  have hX : Erdos993Lean.Analytic.V22.sN r N * sharedGaussianX r N J = sharedGaussianU r N J := by
    unfold sharedGaussianX
    field_simp [hs.ne']
  have hxabs : |sharedGaussianX r N J| ≤ 1 :=
    abs_le_of_sq_le_sq (by simpa only [one_pow] using hw) (by norm_num)
  have huabs : |sharedGaussianU r N J| ≤ Erdos993Lean.Analytic.V22.sN r N := by
    rw [← hX, abs_mul, abs_of_pos hs]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hxabs hs.le
  obtain ⟨huL, huR⟩ := abs_le.mp huabs
  have hsn := shared_sN_le_half_sqrt hr0 hr1 hn
  have hsq := Real.sq_sqrt hn.le
  have hrootSq : (Real.sqrt (N : ℝ)) ^ 2 ≤ (N : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ (N : ℝ) - 1 by linarith) hn.le]
  have hrootN : Real.sqrt (N : ℝ) ≤ (N : ℝ) := le_of_sq_le_sq hrootSq hn.le
  have hroot2 : 2 * Real.sqrt (N : ℝ) ≤ (N : ℝ) + 1 := by
    nlinarith [sq_nonneg (Real.sqrt (N : ℝ) - 1)]
  have hNm1 : 0 ≤ (N : ℝ) - 1 := by linarith
  have hql := mul_le_mul_of_nonneg_right (show (1 / 2 : ℝ) ≤ (1 + r) / 2 by linarith) hNm1
  have hqh := mul_le_mul_of_nonneg_right (show (1 + r) / 2 ≤ (3 / 4 : ℝ) by linarith) hNm1
  unfold sharedGaussianU at huL huR
  have hJ0 : 0 ≤ (J : ℝ) := by linarith
  have hJN : (J : ℝ) ≤ (N : ℝ) := by linarith
  exact ⟨by exact_mod_cast hJ0, by exact_mod_cast hJN⟩

theorem sharedGaussianZ_coordinate (r : ℝ) (N : ℕ) (J : ℤ) :
    interiorTiltCoordinate r N J = sharedGaussianZ r N (sharedGaussianU r N J) := by
  unfold interiorTiltCoordinate interiorSymmetricCoordinate sharedGaussianZ sharedGaussianU
  field_simp [ne_of_gt (by positivity : 0 < (N : ℝ) + 1)]
  ring

/-- Exact native Lemma 4.3(b), all integer J under only the source w<=1
condition. Support and both Gaussian windows are discharged internally. -/
theorem shared_binomial_lower_exponents {N : ℕ} (hN : 10 ≤ N) {r : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (J : ℤ)
    (hw : (sharedGaussianX r N J) ^ 2 ≤ 1) :
    Real.exp (-Erdos993Lean.Analytic.V22.rho N / 2 * (sharedGaussianX r N J) ^ 2 -
        Erdos993Lean.Analytic.V22.epsilon r N * |sharedGaussianX r N J| -
        Erdos993Lean.Analytic.V22.c0 r N - Erdos993Lean.Analytic.V22.quarticError r N 1) ≤
      Real.sqrt (1 - r ^ 2) / Erdos993Lean.Analytic.V22.centralAmplitude N *
        binom N ((1 + r) / 2) J := by
  have hNr : (10 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hr1 : r < 1 := by linarith
  have hn : 0 < (N : ℝ) := by linarith
  have hv := shared_one_sub_sq_pos (by linarith : -1 < r) hr1
  have hs : 0 < Erdos993Lean.Analytic.V22.sN r N :=
    Real.sqrt_pos.2 (mul_pos (shared_varianceR_pos hr0 hr1) hn)
  have hX : Erdos993Lean.Analytic.V22.sN r N * sharedGaussianX r N J = sharedGaussianU r N J := by
    unfold sharedGaussianX
    field_simp [hs.ne']
  have hPsi := sharedKLPsi_window_exponent_upper hr0 hrh hNr (sharedGaussianX r N J) hw
  rw [hX, ← sharedGaussianZ_coordinate] at hPsi
  obtain ⟨hJ0, hJN⟩ := sharedGaussianX_support hN hr0 hrh J hw
  have hloc := binomial_local_lower (by omega : 2 ≤ N) hr0 hr1 J hJ0 hJN
  have hC := interiorCentralPrefactor_pos N
  have hroot := Real.sqrt_pos.2 hv
  have hm := mul_le_mul_of_nonneg_left hloc (div_pos hroot hC).le
  have hcancel : Real.sqrt (1 - r ^ 2) / interiorCentralPrefactor N *
      (interiorCentralPrefactor N / Real.sqrt (1 - r ^ 2) *
        Real.exp (-((N : ℝ) + 1) * sharedKLPsi r (interiorTiltCoordinate r N J))) =
      Real.exp (-((N : ℝ) + 1) * sharedKLPsi r (interiorTiltCoordinate r N J)) := by
    field_simp [hC.ne', hroot.ne'] <;> ring
  rw [hcancel] at hm
  rw [shared_centralAmplitude_eq]
  apply le_trans ?_ hm
  apply Real.exp_le_exp.mpr
  linarith

/-- Exact native Lemma 4.3(c), for every integer J including both exterior
tails. The stronger N>=2 and 0<=r<1 domain contains the source Section 4 range. -/
theorem shared_binomial_upper_exponents {N : ℕ} (hN : 2 ≤ N) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (J : ℤ) :
    Real.sqrt (1 - r ^ 2) / Erdos993Lean.Analytic.V22.centralAmplitude N *
        binom N ((1 + r) / 2) J ≤
      symmetricUpperPrefactor N / Erdos993Lean.Analytic.V22.centralAmplitude N * Real.exp
        (((N : ℝ) + 1) * Erdos993Lean.Analytic.V22.cr r - Erdos993Lean.Analytic.V22.c0Prime r N -
          (1 - r ^ 2) * Erdos993Lean.Analytic.V22.rho N / 2 * (sharedGaussianX r N J) ^ 2 +
          Erdos993Lean.Analytic.V22.epsilonPrime r N * |sharedGaussianX r N J|) := by
  simpa only [shared_centralAmplitude_eq] using binomial_gaussian_upper_normalized hN hr0 hr1 J

end Erdos993Lean.Analytic.V22.Analysis
