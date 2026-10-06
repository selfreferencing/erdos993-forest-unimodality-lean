import Erdos993Lean.Analytic.V22.Analysis.WindowCentral
import Erdos993Lean.Analytic.V22.Analysis.CoefficientMonotonicity

/-! Source: frozen note Lemma 5.10, including exact width-three support and
persistence of (c1), (c2), (c3′). All comparisons retain actual integer atoms.
Parent owns compilation; this drafting subagent does not run Lean or lake. -/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set Erdos993Lean.Analytic.NoValley

private theorem window_quartic_ratio_mono {z Z A D : ℝ} (hA : 0 ≤ A)
    (hD : 0 < D) (hz : |z| ≤ Z) :
    A * z ^ 4 / (12 * D) ≤ A * Z ^ 4 / (12 * D) := by
  have hp := pow_le_pow_left₀ (abs_nonneg z) hz 4
  rw [(by decide : Even 4).pow_abs z] at hp
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hA) (by positivity)

/-- The original (c3) pays for the cubic term throughout width three. -/
theorem window_right_cubic_absorption {r N u : ℝ} (hr0 : 0 ≤ r)
    (hrh : r ≤ 1 / 2) (hN : 10 ≤ N) (hc : V22.windowConditions r N) (hu : r ≤ u)
    (huw : u ^ 2 ≤ 3 * V22.varianceR r * N) :
    (N + 1) * r * (sharedGaussianZ r N u) ^ 3 /
        (3 * ((1 - (r + V22.ZR r N 3) ^ 2) * (1 - r ^ 2))) ≤
      2 * r * u / (V22.varianceR r * (N + 1)) := by
  have hr1 : r < 1 := by linarith
  have hn : 0 < N := by linarith
  have hn1 : 0 < N + 1 := by linarith
  have hv := shared_varianceR_pos hr0 hr1
  have hu0 : 0 ≤ u := hr0.trans hu
  have hsN0 : 0 ≤ V22.sN r N := Real.sqrt_nonneg _
  have hZR0 : 0 ≤ V22.ZR r N 3 := by
    unfold V22.ZR
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hsN0) hn1.le
  let DR : ℝ := 1 - (r + V22.ZR r N 3) ^ 2
  let D : ℝ := DR * (1 - r ^ 2)
  have hDR : 0 < DR := shared_one_sub_sq_pos (by linarith : -1 < r + V22.ZR r N 3) hc.2.1
  have hvr : 1 - r ^ 2 = 4 * V22.varianceR r := by unfold V22.varianceR; ring
  have hD : 0 < D := by dsimp [D]; rw [hvr]; positivity
  have hrho : 0 < V22.rho N := by unfold V22.rho; positivity
  have hC : 3 * ((1 - r ^ 2) * V22.rho N) ≤ 12 * DR :=
    (le_div_iff₀ (mul_pos (shared_one_sub_sq_pos (by linarith) hr1) hrho)).1 hc.2.2
  have hCscaled := mul_le_mul_of_nonneg_right hC hn1.le
  have hcancel : V22.rho N * (N + 1) = N := by unfold V22.rho; field_simp [hn1.ne']
  have hgeom : 3 * V22.varianceR r * N ≤ 3 * (N + 1) * DR := by
    have hscaled : 3 * (1 - r ^ 2) * N ≤ 12 * DR * (N + 1) := by
      convert hCscaled using 1 <;> unfold V22.rho <;> field_simp [hn1.ne'] <;> ring
    rw [hvr] at hscaled
    nlinarith
  have hu2 := huw.trans hgeom
  have hz0 : 0 ≤ sharedGaussianZ r N u := by
    unfold sharedGaussianZ
    exact div_nonneg (by linarith) hn1.le
  have hzu : sharedGaussianZ r N u ≤ 2 * u / (N + 1) := by
    unfold sharedGaussianZ
    exact div_le_div_of_nonneg_right (by linarith) hn1.le
  have hcube := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz0 hzu 3)
    (show 0 ≤ (N + 1) * r / (3 * D) by positivity)
  have hcubic : (N + 1) * r * (sharedGaussianZ r N u) ^ 3 / (3 * D) ≤
      8 * r * u ^ 3 / (3 * (N + 1) ^ 2 * D) := by
    convert hcube using 1 <;> field_simp [hn1.ne', hD.ne'] <;> ring
  have hmul := mul_le_mul_of_nonneg_left hu2
    (show 0 ≤ 8 * r * u * V22.varianceR r * (N + 1) by positivity)
  have hfinal : 8 * r * u ^ 3 / (3 * (N + 1) ^ 2 * D) ≤
      2 * r * u / (V22.varianceR r * (N + 1)) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 3 * (N + 1) ^ 2 * D)
      (by positivity : 0 < V22.varianceR r * (N + 1))).2
    dsimp [D]
    rw [hvr]
    convert hmul using 1 <;> ring
  exact hcubic.trans hfinal

theorem window_shape_exponent_upper {r N : ℝ} (hr0 : 0 ≤ r)
    (hrh : r ≤ 1 / 2) (hN : 10 ≤ N) (x : ℝ) (hc : V22.windowConditions r N) (hw : x ^ 2 ≤ 3) :
    (N + 1) * sharedKLPsi r (sharedGaussianZ r N (Erdos993Lean.Analytic.V22.sN r N * x)) ≤
      Erdos993Lean.Analytic.V22.rho N / 2 * x ^ 2 +
        Erdos993Lean.Analytic.V22.epsilon r N * |x| +
        Erdos993Lean.Analytic.V22.c0 r N + Erdos993Lean.Analytic.V22.quarticError r N 3 := by
  have hr1 : r < 1 := by linarith
  have hn0 : 0 < N := by linarith
  have hn1 : 0 < N + 1 := by linarith
  have hv := shared_varianceR_pos hr0 hr1
  have hvr := shared_one_sub_sq_pos (by linarith : -1 < r) hr1
  have hs := shared_sN_sq hr0 hr1 hn0
  have hs0 : 0 ≤ Erdos993Lean.Analytic.V22.sN r N := Real.sqrt_nonneg _
  let u : ℝ := Erdos993Lean.Analytic.V22.sN r N * x
  let z : ℝ := sharedGaussianZ r N u
  have hu2 : u ^ 2 ≤ 3 * Erdos993Lean.Analytic.V22.varianceR r * N := by
    have h := mul_le_mul_of_nonneg_left hw (sq_nonneg (Erdos993Lean.Analytic.V22.sN r N))
    dsimp [u]
    simpa only [mul_pow, hs, mul_comm, mul_left_comm, mul_assoc] using h
  have huabs : |u| ≤ Real.sqrt 3 * Erdos993Lean.Analytic.V22.sN r N := by
    apply abs_le_of_sq_le_sq _ (by positivity)
    simpa only [u, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), hs,
      mul_assoc] using hu2
  obtain ⟨huL, huR⟩ := abs_le.mp huabs
  have hZL0 : 0 < V22.ZL r N 3 := by unfold V22.ZL; have hs := Real.sqrt_pos.2 (mul_pos hv hn0); positivity
  have hZR0 : 0 < V22.ZR r N 3 := by unfold V22.ZR; have hs := Real.sqrt_pos.2 (mul_pos hv hn0); positivity
  have hZL1 := hc.1
  have hrZR := hc.2.1
  have hDL : 0 < (1 - (Erdos993Lean.Analytic.V22.ZL r N 3) ^ 2) * (1 - r ^ 2) :=
    mul_pos (shared_one_sub_sq_pos (by linarith : -1 < Erdos993Lean.Analytic.V22.ZL r N 3) hZL1) hvr
  have hDR : 0 < (1 - (r + Erdos993Lean.Analytic.V22.ZR r N 3) ^ 2) * (1 - r ^ 2) :=
    mul_pos (shared_one_sub_sq_pos (by linarith : -1 < r + Erdos993Lean.Analytic.V22.ZR r N 3) hrZR) hvr
  have hquad := shared_lower_exponent_identity hr0 hr1 hn0 x
  have heps := shared_epsilon_nonneg hr0 hr1 hn0
  by_cases hleft : u ≤ r
  · have hz0 : z ≤ 0 := by dsimp [z, sharedGaussianZ]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hn1.le
    have hzL : -Erdos993Lean.Analytic.V22.ZL r N 3 ≤ z := by
      dsimp [z, sharedGaussianZ]
      unfold Erdos993Lean.Analytic.V22.ZL
      rw [← neg_div]
      exact div_le_div_of_nonneg_right (by linarith) hn1.le
    have hgauss := mul_le_mul_of_nonneg_left
      (sharedKLPsi_gaussian_left hr0 hr1 hZL0 hZL1 hzL hz0) hn1.le
    have hquartic : (N + 1) * z ^ 4 /
        (12 * ((1 - (Erdos993Lean.Analytic.V22.ZL r N 3) ^ 2) * (1 - r ^ 2))) ≤
        Erdos993Lean.Analytic.V22.quarticError r N 3 := by
      have hzabs : |z| ≤ V22.ZL r N 3 := by
        rw [abs_of_nonpos hz0]
        linarith
      have hmono := window_quartic_ratio_mono (z := z) (Z := V22.ZL r N 3)
        (A := N + 1) (D := (1 - (V22.ZL r N 3) ^ 2) * (1 - r ^ 2))
        hn1.le hDL hzabs
      have hmax : (N + 1) * (V22.ZL r N 3) ^ 4 /
          (12 * ((1 - (V22.ZL r N 3) ^ 2) * (1 - r ^ 2))) ≤
          V22.quarticError r N 3 := by
        unfold V22.quarticError
        simp only [mul_assoc]
        exact le_max_left
          ((N + 1) * (V22.ZL r N 3) ^ 4 /
            (12 * ((1 - (V22.ZL r N 3) ^ 2) * (1 - r ^ 2))) : ℝ)
          ((N + 1) * (V22.ZR r N 3) ^ 4 /
            (12 * ((1 - (r + V22.ZR r N 3) ^ 2) * (1 - r ^ 2))) : ℝ)
      exact hmono.trans hmax
    have hgauss' : (N + 1) * sharedKLPsi r z ≤
        (N + 1) * z ^ 2 / (2 * (1 - r ^ 2)) +
        (N + 1) * z ^ 4 /
          (12 * ((1 - (Erdos993Lean.Analytic.V22.ZL r N 3) ^ 2) * (1 - r ^ 2))) := by
      convert hgauss using 1 <;> ring
    change (N + 1) * z ^ 2 / (2 * (1 - r ^ 2)) = _ at hquad
    rw [hquad] at hgauss'
    have habs := mul_le_mul_of_nonneg_left (neg_le_abs x) heps
    change (N + 1) * sharedKLPsi r z ≤ _
    linarith
  · have hu : r ≤ u := by linarith
    have hz0 : 0 ≤ z := by dsimp [z, sharedGaussianZ]; exact div_nonneg (by linarith) hn1.le
    have hzR : z ≤ Erdos993Lean.Analytic.V22.ZR r N 3 := by
      dsimp [z, sharedGaussianZ]
      unfold Erdos993Lean.Analytic.V22.ZR
      exact div_le_div_of_nonneg_right (by linarith) hn1.le
    have hgauss := mul_le_mul_of_nonneg_left
      (sharedKLPsi_gaussian_right hr0 hr1 hZR0 hrZR hz0 hzR) hn1.le
    have hquartic : (N + 1) * z ^ 4 /
        (12 * ((1 - (r + Erdos993Lean.Analytic.V22.ZR r N 3) ^ 2) * (1 - r ^ 2))) ≤
        Erdos993Lean.Analytic.V22.quarticError r N 3 := by
      have hzabs : |z| ≤ V22.ZR r N 3 := by
        rw [abs_of_nonneg hz0]
        exact hzR
      have hmono := window_quartic_ratio_mono (z := z) (Z := V22.ZR r N 3)
        (A := N + 1) (D := (1 - (r + V22.ZR r N 3) ^ 2) * (1 - r ^ 2))
        hn1.le hDR hzabs
      have hmax : (N + 1) * (V22.ZR r N 3) ^ 4 /
          (12 * ((1 - (r + V22.ZR r N 3) ^ 2) * (1 - r ^ 2))) ≤
          V22.quarticError r N 3 := by
        unfold V22.quarticError
        simp only [mul_assoc]
        exact le_max_right
          ((N + 1) * (V22.ZL r N 3) ^ 4 /
            (12 * ((1 - (V22.ZL r N 3) ^ 2) * (1 - r ^ 2))) : ℝ)
          ((N + 1) * (V22.ZR r N 3) ^ 4 /
            (12 * ((1 - (r + V22.ZR r N 3) ^ 2) * (1 - r ^ 2))) : ℝ)
      exact hmono.trans hmax
    have hcubic := window_right_cubic_absorption hr0 hrh hN hc hu hu2
    have hlin : 2 * Erdos993Lean.Analytic.V22.epsilon r N * x =
        2 * r * u / (Erdos993Lean.Analytic.V22.varianceR r * (N + 1)) := by
      rw [shared_epsilon_eq hr0 hr1 hn0]
      dsimp [u]
      ring
    rw [← hlin] at hcubic
    have hgauss' : (N + 1) * sharedKLPsi r z ≤
        (N + 1) * z ^ 2 / (2 * (1 - r ^ 2)) +
        (N + 1) * r * z ^ 3 /
          (3 * ((1 - (r + Erdos993Lean.Analytic.V22.ZR r N 3) ^ 2) * (1 - r ^ 2))) +
        (N + 1) * z ^ 4 /
          (12 * ((1 - (r + Erdos993Lean.Analytic.V22.ZR r N 3) ^ 2) * (1 - r ^ 2))) := by
      convert hgauss using 1 <;> field_simp [hDR.ne'] <;> ring
    change (N + 1) * z ^ 2 / (2 * (1 - r ^ 2)) = _ at hquad
    rw [hquad] at hgauss'
    have habs := mul_le_mul_of_nonneg_left (le_abs_self x) heps
    change (N + 1) * sharedKLPsi r z ≤ _
    change (N + 1) * r * z ^ 3 /
      (3 * ((1 - (r + Erdos993Lean.Analytic.V22.ZR r N 3) ^ 2) * (1 - r ^ 2))) ≤
      2 * Erdos993Lean.Analytic.V22.epsilon r N * x at hcubic
    linarith


/-- Width three forces support on the entire integer domain, including the
source boundary atoms; support is proved rather than added as a premise. -/
theorem window_shape_support {N : ℕ} (hN : 10 ≤ N) {r : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (J : ℤ)
    (hw : (sharedGaussianX r N J) ^ 2 ≤ 3) : 0 ≤ J ∧ J ≤ (N : ℤ) := by
  have hNr : (10 : ℝ) ≤ N := by exact_mod_cast hN
  have hn : 0 < (N : ℝ) := by linarith
  have hr1 : r < 1 := by linarith
  have hv := shared_varianceR_pos hr0 hr1
  have hs : 0 < V22.sN r N := Real.sqrt_pos.2 (mul_pos hv hn)
  have hX : V22.sN r N * sharedGaussianX r N J = sharedGaussianU r N J := by
    unfold sharedGaussianX
    field_simp [hs.ne']
  have hu2 : (sharedGaussianU r N J) ^ 2 ≤ 3 * V22.varianceR r * (N : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hw (sq_nonneg (V22.sN r N))
    rw [shared_sN_sq hr0 hr1 hn] at h
    rw [← hX, mul_pow, shared_sN_sq hr0 hr1 hn]
    simpa only [mul_comm, mul_left_comm, mul_assoc] using h
  let p : ℝ := (1 - r) / 2
  let R : ℝ := p * ((N : ℝ) - 1) + 1 / 2
  have hp : (1 / 4 : ℝ) ≤ p := by dsimp [p]; linarith
  have hR : 0 ≤ R := by
    dsimp only [R]
    exact add_nonneg
      (mul_nonneg (by linarith : 0 ≤ p) (by linarith : 0 ≤ (N : ℝ) - 1))
      (by norm_num)
  have hvp : V22.varianceR r = p * (1 - p) := by dsimp [p]; unfold V22.varianceR; ring
  have hcoef : 0 ≤ (p + 1 / 4) * ((N : ℝ) ^ 2 + N + 1) - (2 * (N : ℝ) + 1) := by
    have h := mul_nonneg (show 0 ≤ p - 1 / 4 by linarith)
      (show 0 ≤ (N : ℝ) ^ 2 + N + 1 by positivity)
    nlinarith [mul_nonneg hn.le (show 0 ≤ (N : ℝ) - 10 by linarith)]
  have hpay := mul_nonneg (show 0 ≤ p - 1 / 4 by linarith) hcoef
  have hR2 : 3 * V22.varianceR r * (N : ℝ) ≤ R ^ 2 := by
    have hbase : 0 ≤ (N : ℝ) ^ 2 - 7 * N + 1 := by
      nlinarith [mul_nonneg hn.le (show 0 ≤ (N : ℝ) - 7 by linarith)]
    have he : R ^ 2 - 3 * V22.varianceR r * (N : ℝ) =
        (p - 1 / 4) * ((p + 1 / 4) * ((N : ℝ) ^ 2 + N + 1) - (2 * (N : ℝ) + 1)) +
          ((N : ℝ) ^ 2 - 7 * N + 1) / 16 := by rw [hvp]; dsimp [R]; ring
    linarith
  have hvle : V22.varianceR r ≤ (1 / 4 : ℝ) := by unfold V22.varianceR; nlinarith [sq_nonneg r]
  have hupper : (sharedGaussianU r N J) ^ 2 ≤ 3 * (N : ℝ) / 4 := by
    have h := mul_le_mul_of_nonneg_right hvle hn.le
    linarith
  have hc : (N : ℝ) / 2 ≤ (1 + r) / 2 * ((N : ℝ) - 1) + 1 / 2 := by
    nlinarith [mul_nonneg hr0 (show 0 ≤ (N : ℝ) - 1 by linarith)]
  have hJ0 : 0 ≤ (J : ℝ) := by
    by_contra! hJ
    have hu : sharedGaussianU r N J < -(N : ℝ) / 2 := by unfold sharedGaussianU; linarith
    have hsq := mul_pos (show 0 < -sharedGaussianU r N J - (N : ℝ) / 2 by linarith)
      (show 0 < -sharedGaussianU r N J + (N : ℝ) / 2 by linarith)
    nlinarith [mul_nonneg hn.le (show 0 ≤ (N : ℝ) - 3 by linarith)]
  have hJN : (J : ℝ) ≤ (N : ℝ) := by
    by_contra! hJ
    have hu : R < sharedGaussianU r N J := by dsimp [R, p]; unfold sharedGaussianU; linarith
    have hsq := mul_pos (show 0 < sharedGaussianU r N J - R by linarith)
      (show 0 < sharedGaussianU r N J + R by linarith)
    nlinarith
  exact ⟨by exact_mod_cast hJ0, by exact_mod_cast hJN⟩

/-- Lemma 5.10, both support and the native lower exponent under only its
original window conditions and width-three hypothesis. -/
theorem window_shape_bound {N : ℕ} (hN : 10 ≤ N) {r : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hc : V22.windowConditions r N) (J : ℤ)
    (hw : (sharedGaussianX r N J) ^ 2 ≤ 3) :
    (0 ≤ J ∧ J ≤ (N : ℤ)) ∧
      Real.exp (-V22.rho N / 2 * (sharedGaussianX r N J) ^ 2 - V22.epsilon r N * |sharedGaussianX r N J| -
        V22.c0 r N - V22.quarticError r N 3) ≤
        Real.sqrt (1 - r ^ 2) / V22.centralAmplitude N * binom N ((1 + r) / 2) J := by
  have hNr : (10 : ℝ) ≤ N := by exact_mod_cast hN
  have hr1 : r < 1 := by linarith
  have hn : 0 < (N : ℝ) := by linarith
  have hv := shared_one_sub_sq_pos (by linarith : -1 < r) hr1
  have hs : 0 < V22.sN r N := Real.sqrt_pos.2 (mul_pos (shared_varianceR_pos hr0 hr1) hn)
  have hX : V22.sN r N * sharedGaussianX r N J = sharedGaussianU r N J := by
    unfold sharedGaussianX
    field_simp [hs.ne']
  have hPsi := window_shape_exponent_upper hr0 hrh hNr (sharedGaussianX r N J) hc hw
  rw [hX, ← sharedGaussianZ_coordinate] at hPsi
  obtain ⟨hJ0, hJN⟩ := window_shape_support hN hr0 hrh J hw
  refine ⟨⟨hJ0, hJN⟩, ?_⟩
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

theorem window_ZR_eq {r N : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hN : 0 < N) :
    V22.ZR r N 3 = 2 * Real.sqrt 3 * Real.sqrt (V22.varianceR r) * V22.Z0 N := by
  unfold V22.ZR V22.sN V22.Z0
  rw [Real.sqrt_mul (shared_varianceR_pos hr0 hr1).le N]
  ring

theorem window_ZL_eq (r N : ℝ) : V22.ZL r N 3 = V22.ZR r N 3 + 2 * r / (N + 1) := by
  unfold V22.ZL V22.ZR
  ring

/-- The exact width-three radii decrease with the real trial-count parameter. -/
theorem window_radii_antitone {r Na N : ℝ} (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2)
    (ha : 10 ≤ Na) (haN : Na ≤ N) : V22.ZL r N 3 ≤ V22.ZL r Na 3 ∧ V22.ZR r N 3 ≤ V22.ZR r Na 3 := by
  have hn : 10 ≤ N := ha.trans haN
  have hcoef : 0 ≤ 2 * Real.sqrt 3 * Real.sqrt (V22.varianceR r) := by positivity
  have hZR : V22.ZR r N 3 ≤ V22.ZR r Na 3 := by
    rw [window_ZR_eq hr0 (by linarith) (by linarith), window_ZR_eq hr0 (by linarith) (by linarith)]
    exact mul_le_mul_of_nonneg_left (coefficient_Z0_antitone ha haN) hcoef
  have hr := div_le_div_of_nonneg_left (show 0 ≤ 2 * r by positivity)
    (show 0 < Na + 1 by linarith) (show Na + 1 ≤ N + 1 by linarith)
  rw [window_ZL_eq, window_ZL_eq]
  exact ⟨by linarith, hZR⟩

/-- Lemma 5.10's persistence clause includes the stated implication from
(c3') to (c3), rather than assuming the later-window conditions. -/
theorem window_conditions_persist {r Na N : ℝ} (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2)
    (ha : 10 ≤ Na) (haN : Na ≤ N) (hc : V22.persistentWindowConditions r Na) :
    V22.persistentWindowConditions r N ∧ V22.windowConditions r N := by
  have hn : 10 ≤ N := ha.trans haN
  have hd := shared_one_sub_sq_pos (by linarith : -1 < r) (by linarith : r < 1)
  have hrad := window_radii_antitone hr0 hrh ha haN
  have hsN0 : 0 ≤ V22.sN r N := Real.sqrt_nonneg _
  have hZR0 : 0 ≤ V22.ZR r N 3 := by
    unfold V22.ZR
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hsN0)
      (by linarith : 0 ≤ N + 1)
  have hsq : (r + V22.ZR r N 3) ^ 2 ≤ (r + V22.ZR r Na 3) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ V22.ZR r Na 3 - V22.ZR r N 3 by linarith)
      (show 0 ≤ 2 * r + V22.ZR r N 3 + V22.ZR r Na 3 by linarith)]
  have hC : 3 * (1 - r ^ 2) ≤ 12 * (1 - (r + V22.ZR r N 3) ^ 2) := by
    have h := (le_div_iff₀ hd).1 hc.2.2
    linarith
  have hrho : 0 < V22.rho N := by unfold V22.rho; positivity
  have hrho1 : V22.rho N ≤ 1 := by unfold V22.rho; exact (div_le_one (by linarith)).2 (by linarith)
  have hC3 : 3 * ((1 - r ^ 2) * V22.rho N) ≤ 12 * (1 - (r + V22.ZR r N 3) ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hrho1 (show 0 ≤ 3 * (1 - r ^ 2) by positivity)
    nlinarith
  exact ⟨⟨hrad.1.trans_lt hc.1, by linarith [hc.2.1], (le_div_iff₀ hd).2 hC⟩,
    ⟨hrad.1.trans_lt hc.1, by linarith [hc.2.1], (le_div_iff₀ (mul_pos hd hrho)).2 hC3⟩⟩

end Erdos993Lean.Analytic.V22.Analysis
