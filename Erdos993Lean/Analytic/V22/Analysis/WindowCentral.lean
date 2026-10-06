import Erdos993Lean.Analytic.V22.Analysis.BonusRangeBounds
import Erdos993Lean.Analytic.V22.Analysis.WallisUpper

/-! Source: frozen note Lemma 5.9. The central amplitude remains at an
integer trial count with its exact parity branch; no interpolation is used.
The proof of its upper enclosure uses the native Wallis bound and elementary
entropy/log estimates. The parent owns compilation. -/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real

theorem shared_lambdaTc_eq (mu : ℝ) (N : ℕ) :
    V22.lambdaTc mu N = shapeTemplateLambda mu (N : ℝ) (V22.centralAmplitude N) := by
  simp only [V22.lambdaTc, shapeTemplateLambda, shapeTemplatePrefactor,
    shared_gaussianAmplitude_eq, V22.rho, Real.rpow_eq_pow]

/-- The series estimate needed in the odd central-amplitude branch, proved
directly from the native artanh and logarithm comparisons. -/
theorem window_entropy_upper {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    sharedKLI x ≤ x ^ 2 / (2 * (1 - x)) := by
  have hd := shared_one_sub_sq_pos (by linarith : -1 < x) hx1
  have ha : V22.artanh x ≤ x / (1 - x ^ 2) := by
    have hb := (sharedAHat_bounds hx0 hx1).2
    unfold V22.aHat at hb
    have he : x + x ^ 3 / (3 * (1 - x ^ 2)) ≤ x / (1 - x ^ 2) := by
      apply (le_div_iff₀ hd).2
      have hmul : (x ^ 3 / (3 * (1 - x ^ 2))) * (1 - x ^ 2) = x ^ 3 / 3 := by
        field_simp [hd.ne'] <;> ring
      rw [add_mul, hmul]
      nlinarith [pow_nonneg hx0 3]
    exact (by linarith : V22.artanh x ≤ x + x ^ 3 / (3 * (1 - x ^ 2))).trans he
  have hlog := Real.log_le_sub_one_of_pos hd
  have hprod := mul_le_mul_of_nonneg_left ha hx0
  have hpoly : x * (x / (1 - x ^ 2)) - x ^ 2 / 2 ≤ x ^ 2 / (2 * (1 - x)) := by
    have hdm : 0 < 1 - x := by linarith
    apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hdm)).2
    have he : (x * (x / (1 - x ^ 2)) - x ^ 2 / 2) * (2 * (1 - x)) =
        x ^ 2 * (1 + x ^ 2) / (1 + x) := by
      field_simp [hd.ne', hdm.ne', (by linarith : (1 + x : ℝ) ≠ 0)] <;> ring
    rw [he]
    apply (div_le_iff₀ (by linarith : 0 < 1 + x)).2
    nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ x * (1 - x) by positivity)]
  unfold sharedKLI
  linarith

theorem window_odd_entropy_gain {N : ℝ} (hN : 1 < N) :
    (N + 1) * sharedKLI (1 / (N + 1)) ≤ 1 / (2 * N) := by
  have hn : 0 < N := by linarith
  have hn1 : 0 < N + 1 := by linarith
  have hi := mul_le_mul_of_nonneg_left
    (window_entropy_upper (by positivity : 0 ≤ 1 / (N + 1))
      ((div_lt_one hn1).2 (by linarith))) hn1.le
  have hsmall : 1 / (N + 1) < 1 := (div_lt_one hn1).2 (by linarith)
  have hden : 0 < 1 - 1 / (N + 1) := by linarith
  convert hi using 1 <;>
    field_simp [hn.ne', hn1.ne', hden.ne'] <;> ring

private theorem window_wallis_log {N : ℝ} (hN : 0 < N) {m : ℕ}
    (hm : N / 2 ≤ (m : ℝ)) :
    Real.log (centralMass m) ≤ -(1 / 2 : ℝ) * Real.log (Real.pi * N / 2) := by
  have hb : 0 < Real.pi * N / 2 := by positivity
  have hroot : Real.sqrt (Real.pi * N / 2) ≤ Real.sqrt (Real.pi * ((m : ℝ) + 1 / 4)) :=
    Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])
  have hW : centralMass m ≤ (Real.sqrt (Real.pi * N / 2))⁻¹ :=
    (centralMass_upper_sqrt m).trans
      ((inv_le_inv₀ (by positivity) (Real.sqrt_pos.2 hb)).2 hroot)
  have hl := Real.log_le_log (centralMass_pos m) hW
  rw [Real.log_inv, Real.log_sqrt hb.le] at hl
  linarith

/-- The native parity-defined amplitude has the source's upper enclosure. -/
theorem window_central_log_upper {N : ℕ} (hN : 10 ≤ N) :
    Real.log (V22.centralAmplitude N) ≤ -(1 / 2 : ℝ) * Real.log (Real.pi * (N : ℝ) / 2) +
      1 / (2 * (N : ℝ)) := by
  have hNr : (10 : ℝ) ≤ N := by exact_mod_cast hN
  have hn : 0 < (N : ℝ) := by linarith
  rw [shared_centralAmplitude_eq]
  by_cases he : N % 2 = 0
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, N = 2 * m := ⟨N / 2, by omega⟩
    rw [interiorCentralPrefactor_even]
    have hm : (((2 * m : ℕ) : ℝ) / 2) ≤ (m : ℝ) := by push_cast; linarith
    have hW := window_wallis_log hn hm
    have hgain : 0 ≤ 1 / (2 * ((2*m : ℕ) : ℝ)) := by positivity
    linarith
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, N = 2 * m + 1 := ⟨N / 2, by omega⟩
    rw [interiorCentralPrefactor_odd,
      Real.log_mul (centralMass_pos (m + 1)).ne' (Real.exp_pos _).ne', Real.log_exp]
    have hm : (((2 * m + 1 : ℕ) : ℝ) / 2) ≤ ((m + 1 : ℕ) : ℝ) := by push_cast; linarith
    have hW := window_wallis_log hn hm
    have hi := window_odd_entropy_gain (by linarith : 1 < ((2 * m + 1 : ℕ) : ℝ))
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hi hW ⊢
    norm_num only [add_assoc] at hi ⊢
    linarith

/-- The positive logarithmic margin in the lower enclosure of Lemma 5.9. -/
theorem window_lambdaTc_margin {N : ℝ} (hN : 10 ≤ N) :
    0 ≤ (5 / 2 : ℝ) * Real.log (1 + 2 / (N - 2)) + Real.log (1 - 1 / N) -
      1 / (2 * (N + 1)) - 1 / (2 * N) := by
  have hn : 0 < N := by linarith
  have hnm : 0 < N - 2 := by linarith
  have hplus := logShift_log_one_add_lower (by positivity : 0 ≤ 2 / (N - 2))
  have hx := logShift_inv_small hN
  have hminus := logShift_neg_log_one_sub_small_upper hx.1.le hx.2
  have hi : 1 / (2 * (N + 1)) ≤ 1 / (2 * N) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hf : 0 ≤ 3 / N - 5 / (N - 2) ^ 2 - 1 / N ^ 2 := by
    have he : 3 / N - 5 / (N - 2) ^ 2 - 1 / N ^ 2 =
        (3 * N ^ 2 * (N - 6) + 16 * N - 4) / (N ^ 2 * (N - 2) ^ 2) := by
      field_simp [hn.ne', hnm.ne'] <;> ring
    rw [he]
    apply div_nonneg _ (by positivity)
    nlinarith [mul_nonneg (sq_nonneg N) (show 0 ≤ N - 6 by linarith)]
  have hrat : 5 / N ≤ 5 / (N - 2) := div_le_div_of_nonneg_left (by norm_num) hnm (by linarith)
  have hid : (5 / 2 : ℝ) * (2 / (N - 2) - (2 / (N - 2)) ^ 2 / 2) =
      5 / (N - 2) - 5 / (N - 2) ^ 2 := by
    field_simp [hnm.ne'] <;> ring
  have hplus2 := mul_le_mul_of_nonneg_left hplus (by norm_num : (0 : ℝ) ≤ 5 / 2)
  rw [hid] at hplus2
  have hhalf : 1 / (2 * N) = (1 / N) / 2 := by ring
  have hsq : (1 / N) ^ 2 = 1 / N ^ 2 := by
    field_simp [hn.ne'] <;> ring
  rw [hhalf] at hi ⊢
  have hminusSq : -Real.log (1 - 1 / N) ≤
      1 / N + (43 / 80 : ℝ) * (1 / N ^ 2) := by
    simpa only [hsq] using hminus
  have hrecipSq : 0 ≤ (1 : ℝ) / N ^ 2 := by positivity
  have hminusNormalized : -Real.log (1 - 1 / N) ≤ 1 / N + 1 / N ^ 2 := by
    linarith only [hminusSq, hrecipSq]
  have hlower : 0 ≤ 5 / (N - 2) - 5 / (N - 2) ^ 2 - 2 / N - 1 / N ^ 2 := by
    calc
      0 ≤ (3 / N - 5 / (N - 2) ^ 2 - 1 / N ^ 2) +
          (5 / (N - 2) - 5 / N) := add_nonneg hf (sub_nonneg.mpr hrat)
      _ = 5 / (N - 2) - 5 / (N - 2) ^ 2 - 2 / N - 1 / N ^ 2 := by ring
  calc
    0 ≤ 5 / (N - 2) - 5 / (N - 2) ^ 2 - 2 / N - 1 / N ^ 2 := hlower
    _ ≤ (5 / 2 : ℝ) * Real.log (1 + 2 / (N - 2)) + Real.log (1 - 1 / N) -
        1 / (2 * (N + 1)) - (1 / N) / 2 := by
      have hlogLower : -(1 / N + 1 / N ^ 2) ≤ Real.log (1 - 1 / N) := by
        simpa only [neg_neg] using neg_le_neg hminusNormalized
      calc
        5 / (N - 2) - 5 / (N - 2) ^ 2 - 2 / N - 1 / N ^ 2 =
            ((5 / (N - 2) - 5 / (N - 2) ^ 2) + -(1 / N + 1 / N ^ 2) +
              -((1 / N) / 2)) - (1 / N) / 2 := by ring
        _ ≤ ((5 / 2 : ℝ) * Real.log (1 + 2 / (N - 2)) + Real.log (1 - 1 / N) +
              -(1 / (2 * (N + 1)))) - (1 / N) / 2 :=
          sub_le_sub_right (add_le_add (add_le_add hplus2 hlogLower) (neg_le_neg hi)) _
        _ = (5 / 2 : ℝ) * Real.log (1 + 2 / (N - 2)) + Real.log (1 - 1 / N) -
              1 / (2 * (N + 1)) - (1 / N) / 2 := by ring

private theorem window_shapeAmplitude_log_upper {N : ℕ} (hN : 10 ≤ N) :
    Real.log (shapeAmplitude (N : ℝ) (V22.centralAmplitude N)) ≤
      -Real.log (1 - 1 / (N : ℝ)) + 1 / (2 * (N : ℝ)) := by
  have hNr : (10 : ℝ) ≤ N := by exact_mod_cast hN
  have hn : 0 < (N : ℝ) := by linarith
  have hNm : 0 < (N : ℝ) - 1 := by linarith
  have hx : 0 < 1 - 1 / (N : ℝ) := by
    exact sub_pos.mpr ((div_lt_one hn).2 (by linarith))
  have hc := shared_centralAmplitude_pos N
  have hlogN : Real.log ((N : ℝ) - 1) = Real.log (N : ℝ) + Real.log (1 - 1 / (N : ℝ)) := by
    rw [← Real.log_mul hn.ne' hx.ne']
    congr 1
    field_simp [hn.ne']
  have hlogpi : Real.log (Real.pi * (N : ℝ) / 2) = Real.log (Real.pi / 2) + Real.log (N : ℝ) := by
    rw [← Real.log_mul (by positivity : (Real.pi / 2 : ℝ) ≠ 0) hn.ne']
    congr 1
    ring
  have hcentral := window_central_log_upper hN
  rw [hlogpi] at hcentral
  rw [Real.log_div Real.pi_pos.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hcentral
  unfold shapeAmplitude
  simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_rpow]
  rw [hlogN]
  linarith

/-- Lemma 5.9, retaining the actual `t=M/mu` and the integer central amplitude. -/
theorem window_lambdaTc_enclosure {M : ℕ} (hN : 10 ≤ M + 2) {mu : ℝ} (hmu : 0 < mu) :
    activityOneLambda_t ((M : ℝ) / mu) ≤ V22.lambdaTc mu (M + 2) ∧
      V22.lambdaTc mu (M + 2) ≤ activityOneLambda M mu .L ∧
      activityOneLambda M mu .L ≤ activityOneLambda_t ((M : ℝ) / mu) +
        ((77 / 20 : ℝ) + 10 / (M : ℝ)) / ((M : ℝ) + 3) := by
  have hM : 8 ≤ M := by omega
  have hm : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hNr : (10 : ℝ) ≤ (M : ℝ) + 2 := by exact_mod_cast hN
  have hn : 1 < (M : ℝ) + 2 := by linarith
  have hc := shared_centralAmplitude_pos (M + 2)
  have hL := symmetricLowerPrefactor_pos (by omega : 2 ≤ M + 2)
  have hshift := activityOneLambda_shift (by omega : 1 ≤ M) hmu .L
  have hk := (activityOneK_bounds hM .L).2
  have hupper : activityOneLambda M mu .L ≤ activityOneLambda_t ((M : ℝ) / mu) +
      ((77 / 20 : ℝ) + 10 / (M : ℝ)) / ((M : ℝ) + 3) := by
    rw [hshift]
    have hquot : activityOneK M .L / ((M : ℝ) + 3) ≤
        ((77 / 20 : ℝ) + 10 / (M : ℝ)) / ((M : ℝ) + 3) :=
      div_le_div_of_nonneg_right hk (by positivity)
    linarith
  have hcentral := shared_centralAmplitude_lower (by omega : 2 ≤ M + 2)
  have he0 : 0 ≤ V22.quarticErrorZero ((M + 2 : ℕ) : ℝ) := by unfold V22.quarticErrorZero; positivity
  have hLcentral : symmetricLowerPrefactor (M + 2) ≤ V22.centralAmplitude (M + 2) := by
    have h := mul_le_mul_of_nonneg_left (Real.one_le_exp he0) hL.le
    have hExp : symmetricLowerPrefactor (M + 2) ≤ symmetricLowerPrefactor (M + 2) *
        Real.exp (V22.quarticErrorZero ((M + 2 : ℕ) : ℝ)) := by
      simpa only [mul_one] using h
    exact hExp.trans hcentral
  have hPT := mul_le_mul_of_nonneg_left hLcentral
    (show 0 ≤ mu ^ (3 / 2 : ℝ) / (2 * gaussianA * ((M : ℝ) + 1)) from by
      have ha := shapeGaussianA_pos; positivity)
  have hPc : shapeTemplatePrefactor mu ((M : ℝ) + 2) (symmetricLowerPrefactor (M + 2)) ≤
      shapeTemplatePrefactor mu ((M : ℝ) + 2) (V22.centralAmplitude (M + 2)) := by
    convert hPT using 1 <;> unfold shapeTemplatePrefactor <;> ring
  have hmiddle : V22.lambdaTc mu (M + 2) ≤ activityOneLambda M mu .L := by
    rw [shared_lambdaTc_eq]
    simp only [Nat.cast_add, Nat.cast_ofNat]
    change shapeTemplateLambda mu ((M : ℝ) + 2) (V22.centralAmplitude (M + 2)) ≤
      shapeTemplateLambda mu ((M : ℝ) + 2) (symmetricLowerPrefactor (M + 2))
    have hnum : 0 < (((M : ℝ) + 2) / mu) *
        Real.exp ((((M : ℝ) + 2) / ((M : ℝ) + 2 + 1)) / 2) := by positivity
    have hquot := div_le_div_of_nonneg_left hnum.le
      (shapeTemplatePrefactor_pos hmu hn hL) hPc
    unfold shapeTemplateLambda
    exact Real.log_le_log
      (div_pos hnum (shapeTemplatePrefactor_pos hmu hn hc)) hquot
  have hlogratio : Real.log (((M : ℝ) + 2) / mu) =
      Real.log ((M : ℝ) / mu) + Real.log (1 + 2 / (M : ℝ)) := by
    rw [← Real.log_mul (div_pos hm hmu).ne' (by positivity : (1 + 2 / (M : ℝ) : ℝ) ≠ 0)]
    congr 1
    field_simp [hm.ne', hmu.ne']
  have hformula := shapeTemplateLambda_eq hmu hn hc
  have hcentralLog := window_shapeAmplitude_log_upper hN
  simp only [Nat.cast_add, Nat.cast_ofNat] at hcentralLog
  have hf := window_lambdaTc_margin hNr
  have hlower : activityOneLambda_t ((M : ℝ) / mu) ≤ V22.lambdaTc mu (M + 2) := by
    rw [shared_lambdaTc_eq]
    simp only [Nat.cast_add, Nat.cast_ofNat]
    rw [hformula, hlogratio]
    unfold activityOneLambda_t
    norm_num only [add_sub_cancel_right] at hf
    linarith
  exact ⟨hlower, hmiddle, hupper⟩

end Erdos993Lean.Analytic.V22.Analysis
