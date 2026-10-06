import Erdos993Lean.Analytic.V22.Analysis.ClosedRemainders

/-!
# Remainder monotonicity with the actual growing displacement cap

Source: the proof of Theorem4.15. The cap is exactly `min(6,r_m sqrt N)`.
It is not replaced by a fixed cap when the trial count changes. The scaled
coefficient theorem `N*alpha2` controls the growing square-root branch.
The finite monotonicity of `betaE` is consumed explicitly in the upper bound.
-/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

noncomputable def cappedNu (rm N : ℝ) : ℝ := min 6 (rm * Real.sqrt N)

theorem cappedNu_nonneg {rm N : ℝ} (hr : 0 ≤ rm) : 0 ≤ cappedNu rm N := by
  unfold cappedNu
  positivity

theorem cappedNu_ratio_eq {rm N : ℝ} (hN : 10 ≤ N) :
    cappedNu rm N / (N + 1) = min (6 / (N + 1)) (rm * V22.Z0 N) := by
  unfold cappedNu V22.Z0
  rw [← min_div_div_right (show 0 ≤ N + 1 by linarith)]
  congr 1
  ring

theorem cappedNu_ratio_antitone {rm N M : ℝ} (hN : 10 ≤ N) (hNM : N ≤ M)
    (hr : 0 ≤ rm) : cappedNu rm M / (M + 1) ≤ cappedNu rm N / (N + 1) := by
  rw [cappedNu_ratio_eq (hN.trans hNM), cappedNu_ratio_eq hN]
  exact min_le_min (div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith))
    (mul_le_mul_of_nonneg_left (coefficient_Z0_antitone hN hNM) hr)

theorem cappedNu_alpha2_eq {rm N : ℝ} (hN : 10 ≤ N) (hr0 : 0 ≤ rm)
    (hrh : rm ≤ 1 / 2) :
    V22.alpha2 N rm * cappedNu rm N =
      min (6 * V22.alpha2 N rm) (rm * (V22.alpha2 N rm * Real.sqrt N)) := by
  unfold cappedNu
  rw [mul_min_of_nonneg _ _ (coefficient_alpha_nonneg hN hr0 hrh).2]
  congr 1 <;> ring

theorem cappedNu_alpha2_antitone {rm N M : ℝ} (hN : 10 ≤ N) (hNM : N ≤ M)
    (hr0 : 0 ≤ rm) (hrh : rm ≤ 1 / 2) :
    V22.alpha2 M rm * cappedNu rm M ≤ V22.alpha2 N rm * cappedNu rm N := by
  rw [cappedNu_alpha2_eq (hN.trans hNM) hr0 hrh, cappedNu_alpha2_eq hN hr0 hrh]
  exact min_le_min
    (mul_le_mul_of_nonneg_left (coefficient_alpha2_antitone hN hNM hr0 hrh) (by norm_num))
    (mul_le_mul_of_nonneg_left (coefficient_sqrt_alpha2_antitone hN hNM hr0 hrh) hr0)

theorem cappedNu_ebar_decomposition (rm N : ℝ) :
    V22.ebar N rm (cappedNu rm N) =
      V22.alpha1 N rm * (cappedNu rm N / (N + 1)) +
      (V22.alpha2 N rm * cappedNu rm N) * (cappedNu rm N / (N + 1)) := by
  unfold V22.ebar
  ring

theorem cappedNu_ebar_antitone {rm N M : ℝ} (hN : 10 ≤ N) (hNM : N ≤ M)
    (hr0 : 0 ≤ rm) (hrh : rm ≤ 1 / 2) :
    V22.ebar M rm (cappedNu rm M) ≤ V22.ebar N rm (cappedNu rm N) := by
  obtain ⟨hA, hB⟩ := coefficient_alpha_nonneg hN hr0 hrh
  have hCap := cappedNu_nonneg (N := N) hr0
  have hRatio := cappedNu_ratio_antitone hN hNM hr0
  have hRatioM : 0 ≤ cappedNu rm M / (M + 1) := by
    exact div_nonneg (cappedNu_nonneg hr0) (by linarith)
  have hFirst := mul_le_mul (coefficient_alpha1_antitone hN hNM hr0 hrh) hRatio hRatioM hA
  have hSecond := mul_le_mul (cappedNu_alpha2_antitone hN hNM hr0 hrh) hRatio hRatioM
    (mul_nonneg hB hCap)
  rw [cappedNu_ebar_decomposition, cappedNu_ebar_decomposition]
  exact add_le_add hFirst hSecond

theorem cappedNu_betaL_rewrite (t N M0 rm : ℝ) :
    V22.betaL t N M0 rm (cappedNu rm N) =
      (N - 1) * (1 - V22.ebar N rm (cappedNu rm N)) -
      2 * V22.sigma0 t M0 * V22.alpha2 N rm -
      2 * (V22.alpha1 N rm + V22.alpha2 N rm * cappedNu rm N) ^ 2 / (N + 1) := by
  unfold V22.betaL
  ring

/-- The lower denominator grows once the actual starting denominator is
positive. Its growing cap remains present on both sides. -/
theorem cappedNu_betaL_monotone {t N M M0 rm : ℝ} (hN : 10 ≤ N) (hNM : N ≤ M)
    (hr0 : 0 ≤ rm) (hrh : rm ≤ 1 / 2)
    (hbeta : 0 < V22.betaL t N M0 rm (cappedNu rm N)) :
    V22.betaL t N M0 rm (cappedNu rm N) ≤ V22.betaL t M M0 rm (cappedNu rm M) := by
  have hM := hN.trans hNM
  have hE := cappedNu_ebar_antitone hN hNM hr0 hrh
  have hE1 := closed_betaL_forces_ebar hN hr0 hrh (cappedNu_nonneg hr0) hbeta
  have hA := coefficient_alpha1_antitone hN hNM hr0 hrh
  have hB := coefficient_alpha2_antitone hN hNM hr0 hrh
  have hBCap := cappedNu_alpha2_antitone hN hNM hr0 hrh
  have hsum : V22.alpha1 M rm + V22.alpha2 M rm * cappedNu rm M ≤
      V22.alpha1 N rm + V22.alpha2 N rm * cappedNu rm N := add_le_add hA hBCap
  have hsumM : 0 ≤ V22.alpha1 M rm + V22.alpha2 M rm * cappedNu rm M := by
    obtain ⟨ha, hb⟩ := coefficient_alpha_nonneg hM hr0 hrh
    exact add_nonneg ha (mul_nonneg hb (cappedNu_nonneg hr0))
  have hsq := (sq_le_sq₀ hsumM (hsumM.trans hsum)).2 hsum
  have hQ : 2 * (V22.alpha1 M rm + V22.alpha2 M rm * cappedNu rm M) ^ 2 / (M + 1) ≤
      2 * (V22.alpha1 N rm + V22.alpha2 N rm * cappedNu rm N) ^ 2 / (N + 1) :=
    div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hsq (by norm_num))
      (by linarith) (by linarith)
  have hSigma : 0 ≤ 2 * V22.sigma0 t M0 := by
    unfold V22.sigma0 V22.positivePart
    positivity
  have hSigmaB := mul_le_mul_of_nonneg_left hB hSigma
  have hProduct : (N - 1) * (1 - V22.ebar N rm (cappedNu rm N)) ≤
      (M - 1) * (1 - V22.ebar M rm (cappedNu rm M)) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  rw [cappedNu_betaL_rewrite, cappedNu_betaL_rewrite]
  linarith

theorem cappedNu_dLbar_antitone {t N M M0 rm : ℝ} (hN : 10 ≤ N) (hNM : N ≤ M)
    (hr0 : 0 ≤ rm) (hrh : rm ≤ 1 / 2)
    (hbeta : 0 < V22.betaL t N M0 rm (cappedNu rm N)) :
    V22.dLbar t M M0 rm (cappedNu rm M) ≤ V22.dLbar t N M0 rm (cappedNu rm N) := by
  have hBeta := cappedNu_betaL_monotone hN hNM hr0 hrh hbeta
  have hS : 0 ≤ V22.sigma0 t M0 := le_max_right _ _
  have hA := coefficient_alpha1_antitone hN hNM hr0 hrh
  have hProd := mul_le_mul_of_nonneg_left hA hS
  have hProdM : 0 ≤ V22.sigma0 t M0 * V22.alpha1 M rm :=
    mul_nonneg hS (coefficient_alpha_nonneg (hN.trans hNM) hr0 hrh).1
  unfold V22.dLbar
  exact div_le_div₀ (sq_nonneg _) ((sq_le_sq₀ hProdM (hProdM.trans hProd)).2 hProd) hbeta hBeta

/-- The two upper denominators increase with the trial count; the named
`betaE` comparison is the finite derivative/monotonicity consumer. -/
theorem cappedNu_dUbar_antitone {t N M M0 rm : ℝ} (hN : 10 ≤ N) (hNM : N ≤ M)
    (hr0 : 0 ≤ rm) (hrh : rm ≤ 1 / 2)
    (hBeta : V22.betaE N rm (cappedNu rm N) ≤ V22.betaE M rm (cappedNu rm M))
    (hBeta0 : 0 < V22.betaE N rm (cappedNu rm N))
    (hB10 : 0 < N - 1 - V22.kappaA N rm * V22.Ghat t M0 / V22.rhoStar N rm) :
    V22.dUbar t M M0 rm (cappedNu rm M) ≤ V22.dUbar t N M0 rm (cappedNu rm N) := by
  have hM := hN.trans hNM
  have hrsN := coefficient_rhoStar_pos hN hr0 hrh
  have hrsM := coefficient_rhoStar_pos hM hr0 hrh
  have hrs := coefficient_rhoStar_monotone hN hNM hr0 hrh
  have hsq := (sq_le_sq₀ hrsN.le hrsM.le).2 hrs
  have hGh : 0 ≤ V22.Ghat t M0 := by
    unfold V22.Ghat
    rw [shared_G_eq, shared_G_eq]
    exact (rootG_nonneg _).trans (le_max_left _ _)
  have hKap := coefficient_kappaA_antitone hN hNM hr0 hrh
  have hKap0 := (coefficient_remaining_nonneg hN hr0 hrh).1
  have hRatio : V22.kappaA M rm * V22.Ghat t M0 / V22.rhoStar M rm ≤
      V22.kappaA N rm * V22.Ghat t M0 / V22.rhoStar N rm :=
    div_le_div₀ (mul_nonneg hKap0 hGh) (mul_le_mul_of_nonneg_right hKap hGh) hrsN hrs
  have hB1 : N - 1 - V22.kappaA N rm * V22.Ghat t M0 / V22.rhoStar N rm ≤
      M - 1 - V22.kappaA M rm * V22.Ghat t M0 / V22.rhoStar M rm := by linarith
  have hB1M : 0 < M - 1 - V22.kappaA M rm * V22.Ghat t M0 / V22.rhoStar M rm :=
    hB10.trans_le hB1
  have hDen1 := mul_le_mul hsq hB1 hB10.le (sq_nonneg (V22.rhoStar M rm))
  have hDen2 := mul_le_mul hsq hBeta hBeta0.le (sq_nonneg (V22.rhoStar M rm))
  have hFirst : 4 * (V22.Ghat t M0) ^ 2 /
      ((V22.rhoStar M rm) ^ 2 * (M - 1 - V22.kappaA M rm * V22.Ghat t M0 / V22.rhoStar M rm)) ≤
      4 * (V22.Ghat t M0) ^ 2 /
      ((V22.rhoStar N rm) ^ 2 * (N - 1 - V22.kappaA N rm * V22.Ghat t M0 / V22.rhoStar N rm)) :=
    div_le_div_of_nonneg_left (by positivity) (mul_pos (sq_pos_of_pos hrsN) hB10) hDen1
  have hSecond : 4 / ((V22.rhoStar M rm) ^ 2 * V22.betaE M rm (cappedNu rm M)) ≤
      4 / ((V22.rhoStar N rm) ^ 2 * V22.betaE N rm (cappedNu rm N)) :=
    div_le_div_of_nonneg_left (by norm_num) (mul_pos (sq_pos_of_pos hrsN) hBeta0) hDen2
  have hSecondS := mul_le_mul_of_nonneg_left hSecond (abs_nonneg (V22.G1 (V22.lambdaT t)))
  have hSecondScaled : |V22.G1 (V22.lambdaT t)| * 4 /
      ((V22.rhoStar M rm) ^ 2 * V22.betaE M rm (cappedNu rm M)) ≤
      |V22.G1 (V22.lambdaT t)| * 4 /
        ((V22.rhoStar N rm) ^ 2 * V22.betaE N rm (cappedNu rm N)) := by
    convert hSecondS using 1 <;> ring
  unfold V22.dUbar
  exact add_le_add hFirst hSecondScaled

end Erdos993Lean.Analytic.V22.Analysis
