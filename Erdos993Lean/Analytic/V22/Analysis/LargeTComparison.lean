import Erdos993Lean.Analytic.V22.Analysis.CoefficientMonotonicity
import Erdos993Lean.Analytic.V22.Checks.EarlyStatements

/-!
# The exact two-regime large-activity comparison

Source: the monotonicity and radical split in the proof of Lemma 4.14.
The finite premises are the native `largeTConditions`, whose split is exactly
`r_m sqrt N_*`, including the common endpoint. No rounded gap or sliver is
introduced. This module transports the finite majorant comparison to every
admissible actual trial count; the fiber theorem consumes it separately.
-/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

theorem largeT_Xbar_decomposition {nu N rm : ℝ} (hN : 0 < N)
    (hr : 0 < 1 - rm ^ 2) :
    V22.Xbar nu N rm =
      nu ^ 4 / (12 * (1 - rm ^ 2) ^ 2) * (1 / N + 1 / N ^ 2) +
      nu * Real.sqrt (1 + nu ^ 2) *
        (1 / (N + 1) + nu ^ 2 / (6 * N * (1 - rm ^ 2))) -
      V22.rhoStar N rm / 2 * (1 + nu ^ 2 * V22.cCoef N) := by
  unfold V22.Xbar
  field_simp [hN.ne', (show N + 1 ≠ 0 by linarith), hr.ne'] <;> ring

/-- At fixed actual `nu`, each majorant term moves in the stated direction. -/
theorem largeT_Xbar_antitone {nu N M rm : ℝ} (hnu : 0 ≤ nu)
    (hN : 10 ≤ N) (hNM : N ≤ M) (hr0 : 0 ≤ rm) (hr1 : rm ≤ 1 / 2) :
    V22.Xbar nu M rm ≤ V22.Xbar nu N rm := by
  have hM : 10 ≤ M := hN.trans hNM
  have hNp : 0 < N := by linarith
  have hMp : 0 < M := by linarith
  have hd := coefficient_one_sub_rm_sq_pos hr0 hr1
  have hInv : 1 / M ≤ 1 / N := one_div_le_one_div_of_le hNp hNM
  have hInv2 : 1 / M ^ 2 ≤ 1 / N ^ 2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos hNp) ((sq_le_sq₀ hNp.le hMp.le).2 hNM)
  have hInv1 : 1 / (M + 1) ≤ 1 / (N + 1) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have hNu2 : nu ^ 2 / (6 * M * (1 - rm ^ 2)) ≤
      nu ^ 2 / (6 * N * (1 - rm ^ 2)) := by
    apply div_le_div_of_nonneg_left (sq_nonneg nu) (by positivity)
    nlinarith
  have hFirst := mul_le_mul_of_nonneg_left (add_le_add hInv hInv2)
    (show 0 ≤ nu ^ 4 / (12 * (1 - rm ^ 2) ^ 2) by positivity)
  have hSecond := mul_le_mul_of_nonneg_left (add_le_add hInv1 hNu2)
    (show 0 ≤ nu * Real.sqrt (1 + nu ^ 2) by positivity)
  have hRho := coefficient_rhoStar_monotone hN hNM hr0 hr1
  have hRho0 := (coefficient_rhoStar_pos hN hr0 hr1).le
  have hC := coefficient_cCoef_monotone hN hNM
  have hC0 : 0 ≤ V22.cCoef N := by linarith [(coefficient_cCoef_bounds hN).1]
  have hFactor : 1 + nu ^ 2 * V22.cCoef N ≤ 1 + nu ^ 2 * V22.cCoef M := by
    nlinarith [mul_le_mul_of_nonneg_left hC (sq_nonneg nu)]
  have hProduct : V22.rhoStar N rm / 2 * (1 + nu ^ 2 * V22.cCoef N) ≤
      V22.rhoStar M rm / 2 * (1 + nu ^ 2 * V22.cCoef M) := by
    apply mul_le_mul (by linarith) hFactor
    · nlinarith [mul_nonneg (sq_nonneg nu) hC0]
    · exact div_nonneg (hRho0.trans hRho) (by norm_num)
  rw [largeT_Xbar_decomposition hNp hd, largeT_Xbar_decomposition hMp hd]
  linarith

/-- Transport either exact finite regime to an arbitrary fiber count. -/
theorem largeT_comparison_at_actual_N {nu N rm Nstar : ℝ}
    (hfinite : V22.Checks.largeTConditions rm Nstar)
    (hr0 : 0 < rm) (hr1 : rm ≤ 1 / 2) (hNs : 10 ≤ Nstar)
    (hN : Nstar ≤ N) (hnu0 : 0 ≤ nu) (hnu6 : nu ≤ 6)
    (hCap : nu ^ 2 / rm ^ 2 ≤ N) :
    V22.Xbar nu N rm ≤ Real.log ((257 / 100) * V22.rhoStar N rm) := by
  have hNp : 0 < Nstar := by linarith
  have hN10 : 10 ≤ N := hNs.trans hN
  have hRhoPos (n : ℝ) (hn : 10 ≤ n) : 0 < (257 / 100 : ℝ) * V22.rhoStar n rm :=
    mul_pos (by norm_num) (coefficient_rhoStar_pos hn hr0.le hr1)
  rcases le_total nu (rm * Real.sqrt Nstar) with hLow | hHigh
  · have hBase := hfinite.1 nu ⟨hnu0, hLow⟩
    have hX := largeT_Xbar_antitone hnu0 hNs hN hr0.le hr1
    have hRho := coefficient_rhoStar_monotone hNs hN hr0.le hr1
    have hLog : Real.log ((257 / 100) * V22.rhoStar Nstar rm) ≤
        Real.log ((257 / 100) * V22.rhoStar N rm) := by
      apply Real.log_le_log (hRhoPos Nstar hNs)
      nlinarith
    exact hX.trans (hBase.trans hLog)
  · have hStart : Nstar ≤ nu ^ 2 / rm ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hr0)).2
      have hSq : (rm * Real.sqrt Nstar) ^ 2 ≤ nu ^ 2 :=
        (sq_le_sq₀ (by positivity) hnu0).2 hHigh
      rw [mul_pow, Real.sq_sqrt hNp.le] at hSq
      nlinarith
    have hBase := hfinite.2.1 nu ⟨hHigh, hnu6⟩
    have hX := largeT_Xbar_antitone hnu0 (hNs.trans hStart) hCap hr0.le hr1
    have hRho := coefficient_rhoStar_monotone (hNs.trans hStart) hCap hr0.le hr1
    have hLog : Real.log ((257 / 100) * V22.rhoStar (nu ^ 2 / rm ^ 2) rm) ≤
        Real.log ((257 / 100) * V22.rhoStar N rm) := by
      apply Real.log_le_log (hRhoPos _ (hNs.trans hStart))
      nlinarith
    exact hX.trans (hBase.trans hLog)

end Erdos993Lean.Analytic.V22.Analysis
