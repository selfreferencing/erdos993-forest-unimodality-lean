import Erdos993Lean.Analytic.V22.Analysis.CoefficientMonotonicity
import Erdos993Lean.Analytic.V22.Checks.EarlyStatements
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The source A3 denominator monotonicity consumer

Source: Lemma 7.4 and the proof of Theorem 5.6. The finite statement
supplies a positive derivative floor through the exact cap N=576 and
monotonicity on the tail. Continuity and the interval join are proved
here, so the consumer uses only Lemma 7.4.
-/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

private theorem cappedBeta_continuousAt {N rm : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ rm) (hrh : rm ≤ 1 / 2) :
    ContinuousAt (V22.Checks.cappedBeta rm) N := by
  have hn : 0 < N := by linarith
  have hn1 : 0 < N + 1 := by linarith
  have hd := coefficient_one_sub_rm_sq_pos hr0 hrh
  have hc : 0 < V22.cCoef N := by linarith [(coefficient_cCoef_bounds hN).1]
  have hcdirect : 0 < 1 - 1 / N := by simpa only [V22.cCoef] using hc
  have hsdirect := Real.sqrt_pos.2 hcdirect
  have hrs := coefficient_rhoStar_pos hN hr0 hrh
  have hRho : ContinuousAt (fun n => V22.rhoStar n rm) N := by
    unfold V22.rhoStar V22.rho V22.cCoef
    fun_prop (disch := positivity)
  have hE : ContinuousAt (fun n => V22.E2 n rm (min 6 (rm * Real.sqrt n))) N := by
    unfold V22.E2 V22.e2 V22.e3 V22.e4 V22.e5
    fun_prop (disch := positivity)
  unfold V22.Checks.cappedBeta V22.betaE
  exact (continuousAt_id.sub continuousAt_const).sub
    ((continuousAt_const.div hRho hrs.ne').mul hE)

/-- The complete A3 monotonicity on its source all-N domain. -/
theorem cappedBeta_quarter_monotone (h4 : V22.Checks.lemma_7_4) :
    MonotoneOn (V22.Checks.cappedBeta (1 / 4)) (Ici (67 / 5)) := by
  have hcap : ((6 : ℝ) / (1 / 4)) ^ 2 = 576 := by norm_num
  have hcont : ContinuousOn (V22.Checks.cappedBeta (1 / 4)) (Icc (67 / 5) 576) := by
    intro n hn
    exact (cappedBeta_continuousAt (by linarith [hn.1]) (by norm_num) (by norm_num)).continuousWithinAt
  have hderiv (n : ℝ) (hn : n ∈ interior (Icc (67 / 5) 576)) :
      0 < deriv (V22.Checks.cappedBeta (1 / 4)) n := by
    have hi : 67 / 5 < n ∧ n < 576 := by
      simpa only [interior_Icc, mem_Ioo] using hn
    have hd := h4.2.1 n ⟨hi.1.le, hi.2.le⟩
    unfold V22.Checks.betaDerivativeOn at hd
    rw [hcap, derivWithin_of_mem_nhds (Icc_mem_nhds hi.1 hi.2)] at hd
    have hfloor : 0 < V22.Checks.betaDerivativeBound (1 / 4) (67 / 5) := by
      linarith [h4.1]
    exact hfloor.trans_le hd
  have hpre : MonotoneOn (V22.Checks.cappedBeta (1 / 4)) (Icc (67 / 5) 576) :=
    monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcont
      (fun n hn => (differentiableAt_of_deriv_ne_zero (hderiv n hn).ne').differentiableWithinAt)
      (fun n hn => (hderiv n hn).le)
  intro a ha b hb hab
  by_cases hbcap : b ≤ 576
  · exact hpre ⟨ha, hab.trans hbcap⟩ ⟨hb, hbcap⟩ hab
  · by_cases hacap : a ≤ 576
    · exact (hpre ⟨ha, hacap⟩ ⟨by norm_num, le_rfl⟩ hacap).trans
        (h4.2.2 (by simp) (by simpa using le_of_not_ge hbcap) (le_of_not_ge hbcap))
    · exact h4.2.2 (by simpa using le_of_not_ge hacap)
        (by simpa using le_of_not_ge hbcap) hab

end Erdos993Lean.Analytic.V22.Analysis
