import Erdos993Lean.Analytic.V22.Analysis.RootGTaylor

/-!
# Algebra preserving the two copies of the upper-range bonus

Source: the exact split in note Lemma 4.7(b). This is the algebraic helper
consumed after the actual upper minorant and activity-one bound have been
installed. Its inputs explicitly name those bounds; it is not a substitute
for the source fiber theorem. Both signed bonus terms survive the split.
-/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real

/-- Exact upper-range split, before replacing either loss by a positive part. -/
theorem upper_bonus_payment {N rho rhoU Delta e lambdaT lambdaU T C Fpsi : ℝ}
    (hN : 0 < N) (hrho : 0 < rho) (hrhoU : 0 < rhoU) (hDelta : 0 ≤ Delta)
    (hlambda : lambdaU = lambdaT + (rhoU / 2 * Delta - e)) (hneg : lambdaU < 0)
    (hbase : T ≤ N * (1 - 2 / rho * rootG lambdaT) - C)
    (hminorant : N * (1 + Delta - 2 / rhoU * rootG lambdaU) - C ≤ Fpsi) :
    T - 2 * N * (1 / rhoU - 1 / rho) * rootG lambdaT + N * Delta -
      |rootGPrime lambdaU| * (2 * N / rhoU * e - N * Delta) ≤ Fpsi := by
  have hsigma : rootGPrime lambdaU ≤ 0 := rootGPrime_nonpos hneg.le
  have ht := rootG_bonus_split lambdaT Delta (-e) rhoU hrhoU hDelta
  dsimp only at ht
  have he : lambdaT + (rhoU / 2 * Delta + -e) = lambdaU := by
    rw [hlambda]
    ring
  rw [he] at ht
  have hscaled := mul_le_mul_of_nonneg_left ht hN.le
  have hsplit :
      N * (1 - 2 / rhoU * rootG lambdaT +
        Delta * (1 - rootGPrime lambdaU) - 2 / rhoU * (-e) * rootGPrime lambdaU) =
      N * (1 - 2 / rho * rootG lambdaT) -
        2 * N * (1 / rhoU - 1 / rho) * rootG lambdaT + N * Delta -
        |rootGPrime lambdaU| * (2 * N / rhoU * e - N * Delta) := by
    rw [abs_of_nonpos hsigma]
    field_simp [hrho.ne', hrhoU.ne']
    ring
  rw [hsplit] at hscaled
  linarith

/-- The same-factor second payment is preserved when losses are truncated. -/
theorem upper_bonus_positive_parts {N rho rhoU Delta e lambdaT lambdaU T C Fpsi : ℝ}
    (hN : 0 < N) (hrho : 0 < rho) (hrhoU : 0 < rhoU) (hDelta : 0 ≤ Delta)
    (hlambda : lambdaU = lambdaT + (rhoU / 2 * Delta - e)) (hneg : lambdaU < 0)
    (hbase : T ≤ N * (1 - 2 / rho * rootG lambdaT) - C)
    (hminorant : N * (1 + Delta - 2 / rhoU * rootG lambdaU) - C ≤ Fpsi) :
    T - (max (2 * N * (1 / rhoU - 1 / rho) * rootG lambdaT - N * Delta) 0 +
      |rootGPrime lambdaU| * max (2 * N / rhoU * e - N * Delta) 0) ≤ Fpsi := by
  have hp := upper_bonus_payment hN hrho hrhoU hDelta hlambda hneg hbase hminorant
  have hA := le_max_left
    (2 * N * (1 / rhoU - 1 / rho) * rootG lambdaT - N * Delta) (0 : ℝ)
  have hB := mul_le_mul_of_nonneg_left
    (le_max_left (2 * N / rhoU * e - N * Delta) (0 : ℝ)) (abs_nonneg (rootGPrime lambdaU))
  linarith

end Erdos993Lean.Analytic.V22.Analysis
