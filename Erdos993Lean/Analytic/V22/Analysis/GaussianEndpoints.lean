import Erdos993Lean.Analytic.V22.Analysis.GaussianSlack
import Mathlib.Analysis.Complex.Exponential

/-!
# Exact endpoints for paper v2.2, Lemma 3.12

The source interval `[0.5996,1.605]` is contained in the image of
`[-0.528,0.67]` under the exact root coordinate. The comparisons below use
finite rational lower sums for the exponential; they require no numerical
oracle or extra endpoint hypothesis. The resulting source-range theorem
retains only the exact finite `Q >= 0.0053` certificate from Lemma 7.2.

Drafting worker runs no Lean/lake process; the parent lane owns verification.
-/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Finset

/-- Raising the source coordinate to its fifth power eliminates the radical. -/
theorem gaussian_coordinate_pow_five {s : ℝ} (hs : -1 < s) :
    activityOneCoordinate s ^ 5 = Real.exp (2 * s) * (1 + s) ^ 2 := by
  have hp : 0 ≤ Real.exp s * (1 + s) :=
    (mul_pos (Real.exp_pos s) (by linarith)).le
  unfold activityOneCoordinate
  calc
    ((Real.exp s * (1 + s)) ^ (2 / 5 : ℝ)) ^ 5 =
        (Real.exp s * (1 + s)) ^ ((2 / 5 : ℝ) * (5 : ℕ)) :=
      (Real.rpow_mul_natCast hp (2 / 5) 5).symm
    _ = (Real.exp s * (1 + s)) ^ 2 := by norm_num
    _ = Real.exp (2 * s) * (1 + s) ^ 2 := by
      rw [mul_pow, ← Real.exp_nat_mul]
      norm_num

/-- The ten-term rational exponential lower sum at the lower endpoint. -/
theorem gaussian_lower_endpoint_scaled :
    (59 / 125 : ℝ) ^ 2 ≤ Real.exp (132 / 125) * (1499 / 2500 : ℝ) ^ 5 := by
  have he := Real.sum_le_exp_of_nonneg (x := (132 / 125 : ℝ)) (by norm_num) 10
  have hscaled := mul_le_mul_of_nonneg_right he
    (by norm_num : 0 ≤ (1499 / 2500 : ℝ) ^ 5)
  have hrat : (59 / 125 : ℝ) ^ 2 ≤
      (∑ i ∈ range 10, (132 / 125 : ℝ) ^ i / (Nat.factorial i : ℝ)) *
        (1499 / 2500 : ℝ) ^ 5 := by
    norm_num [Finset.sum_range_succ, Nat.factorial_succ]
  exact hrat.trans hscaled

/-- Exact lower endpoint containment: `t(-0.528) <= 0.5996`. -/
theorem gaussian_coordinate_lower_endpoint :
    activityOneCoordinate (-(66 / 125 : ℝ)) ≤ (1499 / 2500 : ℝ) := by
  apply (pow_le_pow_iff_left₀
    (activityOneCoordinate_pos (s := -(66 / 125 : ℝ)) (by norm_num)).le
    (by norm_num : 0 ≤ (1499 / 2500 : ℝ)) (by decide : (5 : ℕ) ≠ 0)).1
  rw [gaussian_coordinate_pow_five (by norm_num)]
  have htwo : 2 * (-(66 / 125 : ℝ)) = -(132 / 125 : ℝ) := by norm_num
  have hone : 1 + (-(66 / 125 : ℝ)) = (59 / 125 : ℝ) := by norm_num
  rw [htwo, hone, Real.exp_neg, ← div_eq_inv_mul]
  exact (div_le_iff₀ (Real.exp_pos (132 / 125))).2
    (by simpa only [mul_comm] using gaussian_lower_endpoint_scaled)

/-- The fourteen-term rational exponential lower sum at the upper endpoint. -/
theorem gaussian_upper_endpoint_scaled :
    (321 / 200 : ℝ) ^ 5 ≤ Real.exp (67 / 50) * (167 / 100 : ℝ) ^ 2 := by
  have he := Real.sum_le_exp_of_nonneg (x := (67 / 50 : ℝ)) (by norm_num) 14
  have hscaled := mul_le_mul_of_nonneg_right he
    (by norm_num : 0 ≤ (167 / 100 : ℝ) ^ 2)
  have hrat : (321 / 200 : ℝ) ^ 5 ≤
      (∑ i ∈ range 14, (67 / 50 : ℝ) ^ i / (Nat.factorial i : ℝ)) *
        (167 / 100 : ℝ) ^ 2 := by
    norm_num [Finset.sum_range_succ, Nat.factorial_succ]
  exact hrat.trans hscaled

/-- Exact upper endpoint containment: `1.605 <= t(0.67)`. -/
theorem gaussian_coordinate_upper_endpoint :
    (321 / 200 : ℝ) ≤ activityOneCoordinate (67 / 100) := by
  apply (pow_le_pow_iff_left₀ (by norm_num : 0 ≤ (321 / 200 : ℝ))
    (activityOneCoordinate_pos (s := (67 / 100 : ℝ)) (by norm_num)).le
    (by decide : (5 : ℕ) ≠ 0)).1
  rw [gaussian_coordinate_pow_five (by norm_num)]
  have htwo : 2 * (67 / 100 : ℝ) = (67 / 50 : ℝ) := by norm_num
  have hone : 1 + (67 / 100 : ℝ) = (167 / 100 : ℝ) := by norm_num
  rw [htwo, hone]
  exact gaussian_upper_endpoint_scaled

/-- Both source endpoint facts are proved and can be supplied to the frozen core. -/
theorem gaussianSlack_endpoint_certificate : GaussianSlackEndpointCertificate :=
  ⟨gaussian_coordinate_lower_endpoint, gaussian_coordinate_upper_endpoint⟩

/-- Paper Lemma 3.12 on `[0.5996,1.605]`, requiring only exact Lemma 7.2. -/
theorem gaussianSlack_nonneg_source_range_of_Q (hQ : GaussianSlackQCertificate)
    {t : ℝ} (ht0 : (1499 / 2500 : ℝ) ≤ t) (ht1 : t ≤ 321 / 200) :
    0 ≤ activityOneS t :=
  gaussianSlack_nonneg_source_range hQ gaussianSlack_endpoint_certificate ht0 ht1

end Erdos993Lean.Analytic.V22.Analysis
