import Erdos993Lean.Analytic.V22.Analysis.ActivityOne

/-! Source: Proposition 4.5(M), Proposition 4.6's middle range and the
nonnegative lower-sign ranges in Lemma 4.14. Every integer offset is retained.
The proofs use the exact weighted kernel identity, with no shape premise. -/

namespace Erdos993Lean.Analytic.V22.Analysis

open Erdos993Lean.Analytic.NoValley

theorem bonus_ge_one {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (M : ℕ) :
    1 ≤ bonus q M := by
  have hqb : 0 < 1 - q := sub_pos.mpr hq1
  have hden : 0 < (1 - signedR q ^ 2) * ((M : ℝ) + 2) := by
    rw [one_sub_signedR_sq]
    unfold variance
    positivity
  unfold bonus
  apply (le_div_iff₀ hden).2
  nlinarith [sq_nonneg (signedR q), sq_nonneg ((M : ℝ) + 1),
    mul_nonneg (sq_nonneg (signedR q)) (sq_nonneg ((M : ℝ) + 1))]

theorem squareOffset_nonneg {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (M : ℕ) (j : ℤ) : 0 ≤ squareOffset q M j := by
  have hqb : 0 < 1 - q := sub_pos.mpr hq1
  unfold squareOffset variance
  exact div_nonneg (sq_nonneg _) (by positivity)

theorem fiber_ge_penalty_below_bonus {q mu : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hmu : 0 < mu) (M : ℕ) (j : ℤ)
    (hw : squareOffset q M j ≤ bonus q M) :
    (((M : ℝ) + 2) / mu) * squareOffset q M j ≤ fiber q mu M j := by
  rw [fiber_eq hq0 hq1 hmu]
  have hbin := binom_nonneg hq0.le hq1.le (M := M + 2) (j + 1)
  have hden : 0 < 2 * gaussianA * ((M : ℝ) + 1) := by
    have := shapeGaussianA_pos
    positivity
  have hp : 0 ≤ mu ^ (3 / 2 : ℝ) * Real.sqrt (1 - signedR q ^ 2) *
      binom (M + 2) q (j + 1) / (2 * gaussianA * ((M : ℝ) + 1)) := by
    exact div_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hmu.le _)
      (Real.sqrt_nonneg _)) hbin) hden.le
  have hn := mul_nonneg hp (sub_nonneg.mpr hw)
  linarith

theorem fiber_nonneg_below_bonus {q mu : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hmu : 0 < mu) (M : ℕ) (j : ℤ)
    (hw : squareOffset q M j ≤ bonus q M) : 0 ≤ fiber q mu M j := by
  exact (mul_nonneg (by positivity) (squareOffset_nonneg hq0 hq1 M j)).trans
    (fiber_ge_penalty_below_bonus hq0 hq1 hmu M j hw)

/-- Source Proposition 4.5(M): both displayed comparisons. -/
theorem fiber_middle_lower {q mu : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hmu : 0 < mu) (M : ℕ) (j : ℤ)
    (hw0 : 1 ≤ squareOffset q M j) (hw1 : squareOffset q M j ≤ bonus q M) :
    (((M : ℝ) + 2) / mu) * squareOffset q M j ≤ fiber q mu M j ∧
      ((M : ℝ) + 2) / mu ≤ fiber q mu M j := by
  have h := fiber_ge_penalty_below_bonus hq0 hq1 hmu M j hw1
  refine ⟨h, le_trans ?_ h⟩
  simpa using mul_le_mul_of_nonneg_left hw0 (show 0 ≤ ((M : ℝ) + 2) / mu by positivity)

/-- Source Proposition 4.6: the middle range retains the exact margin `2`. -/
theorem scaled_fiber_middle_margin {q mu : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hmu : 0 < mu) (M : ℕ) (j : ℤ)
    (hw0 : 1 ≤ squareOffset q M j) (hw1 : squareOffset q M j ≤ bonus q M) :
    (2 : ℝ) ≤ mu * (fiber q mu M j - activityOnePsi ((M : ℝ) / mu)) := by
  have h := mul_le_mul_of_nonneg_left
    (fiber_middle_lower hq0 hq1 hmu M j hw0 hw1).2 hmu.le
  have heq : mu * (((M : ℝ) + 2) / mu - activityOnePsi ((M : ℝ) / mu)) =
      2 + (9 / 2 : ℝ) * mu * ((M : ℝ) / mu - 1) ^ 2 := by
    unfold activityOnePsi
    field_simp [hmu.ne']
    ring
  have hn : 0 ≤ (9 / 2 : ℝ) * mu * ((M : ℝ) / mu - 1) ^ 2 := by positivity
  nlinarith

end Erdos993Lean.Analytic.V22.Analysis
