import Erdos993Lean.Analytic.V22.Analysis.Kernel
import Mathlib.Tactic

/-!
# Note Proposition 2.1: averaging with the shifted penalty

The actual integer-indexed fiber hypothesis is retained. The consumer is
`NoValleyAtMGF2`; there is no inference reconstructing a forest from scalars.
-/

namespace Erdos993Lean.Analytic.V22.Analysis

open Erdos993Lean.Analytic.NoValley

noncomputable def fiberScale (q mu : ℝ) : ℝ :=
  4 * variance q ^ 2 * gaussianA / sigma q mu ^ 3

theorem gaussianA_pos : 0 < gaussianA := by
  unfold gaussianA
  positivity

theorem sigma_pos {q mu : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hmu : 0 < mu) :
    0 < sigma q mu := by
  unfold sigma variance
  exact Real.sqrt_pos.2 (mul_pos (mul_pos hq0 (sub_pos.mpr hq1)) hmu)

theorem fiberScale_pos {q mu : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hmu : 0 < mu) :
    0 < fiberScale q mu := by
  have hs := sigma_pos hq0 hq1 hmu
  have ha := gaussianA_pos
  have hv : 0 < variance q := mul_pos hq0 (sub_pos.mpr hq1)
  unfold fiberScale
  positivity

theorem fiberScale_mul_fiber {q mu : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hmu : 0 < mu) (M : ℕ) (j : ℤ) :
    fiberScale q mu * fiber q mu M j = weightedKernel q M j +
      (fiberScale q mu / sigma q mu ^ 2) * offset q M j ^ 2 := by
  have hs := (sigma_pos hq0 hq1 hmu).ne'
  have ha := gaussianA_pos.ne'
  have hv : variance q ≠ 0 := (mul_pos hq0 (sub_pos.mpr hq1)).ne'
  unfold fiberScale fiber
  field_simp

/-- Source Proposition 2.1, condition (P), with its exact displayed prices. -/
theorem averaging_pointwise {q mu alpha beta Gamma Z : ℝ}
    (hqa : 1 / 4 ≤ q) (hqb : q ≤ 3 / 4) (hmu : 0 < mu)
    (hf : ∀ (M : ℕ) (j : ℤ), alpha + beta * ((M : ℝ) / mu - 1) -
      Gamma * ((M : ℝ) / mu - 1) ^ 2 - Z * (1 - q) ^ M ≤ fiber q mu M j)
    (M : ℕ) (j : ℤ) :
    fiberScale q mu * (alpha - signedR q ^ 2 / (4 * sigma q mu ^ 2)) +
        (fiberScale q mu * beta / mu) * ((M : ℝ) - mu) -
        (fiberScale q mu * Gamma / mu ^ 2) * ((M : ℝ) - mu) ^ 2 -
        (fiberScale q mu * Z) * (1 - q) ^ M ≤
      kernel2 q (weightL q) (weightR q) M j -
        (signedR q * (fiberScale q mu / sigma q mu ^ 2)) * ((j : ℝ) - q * M) +
        (fiberScale q mu / sigma q mu ^ 2) * ((j : ℝ) - q * M) ^ 2 := by
  have hq0 : 0 < q := by linarith
  have hq1 : q < 1 := by linarith
  have h := mul_le_mul_of_nonneg_left (hf M j) (fiberScale_pos hq0 hq1 hmu).le
  rw [fiberScale_mul_fiber hq0 hq1 hmu] at h
  have hs := (sigma_pos hq0 hq1 hmu).ne'
  have heq :
      kernel2 q (weightL q) (weightR q) M j -
        (signedR q * (fiberScale q mu / sigma q mu ^ 2)) * ((j : ℝ) - q * M) +
        (fiberScale q mu / sigma q mu ^ 2) * ((j : ℝ) - q * M) ^ 2 -
        (fiberScale q mu * (alpha - signedR q ^ 2 / (4 * sigma q mu ^ 2)) +
          (fiberScale q mu * beta / mu) * ((M : ℝ) - mu) -
          (fiberScale q mu * Gamma / mu ^ 2) * ((M : ℝ) - mu) ^ 2 -
          (fiberScale q mu * Z) * (1 - q) ^ M) =
      weightedKernel q M j + (fiberScale q mu / sigma q mu ^ 2) * offset q M j ^ 2 -
        fiberScale q mu * (alpha + beta * ((M : ℝ) / mu - 1) -
          Gamma * ((M : ℝ) / mu - 1) ^ 2 - Z * (1 - q) ^ M) := by
    unfold weightedKernel offset
    field_simp [hs, hmu.ne']
    ring
  linarith

/-- Source Proposition 2.1, the exact if-and-only-if averaging margin. -/
theorem averaging_margin_iff {q mu alpha theta Gamma D Z ell : ℝ}
    (hqa : 1 / 4 ≤ q) (hqb : q ≤ 3 / 4) (hmu : 0 < mu) :
    (fiberScale q mu / sigma q mu ^ 2) * theta * variance q * mu <
      fiberScale q mu * (alpha - signedR q ^ 2 / (4 * sigma q mu ^ 2)) -
        (fiberScale q mu * Gamma / mu ^ 2) * D * mu -
        (fiberScale q mu * Z) * Real.exp (-ell * mu) ↔
    0 < alpha - theta - Gamma * D / mu -
      signedR q ^ 2 / ((1 - signedR q ^ 2) * mu) - Z * Real.exp (-ell * mu) := by
  have hq0 : 0 < q := by linarith
  have hq1 : q < 1 := by linarith
  have hC := fiberScale_pos hq0 hq1 hmu
  have hv : 0 < variance q := mul_pos hq0 (sub_pos.mpr hq1)
  have hs : sigma q mu ^ 2 = variance q * mu := Real.sq_sqrt (by positivity)
  have heq :
      fiberScale q mu * (alpha - signedR q ^ 2 / (4 * sigma q mu ^ 2)) -
        (fiberScale q mu * Gamma / mu ^ 2) * D * mu -
        (fiberScale q mu * Z) * Real.exp (-ell * mu) -
        (fiberScale q mu / sigma q mu ^ 2) * theta * variance q * mu =
      fiberScale q mu * (alpha - theta - Gamma * D / mu -
        signedR q ^ 2 / ((1 - signedR q ^ 2) * mu) - Z * Real.exp (-ell * mu)) := by
    rw [hs, one_sub_signedR_sq]
    field_simp [hv.ne', hmu.ne']
    ring
  rw [← sub_pos, heq]
  exact mul_pos_iff_of_pos_left hC

/-- Source Proposition 2.1: the shifted fiber bound and its margin supply
the paper's existing two-sided MGF certificate. -/
theorem averaging_explicit_threshold {q mu alpha beta Gamma Z theta D ell : ℝ}
    (hqa : 1 / 4 ≤ q) (hqb : q ≤ 3 / 4) (hmu : 0 < mu)
    (hGamma : 0 ≤ Gamma) (hZ : 0 ≤ Z)
    (hf : ∀ (M : ℕ) (j : ℤ), alpha + beta * ((M : ℝ) / mu - 1) -
      Gamma * ((M : ℝ) / mu - 1) ^ 2 - Z * (1 - q) ^ M ≤ fiber q mu M j)
    (hm : 0 < alpha - theta - Gamma * D / mu -
      signedR q ^ 2 / ((1 - signedR q ^ 2) * mu) - Z * Real.exp (-ell * mu)) :
    ExplicitThresholdMGF2 q mu theta D [(1 - q, Real.exp (-ell * mu))] := by
  have hq0 : 0 < q := by linarith
  have hq1 : q < 1 := by linarith
  have hC := fiberScale_pos hq0 hq1 hmu
  have hs := sigma_pos hq0 hq1 hmu
  refine ⟨fiberScale q mu / sigma q mu ^ 2,
    -signedR q * (fiberScale q mu / sigma q mu ^ 2),
    fiberScale q mu * (alpha - signedR q ^ 2 / (4 * sigma q mu ^ 2)),
    fiberScale q mu * beta / mu, fiberScale q mu * Gamma / mu ^ 2,
    weightL q, weightR q, [fiberScale q mu * Z], by positivity, by positivity,
    (weights_nonneg hqa hqb).1, (weights_nonneg hqa hqb).2, ?_, ?_, ?_⟩
  · simp only [List.mem_singleton]
    rintro z rfl
    positivity
  · intro M j
    simpa [neg_mul, sub_eq_add_neg, pricedTail] using averaging_pointwise hqa hqb hmu hf M j
  · simpa [variance, pricedMargin] using (averaging_margin_iff hqa hqb hmu).2 hm

/-- Source Proposition 2.1, its final no-valley conclusion. -/
theorem averaging_noValley {q mu alpha beta Gamma Z theta D ell : ℝ}
    (hqa : 1 / 4 ≤ q) (hqb : q ≤ 3 / 4) (hmu : 0 < mu)
    (hGamma : 0 ≤ Gamma) (hZ : 0 ≤ Z)
    (hf : ∀ (M : ℕ) (j : ℤ), alpha + beta * ((M : ℝ) / mu - 1) -
      Gamma * ((M : ℝ) / mu - 1) ^ 2 - Z * (1 - q) ^ M ≤ fiber q mu M j)
    (hm : 0 < alpha - theta - Gamma * D / mu -
      signedR q ^ 2 / ((1 - signedR q ^ 2) * mu) - Z * Real.exp (-ell * mu)) :
    NoValleyAtMGF2 q mu theta D [(1 - q, Real.exp (-ell * mu))] := by
  apply noValleyAtMGF2_of_explicit (by linarith) (by linarith)
  exact averaging_explicit_threshold hqa hqb hmu hGamma hZ hf hm

end Erdos993Lean.Analytic.V22.Analysis
