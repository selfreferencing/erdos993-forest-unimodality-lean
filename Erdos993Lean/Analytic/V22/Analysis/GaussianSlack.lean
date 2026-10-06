import Erdos993Lean.Analytic.V22.Analysis.ActivityOne
import Erdos993Lean.Analytic.V22.Analysis.LogShiftBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Paper v2.2, Lemma 3.12: the Gaussian slack

The positive and negative analytic lower bounds are proved without auxiliary
analytic hypotheses. The negative polynomial uses the source's installed
continuous extension at zero. The two finite source facts are kept explicit:
Lemma 7.2's exact `Q >= 0.0053` certificate and the two endpoint comparisons
used to include `[0.5996,1.605]`. They are propositions, not axioms; the finite
checker lane must supply their proofs before the conditional interval theorem
is consumed. This helper creates no forest or process data.
-/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set Finset

/-- Source: note Lemma 3.12, the positive-branch rational function. -/
noncomputable def gaussianPhi (s : ℝ) : ℝ :=
  (18 / 25 : ℝ) * (2 - s / 2) ^ 2 - 2 / (1 + s)

/-- The continuous polynomial extension of `Lambda(a)/a`, including `a=0`. -/
noncomputable def gaussianLambdaQuotient (a : ℝ) : ℝ :=
  2 + a / 2 + a ^ 2 / 3 + a ^ 3 / 4 + a ^ 4 / 5 + a ^ 5 / 6

/-- Source: note Lemma 3.12, the degree-six logarithmic lower polynomial. -/
noncomputable def gaussianLambda (a : ℝ) : ℝ :=
  2 * a + a ^ 2 / 2 + a ^ 3 / 3 + a ^ 4 / 4 + a ^ 5 / 5 + a ^ 6 / 6

/-- Source: note Lemmas 3.12 and 7.2, with its removable endpoint installed. -/
noncomputable def gaussianQ (a : ℝ) : ℝ :=
  (18 / 25 : ℝ) * gaussianLambdaQuotient a ^ 2 *
    (1 + gaussianLambda a ^ 2 / 75) * (1 - a) - 2

theorem gaussianLambda_eq_mul (a : ℝ) :
    gaussianLambda a = a * gaussianLambdaQuotient a := by
  unfold gaussianLambda gaussianLambdaQuotient
  ring

@[simp] theorem gaussianQ_zero : gaussianQ 0 = 22 / 25 := by
  norm_num [gaussianQ, gaussianLambda, gaussianLambdaQuotient]

/-- The exact finite source obligation from note Lemma 7.2; no margin is dropped. -/
def GaussianSlackQCertificate : Prop :=
  ∀ a ∈ Icc (0 : ℝ) (66 / 125), (53 / 10000 : ℝ) ≤ gaussianQ a

/-- The exact two endpoint comparisons used by the final sentence of Lemma 3.12. -/
def GaussianSlackEndpointCertificate : Prop :=
  activityOneCoordinate (-(66 / 125 : ℝ)) ≤ (1499 / 2500 : ℝ) ∧
    (321 / 200 : ℝ) ≤ activityOneCoordinate (67 / 100)

/-- The global hyperbolic bound used by the Gaussian slack proof. -/
theorem gaussian_sinh_sq_lower (y : ℝ) :
    y ^ 2 + y ^ 4 / 3 ≤ Real.sinh y ^ 2 := by
  have hs := Real.hasSum_cosh (2 * y)
  have h := hs.summable.sum_le_tsum (range 3) (fun n _ => by
    rw [pow_mul]
    exact div_nonneg (pow_nonneg (sq_nonneg _) _) (Nat.cast_nonneg _))
  rw [hs.tsum_eq] at h
  norm_num [sum_range_succ] at h
  rw [Real.cosh_two_mul, Real.cosh_sq] at h
  nlinarith

/-- The exact exponential form of the paper's `t(s)` coordinate. -/
theorem gaussian_coordinate_exp {s : ℝ} (hs : -1 < s) :
    activityOneCoordinate s = Real.exp ((2 / 5 : ℝ) * rootEquation s) := by
  unfold activityOneCoordinate
  rw [Real.rpow_def_of_pos (mul_pos (Real.exp_pos s) (by linarith)),
    Real.log_mul (Real.exp_pos s).ne' (by linarith : 1 + s ≠ 0), Real.log_exp]
  unfold rootEquation
  congr 1
  ring

/-- The coordinate correspondence is lossless on the stated positive domain. -/
theorem gaussian_coordinate_rootMap {t : ℝ} (ht : 0 < t) :
    activityOneCoordinate (rootMap (activityOneLambda_t t)) = t := by
  have hs := rootMap_gt_neg_one (activityOneLambda_t t)
  apply Real.log_injOn_pos (activityOneCoordinate_pos hs) ht
  have h := activityOneCoordinate_lambda hs
  rw [rootMap_equation] at h
  unfold activityOneLambda_t at h
  unfold activityOneLambda_t
  linarith

/-- Source: note Lemma 3.12, the exact hyperbolic identity. -/
theorem gaussian_coordinate_ratio {s : ℝ} (hs : -1 < s) :
    (activityOneCoordinate s - 1) ^ 2 / activityOneCoordinate s =
      4 * Real.sinh (rootEquation s / 5) ^ 2 := by
  rw [gaussian_coordinate_exp hs]
  have he : (2 / 5 : ℝ) * rootEquation s =
      rootEquation s / 5 + rootEquation s / 5 := by ring
  rw [he, Real.exp_add, Real.sinh_eq, Real.exp_neg]
  field_simp [Real.exp_ne_zero]
  ring

/-- The polynomial Gaussian lower bound before splitting the sign of the root. -/
theorem gaussianSlack_coordinate_lower {s : ℝ} (hs : -1 < s) :
    (18 / 25 : ℝ) * rootEquation s ^ 2 * (1 + rootEquation s ^ 2 / 75) -
        2 * s ^ 2 / (1 + s) ≤ activityOneS (activityOneCoordinate s) := by
  unfold activityOneS activityOneG0 rootG
  rw [activityOneCoordinate_root hs, gaussian_coordinate_ratio hs]
  have h := gaussian_sinh_sq_lower (rootEquation s / 5)
  have hscaled := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 18)
  convert sub_le_sub_right hscaled (2 * s ^ 2 / (1 + s)) using 1 <;> ring

/-- The elementary bound on the positive root equation. -/
theorem gaussian_rootEquation_lower {s : ℝ} (hs : 0 ≤ s) :
    2 * s - s ^ 2 / 2 ≤ rootEquation s := by
  have h := logShift_log_one_add_lower hs
  unfold rootEquation
  linarith

/-- The source's rational positive-branch nonnegativity, proved directly. -/
theorem gaussianPhi_nonneg {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 67 / 100) :
    0 ≤ gaussianPhi s := by
  have hden : 0 < 1 + s := by linarith
  have hs2 : s ^ 2 ≤ (67 / 100 : ℝ) * s := by
    nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs1)]
  have hs3 : 0 ≤ s ^ 3 := pow_nonneg hs0 3
  unfold gaussianPhi
  apply sub_nonneg.mpr
  apply (div_le_iff₀ hden).2
  nlinarith

/-- Source: note Lemma 3.12, the positive analytic branch with the exact `phi`. -/
theorem gaussianSlack_positive {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 67 / 100) :
    s ^ 2 * gaussianPhi s ≤ activityOneS (activityOneCoordinate s) ∧
      0 ≤ s ^ 2 * gaussianPhi s := by
  have hs : -1 < s := by linarith
  have hl := gaussian_rootEquation_lower hs0
  have hlow : 0 ≤ s * (2 - s / 2) := mul_nonneg hs0 (by linarith)
  have hloweq : 2 * s - s ^ 2 / 2 = s * (2 - s / 2) := by ring
  rw [hloweq] at hl
  have hr : 0 ≤ rootEquation s := hlow.trans hl
  have hsq : (s * (2 - s / 2)) ^ 2 ≤ rootEquation s ^ 2 :=
    (sq_le_sq₀ hlow hr).2 hl
  have hg := gaussianSlack_coordinate_lower hs
  constructor
  · have hbase : s ^ 2 * gaussianPhi s =
        (18 / 25 : ℝ) * (s * (2 - s / 2)) ^ 2 - 2 * s ^ 2 / (1 + s) := by
      unfold gaussianPhi
      ring
    have hboost : (18 / 25 : ℝ) * rootEquation s ^ 2 ≤
        (18 / 25 : ℝ) * rootEquation s ^ 2 * (1 + rootEquation s ^ 2 / 75) := by
      have hm := mul_le_mul_of_nonneg_left
        (show (1 : ℝ) ≤ 1 + rootEquation s ^ 2 / 75 by
          have hn : (0 : ℝ) ≤ rootEquation s ^ 2 / 75 := by positivity
          linarith)
        (show (0 : ℝ) ≤ (18 / 25 : ℝ) * rootEquation s ^ 2 by positivity)
      simpa only [mul_one] using hm
    rw [hbase]
    exact ((sub_le_sub_right (mul_le_mul_of_nonneg_left hsq
      (by norm_num : (0 : ℝ) ≤ 18 / 25)) _).trans
      (sub_le_sub_right hboost _)).trans hg
  · exact mul_nonneg (sq_nonneg s) (gaussianPhi_nonneg hs0 hs1)

/-- The degree-six lower truncation of the exact logarithm series. -/
theorem gaussianLambda_le_neg_rootEquation {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    gaussianLambda a ≤ -rootEquation (-a) := by
  have hseries := Real.hasSum_pow_div_log_of_abs_lt_one (x := a)
    (by simpa only [abs_of_nonneg ha0] using ha1)
  have h := hseries.summable.sum_le_tsum (range 6) (fun n _ => by positivity)
  rw [hseries.tsum_eq] at h
  norm_num [sum_range_succ] at h
  unfold gaussianLambda rootEquation
  rw [← sub_eq_add_neg]
  linarith

theorem gaussianLambda_nonneg {a : ℝ} (ha : 0 ≤ a) : 0 ≤ gaussianLambda a := by
  unfold gaussianLambda
  positivity

private theorem gaussian_boost_mono {x y : ℝ} (h : x ^ 2 ≤ y ^ 2) :
    (18 / 25 : ℝ) * x ^ 2 * (1 + x ^ 2 / 75) ≤
      (18 / 25 : ℝ) * y ^ 2 * (1 + y ^ 2 / 75) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (add_nonneg (sq_nonneg x) (sq_nonneg y))]

/-- The exact factorization using the installed polynomial extension, also at zero. -/
theorem gaussianQ_factorization {a : ℝ} (ha : a < 1) :
    (18 / 25 : ℝ) * gaussianLambda a ^ 2 * (1 + gaussianLambda a ^ 2 / 75) -
        2 * a ^ 2 / (1 - a) = a ^ 2 / (1 - a) * gaussianQ a := by
  have hlam : gaussianLambda a ^ 2 = a ^ 2 * gaussianLambdaQuotient a ^ 2 := by
    rw [gaussianLambda_eq_mul, mul_pow]
  unfold gaussianQ
  rw [hlam]
  field_simp [(sub_pos.mpr ha).ne'] <;> ring

/-- Source: note Lemma 3.12, the negative analytic branch with exact `Q`. -/
theorem gaussianSlack_negative_lower {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    a ^ 2 / (1 - a) * gaussianQ a ≤ activityOneS (activityOneCoordinate (-a)) := by
  have hl := gaussianLambda_le_neg_rootEquation ha0 ha1
  have hln := gaussianLambda_nonneg ha0
  have hrn : 0 ≤ -rootEquation (-a) := hln.trans hl
  have hsq : gaussianLambda a ^ 2 ≤ rootEquation (-a) ^ 2 := by
    simpa only [neg_sq] using (sq_le_sq₀ hln hrn).2 hl
  have hb := gaussian_boost_mono hsq
  have hg := gaussianSlack_coordinate_lower (s := -a) (by linarith)
  rw [← gaussianQ_factorization ha1]
  simp only [neg_sq, ← sub_eq_add_neg] at hg
  exact (sub_le_sub_right hb (2 * a ^ 2 / (1 - a))).trans hg

/-- Source: note Lemma 3.12's negative chain, using only exact Lemma 7.2. -/
theorem gaussianSlack_negative (hQ : GaussianSlackQCertificate) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 66 / 125) :
    a ^ 2 / (1 - a) * gaussianQ a ≤ activityOneS (activityOneCoordinate (-a)) ∧
      0 ≤ a ^ 2 / (1 - a) * gaussianQ a := by
  have ha : a < 1 := by linarith
  constructor
  · exact gaussianSlack_negative_lower ha0 ha
  · have hcert := hQ a ⟨ha0, ha1⟩
    exact mul_nonneg (div_nonneg (sq_nonneg a) (by linarith)) (by linarith)

/-- The source root-coordinate interval, with only its finite `Q` certificate. -/
theorem gaussianSlack_nonneg_coordinate (hQ : GaussianSlackQCertificate) {s : ℝ}
    (hs0 : -(66 / 125 : ℝ) ≤ s) (hs1 : s ≤ 67 / 100) :
    0 ≤ activityOneS (activityOneCoordinate s) := by
  by_cases hs : 0 ≤ s
  · exact (gaussianSlack_positive hs hs1).2.trans (gaussianSlack_positive hs hs1).1
  · have h := gaussianSlack_negative hQ (a := -s) (by linarith) (by linarith)
    simpa only [neg_neg] using h.2.trans h.1

/-- Source: note Lemma 3.12, the complete `t(s)` interval. -/
theorem gaussianSlack_nonneg_interval (hQ : GaussianSlackQCertificate) {t : ℝ}
    (ht0 : activityOneCoordinate (-(66 / 125 : ℝ)) ≤ t)
    (ht1 : t ≤ activityOneCoordinate (67 / 100)) : 0 ≤ activityOneS t := by
  have ht : 0 < t := (activityOneCoordinate_pos (s := -(66 / 125 : ℝ))
    (by norm_num)).trans_le ht0
  let s := rootMap (activityOneLambda_t t)
  have hs : -1 < s := rootMap_gt_neg_one _
  have hcoord : activityOneCoordinate s = t := gaussian_coordinate_rootMap ht
  have hsl : -(66 / 125 : ℝ) ≤ s := by
    by_contra! hlt
    have h := activityOneCoordinate_strictMonoOn hs (by norm_num) hlt
    rw [hcoord] at h
    linarith
  have hsu : s ≤ 67 / 100 := by
    by_contra! hlt
    have h := activityOneCoordinate_strictMonoOn (by norm_num) hs hlt
    rw [hcoord] at h
    linarith
  rw [← hcoord]
  exact gaussianSlack_nonneg_coordinate hQ hsl hsu

/-- Source: note Lemma 3.12, `[0.5996,1.605]`, with finite facts explicit. -/
theorem gaussianSlack_nonneg_source_range (hQ : GaussianSlackQCertificate)
    (hends : GaussianSlackEndpointCertificate) {t : ℝ}
    (ht0 : (1499 / 2500 : ℝ) ≤ t) (ht1 : t ≤ 321 / 200) : 0 ≤ activityOneS t :=
  gaussianSlack_nonneg_interval hQ (hends.1.trans ht0) (ht1.trans hends.2)

end Erdos993Lean.Analytic.V22.Analysis
