import Erdos993Lean.Analytic.V22.Analysis.ThreeRanges
import Erdos993Lean.Analytic.V22.Analysis.LowerBonusAlgebra
import Erdos993Lean.Analytic.V22.Analysis.UpperBonusAlgebra
import Erdos993Lean.Analytic.V22.Analysis.SharedActivity
import Erdos993Lean.Analytic.V22.Analysis.LinearizedBounds

/-!
# Native lower and upper range minima with both bonus payments

Source: frozen `SOURCE_V5_note.tex`, Proposition 4.6 and Lemma 4.7.
The parameter `t` is the actual `M/mu`, the trial count is `N=M+2`, and
every final fiber comparison retains the integer `j`. The upper coefficient
is proved positive on the original domain using the pointwise coefficient
bounds; it is not an extra premise. Universal comparisons with the real
minorant encode the source's range minima before they are consumed by the
actual fiber. Parent owns compilation; this subagent runs no Lean or lake.
-/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

/-- The exact `D_L` in Proposition 4.6. -/
noncomputable def bonusRangeDL (r mu : ℝ) (M : ℕ) : ℝ :=
  max (2 * ((M : ℝ) + 3) * V22.eL r ((M : ℝ) + 2) *
      max (rootMap (activityOneLambda M mu .L + V22.eL r ((M : ℝ) + 2))) 0 -
    ((M : ℝ) + 2) * V22.Delta r ((M : ℝ) + 2) * (1 - V22.eL r ((M : ℝ) + 2))) 0

/-- The exact `D_U'`, preserving both independent positive-part payments. -/
noncomputable def bonusRangeDUPrime (r mu : ℝ) (M : ℕ) : ℝ :=
  max (2 * ((M : ℝ) + 2) *
      (1 / V22.rhoU r ((M : ℝ) + 2) - 1 / V22.rho ((M : ℝ) + 2)) *
      rootG (activityOneLambda M mu .U) - ((M : ℝ) + 2) * V22.Delta r ((M : ℝ) + 2)) 0 +
    |rootGPrime (threeRangeLambdaU r mu M)| *
      max (2 * ((M : ℝ) + 2) / V22.rhoU r ((M : ℝ) + 2) * V22.eU r ((M : ℝ) + 2) -
        ((M : ℝ) + 2) * V22.Delta r ((M : ℝ) + 2)) 0

/-- Source remainder in exactly the shared root and positive-part functions. -/
noncomputable def sharedLowerRemainder (r mu : ℝ) (M : ℕ) : ℝ :=
  V22.positivePart (2 * ((M : ℝ) + 3) * V22.eL r ((M : ℝ) + 2) *
      V22.positivePart (V22.rootMap (shapeTemplateLambda mu ((M : ℝ) + 2)
        (symmetricLowerPrefactor (M + 2)) + V22.eL r ((M : ℝ) + 2))) -
    ((M : ℝ) + 2) * V22.Delta r ((M : ℝ) + 2) * (1 - V22.eL r ((M : ℝ) + 2)))

noncomputable def sharedUpperRemainderPrime (r mu : ℝ) (M : ℕ) : ℝ :=
  V22.positivePart (2 * ((M : ℝ) + 2) *
      (1 / V22.rhoU r ((M : ℝ) + 2) - 1 / V22.rho ((M : ℝ) + 2)) *
      V22.G (shapeTemplateLambda mu ((M : ℝ) + 2) (symmetricUpperPrefactor (M + 2))) -
    ((M : ℝ) + 2) * V22.Delta r ((M : ℝ) + 2)) +
    |V22.G1 (threeRangeLambdaU r mu M)| *
      V22.positivePart (2 * ((M : ℝ) + 2) / V22.rhoU r ((M : ℝ) + 2) *
        V22.eU r ((M : ℝ) + 2) - ((M : ℝ) + 2) * V22.Delta r ((M : ℝ) + 2))

theorem sharedLowerRemainder_eq (r mu : ℝ) (M : ℕ) :
    sharedLowerRemainder r mu M = bonusRangeDL r mu M := by
  simp only [sharedLowerRemainder, bonusRangeDL, V22.positivePart,
    shared_rootMap_eq, activityOneLambda, activityOnePrefactor]

theorem sharedUpperRemainderPrime_eq (r mu : ℝ) (M : ℕ) :
    sharedUpperRemainderPrime r mu M = bonusRangeDUPrime r mu M := by
  simp only [sharedUpperRemainderPrime, bonusRangeDUPrime, V22.positivePart,
    shared_G_eq, shared_G1_eq, activityOneLambda, activityOnePrefactor]

theorem bonusRangeDL_nonneg (r mu : ℝ) (M : ℕ) : 0 ≤ bonusRangeDL r mu M :=
  le_max_right _ _

theorem bonusRangeDUPrime_nonneg (r mu : ℝ) (M : ℕ) : 0 ≤ bonusRangeDUPrime r mu M := by
  exact add_nonneg (le_max_right _ _) (mul_nonneg (abs_nonneg _) (le_max_right _ _))

/-- Automatic positivity on the full domain of Lemma 4.7. -/
theorem bonusRange_rhoU_pos {r N : ℝ} (hN : 10 ≤ N) (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) :
    0 < V22.rhoU r N := by
  have hs := linearized_rhoStar_lower hN hr0 hrh
  have hu := linearized_rhoU_lower hN hr0 (le_rfl : r ≤ r) hrh
  linarith

theorem bonusRange_eL_nonneg {r N : ℝ} (hN : 0 < N) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    0 ≤ V22.eL r N := by
  have hv := shared_varianceR_pos hr0 hr1
  have hc : 0 ≤ V22.c0 r N := by
    unfold V22.c0
    positivity
  have hp : 0 ≤ V22.positivePart (V22.quarticError r N 1 - V22.quarticErrorZero N) :=
    le_max_right _ _
  have he := shared_epsilon_nonneg hr0 hr1 hN
  unfold V22.eL
  linarith

private theorem bonusRange_base_margin {mu : ℝ} (hmu : 0 < mu) (M : ℕ) :
    2 ≤ (M : ℝ) + 2 - mu * activityOnePsi ((M : ℝ) / mu) := by
  have heq : (M : ℝ) + 2 - mu * activityOnePsi ((M : ℝ) / mu) =
      2 + (9 / 2 : ℝ) * mu * ((M : ℝ) / mu - 1) ^ 2 := by
    unfold activityOnePsi
    field_simp [hmu.ne']; ring
  rw [heq]
  have hnonneg : 0 ≤ (9 / 2 : ℝ) * mu * ((M : ℝ) / mu - 1) ^ 2 := by positivity
  linarith

private theorem bonusRange_mulB {mu : ℝ} (hmu : 0 < mu) (M : ℕ) :
    mu * (((M : ℝ) + 2) / mu) = (M : ℝ) + 2 := by
  field_simp [hmu.ne']

/-- A faithful real-minorant form of the nonpositive lower log branch. -/
theorem bonusRange_lower_nonpos {P B rho gamma : ℝ} (hP : 0 < P) (hB : 0 < B)
    (hrho : 0 < rho) (hgamma : 1 ≤ gamma)
    (hl : Real.log (B * Real.exp (rho * gamma / 2) / P) ≤ 0) (w : ℝ) (hw : w ≤ 1) :
    B ≤ rootMinorant P B rho gamma w := by
  let lambda := Real.log (B * Real.exp (rho * gamma / 2) / P)
  have hs : rootMap lambda ≤ 0 := by simpa using rootMap_monotone hl
  have harg : gamma ≤ rootMinorantArgmin rho gamma (rootMap lambda) := by
    unfold rootMinorantArgmin
    have hd : 2 * rootMap lambda / rho ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hrho.le
    linarith
  have hm := (rootMinorant_monotonicity_of_root hP hB hrho
    (rootMap_gt_neg_one lambda) (rootMap_equation lambda)).1
  have hcomp := hm (show w ∈ Iic (rootMinorantArgmin rho gamma (rootMap lambda)) by
      exact hw.trans (hgamma.trans harg))
    (show 1 ∈ Iic (rootMinorantArgmin rho gamma (rootMap lambda)) by exact hgamma.trans harg) hw
  have h1 : B ≤ rootMinorant P B rho gamma 1 := by
    unfold rootMinorant
    simp only [mul_one]
    have hp := mul_nonneg (mul_nonneg hP.le (sub_nonneg.mpr hgamma))
      (Real.exp_pos (-rho / 2)).le
    nlinarith
  exact h1.trans hcomp

/-- A faithful real-minorant form of Lemma 4.7(a)'s range minimum. -/
theorem bonusRange_upper_nonneg {P B rho gamma : ℝ} (hP : 0 < P) (hB : 0 < B)
    (hrho : 0 < rho) (hgamma : 1 ≤ gamma)
    (hl : 0 ≤ Real.log (B * Real.exp (rho * gamma / 2) / P))
    (w : ℝ) (hw : gamma ≤ w) : B * gamma ≤ rootMinorant P B rho gamma w := by
  let lambda := Real.log (B * Real.exp (rho * gamma / 2) / P)
  have hs : 0 ≤ rootMap lambda := (rootMap_nonneg_le hl).1
  have harg : rootMinorantArgmin rho gamma (rootMap lambda) ≤ gamma := by
    unfold rootMinorantArgmin
    have hd : 0 ≤ 2 * rootMap lambda / rho := by positivity
    linarith only [hd, hgamma]
  have hm := (rootMinorant_monotonicity_of_root hP hB hrho
    (rootMap_gt_neg_one lambda) (rootMap_equation lambda)).2
  have hcomp := hm (show gamma ∈ Ici (rootMinorantArgmin rho gamma (rootMap lambda)) by exact harg)
    (show w ∈ Ici (rootMinorantArgmin rho gamma (rootMap lambda)) by exact harg.trans hw) hw
  simpa only [rootMinorant, sub_self, mul_zero, zero_mul, zero_add] using hcomp

private theorem bonusRange_activity_base {M : ℕ} (hN : 10 ≤ M + 2)
    {mu : ℝ} (hmu : 0 < mu) (side : ActivityOneSide) :
    activityOneT ((M : ℝ) / mu) (M : ℝ) ≤
      ((M : ℝ) + 2) * (1 - 2 / V22.rho ((M : ℝ) + 2) * rootG (activityOneLambda M mu side)) -
        mu * activityOnePsi ((M : ℝ) / mu) := by
  have h := (activityOne_bound M mu side (by omega : 8 ≤ M) hmu).2
  have hN0 : (M : ℝ) + 2 ≠ 0 := ne_of_gt (by positivity)
  convert h using 1
  unfold V22.rho
  field_simp [hmu.ne', hN0] <;> ring

private theorem bonusRange_scaled_minimum {M : ℕ} {mu P rho gamma : ℝ}
    (hmu : 0 < mu) (hP : 0 < P) (hrho : 0 < rho) (w : ℝ) :
    ((M : ℝ) + 2) * (gamma - 2 / rho *
      rootG (Real.log ((((M : ℝ) + 2) / mu) * Real.exp (rho * gamma / 2) / P))) -
        mu * activityOnePsi ((M : ℝ) / mu) ≤
      mu * (rootMinorant P (((M : ℝ) + 2) / mu) rho gamma w - activityOnePsi ((M : ℝ) / mu)) := by
  have h := mul_le_mul_of_nonneg_left
    (rootMinorant_lower_bound hP (by positivity : 0 < ((M : ℝ) + 2) / mu) hrho gamma w) hmu.le
  calc
    _ = mu * ((((M : ℝ) + 2) / mu) * (gamma - 2 / rho *
      rootG (Real.log ((((M : ℝ) + 2) / mu) * Real.exp (rho * gamma / 2) / P)))) -
      mu * activityOnePsi ((M : ℝ) / mu) := by rw [← mul_assoc, bonusRange_mulB hmu]
    _ ≤ mu * rootMinorant P (((M : ℝ) + 2) / mu) rho gamma w -
      mu * activityOnePsi ((M : ℝ) / mu) := sub_le_sub_right h _
    _ = _ := by ring

private theorem bonusRange_lower_pos_bound {M : ℕ} (hN : 10 ≤ M + 2)
    {r mu : ℝ} (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hmu : 0 < mu)
    (hl : 0 < threeRangeLambdaL r mu M) (w : ℝ) :
    activityOneT ((M : ℝ) / mu) (M : ℝ) - bonusRangeDL r mu M ≤
      mu * (rootMinorant (threeRangePL r mu M) (((M : ℝ) + 2) / mu)
        (threeRangeRhoL r ((M : ℝ) + 2)) (V22.gamma r ((M : ℝ) + 2)) w -
          activityOnePsi ((M : ℝ) / mu)) := by
  let N : ℝ := (M : ℝ) + 2
  let rhoL := threeRangeRhoL r N
  let lambda0 := activityOneLambda M mu .L
  let lambda := threeRangeLambdaL r mu M
  let e := V22.eL r N
  let Delta := V22.Delta r N
  have hNr : 10 ≤ N := by dsimp [N]; exact_mod_cast hN
  have hn : 0 < N := by linarith
  have hr1 : r < 1 := by linarith
  have hrL : 0 < rhoL := threeRangeRhoL_pos hr0 hr1 M
  have hrho : 0 < V22.rho N := by unfold V22.rho; positivity
  have he : 0 ≤ e := bonusRange_eL_nonneg hn hr0 hr1
  have hD : 0 ≤ Delta := delta_nonneg (by linarith : 1 ≤ N)
    (by nlinarith : r ^ 2 < 1)
  have heps := shared_epsilon_nonneg hr0 hr1 hn
  have hrr : V22.rho N ≤ rhoL := by dsimp [rhoL, threeRangeRhoL]; linarith
  have hlambda : lambda ≤ lambda0 + rhoL / 2 * Delta + e := by
    simpa only [activityOneLambda, activityOnePrefactor] using
      threeRanges_lambdaL_upper hN hr0 hrh hmu
  have hs : 0 ≤ rootMap lambda := (rootMap_nonneg_le hl.le).1
  have hsigma : 0 ≤ rootGPrime lambda := rootGPrime_nonneg hl.le
  have ht := rootG_tangent_upper lambda0 lambda
  have hshift := mul_le_mul_of_nonneg_right
    (show lambda - lambda0 ≤ rhoL / 2 * Delta + e by linarith) hsigma
  have hg : rootG lambda ≤ rootG lambda0 + (rhoL / 2 * Delta + e) * rootGPrime lambda := by
    linarith
  have hroot0 := rootMap_monotone (show lambda ≤ lambda0 + e + rhoL / 2 * Delta by linarith)
  have hroot1 := rootMap_shift_le (lambda0 + e) (rhoL / 2 * Delta) (by positivity)
  have hsbar : rootMap lambda ≤ rootMap (lambda0 + e) + rhoL / 2 * Delta := hroot0.trans hroot1
  have hloss := lower_bonus_loss hn hrL hrr hD he hs hsbar
  have hden : 1 + rootMap lambda ≠ 0 := ne_of_gt (by linarith [rootMap_gt_neg_one lambda])
  have hpay : N * (Delta * (1 - rootGPrime lambda) - 2 / rhoL * e * rootGPrime lambda) =
      N * (Delta - 2 / rhoL * e * rootMap lambda) / (1 + rootMap lambda) := by
    unfold rootGPrime
    field_simp [hden, hrL.ne'] <;> ring
  have hbase := bonusRange_activity_base hN hmu .L
  have hinv := one_div_le_one_div_of_le hrho hrr
  have hG0 := rootG_nonneg lambda0
  have hcoef := mul_le_mul_of_nonneg_right hinv hG0
  have hquad := mul_le_mul_of_nonneg_left hg (show 0 ≤ 2 / rhoL by positivity)
  have hsplit : N * (1 - 2 / V22.rho N * rootG lambda0) +
        N * (Delta * (1 - rootGPrime lambda) - 2 / rhoL * e * rootGPrime lambda) ≤
      N * (1 + Delta - 2 / rhoL * rootG lambda) := by
    have hncoef := mul_le_mul_of_nonneg_left hcoef hn.le
    have hnquad := mul_le_mul_of_nonneg_left hquad hn.le
    have hBase : N * (1 - 2 / V22.rho N * rootG lambda0) ≤
        N * (1 - 2 / rhoL * rootG lambda0) := by
      have hneg := neg_le_neg (mul_le_mul_of_nonneg_left hncoef
        (by norm_num : (0 : ℝ) ≤ 2))
      have hsum := add_le_add (le_refl N) hneg
      convert hsum using 1 <;> ring
    have hid : N * (1 + Delta - 2 / rhoL *
        (rootG lambda0 + (rhoL / 2 * Delta + e) * rootGPrime lambda)) =
      N * (1 - 2 / rhoL * rootG lambda0) +
        N * (Delta * (1 - rootGPrime lambda) - 2 / rhoL * e * rootGPrime lambda) := by
      field_simp [hrL.ne'] <;> ring
    calc
      _ ≤ N * (1 - 2 / rhoL * rootG lambda0) +
          N * (Delta * (1 - rootGPrime lambda) - 2 / rhoL * e * rootGPrime lambda) :=
        add_le_add hBase le_rfl
      _ = N * (1 + Delta - 2 / rhoL *
          (rootG lambda0 + (rhoL / 2 * Delta + e) * rootGPrime lambda)) := hid.symm
      _ ≤ _ := by
        have hsub := sub_le_sub_left hnquad (N * (1 + Delta))
        convert hsub using 1 <;> ring
  rw [hpay] at hsplit
  have hmin := bonusRange_scaled_minimum (M := M) (gamma := V22.gamma r N)
    hmu (threeRangePL_pos hmu r M) hrL w
  change N * (V22.gamma r N - 2 / rhoL * rootG lambda) -
    mu * activityOnePsi ((M : ℝ) / mu) ≤ _ at hmin
  unfold V22.gamma at hmin
  dsimp [N, lambda0, e, Delta] at hloss
  norm_num only [add_assoc] at hloss
  change -bonusRangeDL r mu M ≤ _ at hloss
  simp only [N, rhoL, lambda, lambda0, e, Delta] at hsplit hloss hmin
  unfold V22.gamma
  linarith

/-- Proposition 4.6, the actual lower range under only the original assumptions. -/
theorem bonusRange_lower {M : ℕ} (hN : 10 ≤ M + 2) {r mu : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hmu : 0 < mu) (j : ℤ)
    (hw : threeRangeW r M j ≤ 1) :
    min 2 (activityOneT ((M : ℝ) / mu) (M : ℝ) - bonusRangeDL r mu M) ≤
      mu * (V22.fiberFunction ((1 + r) / 2) mu M j - activityOnePsi ((M : ℝ) / mu)) := by
  have hr1 : r < 1 := by linarith
  have hF := mul_le_mul_of_nonneg_left (threeRanges_lower hN hr0 hrh hmu j hw) hmu.le
  by_cases hl : threeRangeLambdaL r mu M ≤ 0
  · have hB := bonusRange_lower_nonpos (threeRangePL_pos hmu r M)
      (by positivity : 0 < ((M : ℝ) + 2) / mu)
      (threeRangeRhoL_pos hr0 hr1 M) (threeRange_gamma_ge_one hr0 hr1 M) hl _ hw
    have hBs := mul_le_mul_of_nonneg_left hB hmu.le
    rw [bonusRange_mulB hmu] at hBs
    have hmargin := bonusRange_base_margin hmu M
    exact (min_le_left _ _).trans (by linarith)
  · have hmin := bonusRange_lower_pos_bound hN hr0 hrh hmu (by linarith : 0 < threeRangeLambdaL r mu M)
      (threeRangeW r M j)
    exact (min_le_right _ _).trans (by linarith)

/-- Proposition 4.6's middle clause, for every actual atom. -/
theorem bonusRange_middle {M : ℕ} (hN : 10 ≤ M + 2) {r mu : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hmu : 0 < mu) (j : ℤ)
    (hw0 : 1 ≤ threeRangeW r M j) (hw1 : threeRangeW r M j ≤ V22.gamma r ((M : ℝ) + 2)) :
    2 ≤ mu * (V22.fiberFunction ((1 + r) / 2) mu M j - activityOnePsi ((M : ℝ) / mu)) := by
  have h := mul_le_mul_of_nonneg_left (threeRanges_middle hN hr0 hrh hmu j hw0 hw1).2 hmu.le
  rw [bonusRange_mulB hmu] at h
  have hm := bonusRange_base_margin hmu M
  linarith

/-- The upper branch uses the genuine negative derivative, as in Lemma 4.7(b). -/
theorem bonusRange_upper_sigma_negative {r mu : ℝ} {M : ℕ}
    (hl : threeRangeLambdaU r mu M < 0) : rootGPrime (threeRangeLambdaU r mu M) < 0 := by
  simpa only [rootGPrime_zero] using rootGPrime_strictMono hl

/-- The source upper range minimum in branch (a) is attained at `gamma`. -/
theorem bonusRange_upper_minimum_nonnegative {M : ℕ} (hN : 10 ≤ M + 2) {r mu : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hmu : 0 < mu)
    (hl : 0 ≤ threeRangeLambdaU r mu M) :
    IsLeast (rootMinorant (threeRangePU r mu M) (((M : ℝ) + 2) / mu)
      (V22.rhoU r ((M : ℝ) + 2)) (V22.gamma r ((M : ℝ) + 2)) ''
        Ici (V22.gamma r ((M : ℝ) + 2)))
      ((((M : ℝ) + 2) / mu) * V22.gamma r ((M : ℝ) + 2)) := by
  have hNr : (10 : ℝ) ≤ (M : ℝ) + 2 := by exact_mod_cast hN
  have hu := bonusRange_rhoU_pos hNr hr0 hrh
  have hg := threeRange_gamma_ge_one hr0 (by linarith : r < 1) M
  constructor
  · refine ⟨V22.gamma r ((M : ℝ) + 2), (by
      change V22.gamma r ((M : ℝ) + 2) ≤ V22.gamma r ((M : ℝ) + 2)
      exact le_rfl), ?_⟩
    simp only [rootMinorant, sub_self, mul_zero, zero_mul, zero_add]
  · rintro _ ⟨w, hw, rfl⟩
    exact bonusRange_upper_nonneg (threeRangePU_pos hmu r M)
      (by positivity : 0 < ((M : ℝ) + 2) / mu) hu hg hl w hw

/-- In branch (b) the actual root argmin belongs to the upper range and
attains the source's closed-form minimum. -/
theorem bonusRange_upper_minimum_negative {M : ℕ} (hN : 10 ≤ M + 2) {r mu : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hmu : 0 < mu)
    (hl : threeRangeLambdaU r mu M < 0) :
    IsLeast (rootMinorant (threeRangePU r mu M) (((M : ℝ) + 2) / mu)
      (V22.rhoU r ((M : ℝ) + 2)) (V22.gamma r ((M : ℝ) + 2)) ''
        Ici (V22.gamma r ((M : ℝ) + 2)))
      ((((M : ℝ) + 2) / mu) * (V22.gamma r ((M : ℝ) + 2) -
        2 / V22.rhoU r ((M : ℝ) + 2) * rootG (threeRangeLambdaU r mu M))) := by
  have hNr : (10 : ℝ) ≤ (M : ℝ) + 2 := by exact_mod_cast hN
  have hu := bonusRange_rhoU_pos hNr hr0 hrh
  have hb : 0 < ((M : ℝ) + 2) / mu := by positivity
  have hs : rootMap (threeRangeLambdaU r mu M) < 0 := (rootMap_neg_iff _).2 hl
  have harg : V22.gamma r ((M : ℝ) + 2) ≤
      rootMinorantArgmin (V22.rhoU r ((M : ℝ) + 2)) (V22.gamma r ((M : ℝ) + 2))
        (rootMap (threeRangeLambdaU r mu M)) := by
    unfold rootMinorantArgmin
    have hd : 2 * rootMap (threeRangeLambdaU r mu M) / V22.rhoU r ((M : ℝ) + 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hu.le
    linarith
  constructor
  · refine ⟨rootMinorantArgmin (V22.rhoU r ((M : ℝ) + 2)) (V22.gamma r ((M : ℝ) + 2))
      (rootMap (threeRangeLambdaU r mu M)), harg, ?_⟩
    exact rootMinorant_argmin_value (threeRangePU_pos hmu r M) hb hu _
  · rintro _ ⟨w, _, rfl⟩
    exact rootMinorant_lower_bound (threeRangePU_pos hmu r M) hb hu _ w

/-- Lemma 4.7(a), before consumption by the actual fiber: every real `w≥gamma`. -/
theorem bonusRange_upper_min_nonneg {M : ℕ} (hN : 10 ≤ M + 2) {r mu : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hmu : 0 < mu)
    (hl : 0 ≤ threeRangeLambdaU r mu M) (w : ℝ) (hw : V22.gamma r ((M : ℝ) + 2) ≤ w) :
    2 ≤ mu * (rootMinorant (threeRangePU r mu M) (((M : ℝ) + 2) / mu)
      (V22.rhoU r ((M : ℝ) + 2)) (V22.gamma r ((M : ℝ) + 2)) w -
        activityOnePsi ((M : ℝ) / mu)) := by
  have hNr : (10 : ℝ) ≤ (M : ℝ) + 2 := by exact_mod_cast hN
  have hgamma := threeRange_gamma_ge_one hr0 (by linarith : r < 1) M
  have h := bonusRange_upper_nonneg (threeRangePU_pos hmu r M)
    (by positivity : 0 < ((M : ℝ) + 2) / mu)
    (bonusRange_rhoU_pos hNr hr0 hrh) hgamma hl w hw
  have hs := mul_le_mul_of_nonneg_left h hmu.le
  have hB := mul_le_mul_of_nonneg_left hgamma (show 0 ≤ (M : ℝ) + 2 by positivity)
  rw [← mul_assoc, bonusRange_mulB hmu] at hs
  have hm := bonusRange_base_margin hmu M
  linarith

/-- Lemma 4.7(b), its first displayed inequality with both bonus copies. -/
theorem bonusRange_upper_min_negative_payment {M : ℕ} (hN : 10 ≤ M + 2) {r mu : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hmu : 0 < mu)
    (hl : threeRangeLambdaU r mu M < 0) (w : ℝ) :
    activityOneT ((M : ℝ) / mu) (M : ℝ) - 2 * ((M : ℝ) + 2) *
        (1 / V22.rhoU r ((M : ℝ) + 2) - 1 / V22.rho ((M : ℝ) + 2)) *
        rootG (activityOneLambda M mu .U) + ((M : ℝ) + 2) * V22.Delta r ((M : ℝ) + 2) -
      |rootGPrime (threeRangeLambdaU r mu M)| *
        (2 * ((M : ℝ) + 2) / V22.rhoU r ((M : ℝ) + 2) * V22.eU r ((M : ℝ) + 2) -
          ((M : ℝ) + 2) * V22.Delta r ((M : ℝ) + 2)) ≤
      mu * (rootMinorant (threeRangePU r mu M) (((M : ℝ) + 2) / mu)
        (V22.rhoU r ((M : ℝ) + 2)) (V22.gamma r ((M : ℝ) + 2)) w -
          activityOnePsi ((M : ℝ) / mu)) := by
  have hNr : (10 : ℝ) ≤ (M : ℝ) + 2 := by exact_mod_cast hN
  have hn : 0 < (M : ℝ) + 2 := by positivity
  have hrho : 0 < V22.rho ((M : ℝ) + 2) := by unfold V22.rho; positivity
  have hu := bonusRange_rhoU_pos hNr hr0 hrh
  have hd := delta_nonneg (by linarith : 1 ≤ (M : ℝ) + 2) (by nlinarith : r ^ 2 < 1)
  have heq : threeRangeLambdaU r mu M = activityOneLambda M mu .U +
      (V22.rhoU r ((M : ℝ) + 2) / 2 * V22.Delta r ((M : ℝ) + 2) - V22.eU r ((M : ℝ) + 2)) := by
    simpa only [activityOneLambda, activityOnePrefactor, add_sub_assoc] using
      threeRanges_lambdaU_eq hN hr0 hrh hmu
  have hbase := bonusRange_activity_base hN hmu .U
  have hmin := bonusRange_scaled_minimum (M := M) (gamma := V22.gamma r ((M : ℝ) + 2))
    hmu (threeRangePU_pos hmu r M) hu w
  unfold V22.gamma at hmin
  exact upper_bonus_payment hn hrho hu hd heq hl hbase hmin

/-- Lemma 4.7(b), the exact positive-part remainder bound on every real atom. -/
theorem bonusRange_upper_min_negative {M : ℕ} (hN : 10 ≤ M + 2) {r mu : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hmu : 0 < mu)
    (hl : threeRangeLambdaU r mu M < 0) (w : ℝ) :
    activityOneT ((M : ℝ) / mu) (M : ℝ) - bonusRangeDUPrime r mu M ≤
      mu * (rootMinorant (threeRangePU r mu M) (((M : ℝ) + 2) / mu)
        (V22.rhoU r ((M : ℝ) + 2)) (V22.gamma r ((M : ℝ) + 2)) w -
          activityOnePsi ((M : ℝ) / mu)) := by
  have hp := bonusRange_upper_min_negative_payment hN hr0 hrh hmu hl w
  have hA := le_max_left (2 * ((M : ℝ) + 2) *
    (1 / V22.rhoU r ((M : ℝ) + 2) - 1 / V22.rho ((M : ℝ) + 2)) *
      rootG (activityOneLambda M mu .U) - ((M : ℝ) + 2) * V22.Delta r ((M : ℝ) + 2)) (0 : ℝ)
  have hB := mul_le_mul_of_nonneg_left (le_max_left
    (2 * ((M : ℝ) + 2) / V22.rhoU r ((M : ℝ) + 2) * V22.eU r ((M : ℝ) + 2) -
      ((M : ℝ) + 2) * V22.Delta r ((M : ℝ) + 2)) (0 : ℝ))
      (abs_nonneg (rootGPrime (threeRangeLambdaU r mu M)))
  unfold bonusRangeDUPrime
  linarith

/-- The actual-fiber consumer of Lemma 4.7(a). -/
theorem bonusRange_upper_nonnegative_fiber {M : ℕ} (hN : 10 ≤ M + 2) {r mu : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hmu : 0 < mu)
    (hl : 0 ≤ threeRangeLambdaU r mu M) (j : ℤ)
    (hw : V22.gamma r ((M : ℝ) + 2) ≤ threeRangeW r M j) :
    2 ≤ mu * (V22.fiberFunction ((1 + r) / 2) mu M j - activityOnePsi ((M : ℝ) / mu)) := by
  have hm := bonusRange_upper_min_nonneg hN hr0 hrh hmu hl _ hw
  have hF := mul_le_mul_of_nonneg_left (threeRanges_upper hN hr0 hrh hmu j hw) hmu.le
  linarith

/-- The actual-fiber consumer of Lemma 4.7(b), with its source sign premise. -/
theorem bonusRange_upper_negative_fiber {M : ℕ} (hN : 10 ≤ M + 2) {r mu : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hmu : 0 < mu)
    (hl : threeRangeLambdaU r mu M < 0) (j : ℤ)
    (hw : V22.gamma r ((M : ℝ) + 2) ≤ threeRangeW r M j) :
    activityOneT ((M : ℝ) / mu) (M : ℝ) - bonusRangeDUPrime r mu M ≤
      mu * (V22.fiberFunction ((1 + r) / 2) mu M j - activityOnePsi ((M : ℝ) / mu)) := by
  have hm := bonusRange_upper_min_negative hN hr0 hrh hmu hl (threeRangeW r M j)
  have hF := mul_le_mul_of_nonneg_left (threeRanges_upper hN hr0 hrh hmu j hw) hmu.le
  linarith

/-- The actual-fiber consumer of the first displayed inequality of Lemma 4.7(b). -/
theorem bonusRange_upper_negative_payment_fiber {M : ℕ} (hN : 10 ≤ M + 2) {r mu : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hmu : 0 < mu)
    (hl : threeRangeLambdaU r mu M < 0) (j : ℤ)
    (hw : V22.gamma r ((M : ℝ) + 2) ≤ threeRangeW r M j) :
    activityOneT ((M : ℝ) / mu) (M : ℝ) - 2 * ((M : ℝ) + 2) *
        (1 / V22.rhoU r ((M : ℝ) + 2) - 1 / V22.rho ((M : ℝ) + 2)) *
        rootG (activityOneLambda M mu .U) + ((M : ℝ) + 2) * V22.Delta r ((M : ℝ) + 2) -
      |rootGPrime (threeRangeLambdaU r mu M)| *
        (2 * ((M : ℝ) + 2) / V22.rhoU r ((M : ℝ) + 2) * V22.eU r ((M : ℝ) + 2) -
          ((M : ℝ) + 2) * V22.Delta r ((M : ℝ) + 2)) ≤
      mu * (V22.fiberFunction ((1 + r) / 2) mu M j - activityOnePsi ((M : ℝ) / mu)) := by
  have hm := bonusRange_upper_min_negative_payment hN hr0 hrh hmu hl (threeRangeW r M j)
  have hF := mul_le_mul_of_nonneg_left (threeRanges_upper hN hr0 hrh hmu j hw) hmu.le
  linarith

/-- The useful unconditional upper-range consequence retains the source minimum. -/
theorem bonusRange_upper {M : ℕ} (hN : 10 ≤ M + 2) {r mu : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hmu : 0 < mu) (j : ℤ)
    (hw : V22.gamma r ((M : ℝ) + 2) ≤ threeRangeW r M j) :
    min 2 (activityOneT ((M : ℝ) / mu) (M : ℝ) - bonusRangeDUPrime r mu M) ≤
      mu * (V22.fiberFunction ((1 + r) / 2) mu M j - activityOnePsi ((M : ℝ) / mu)) := by
  by_cases hl : 0 ≤ threeRangeLambdaU r mu M
  · exact (min_le_left _ _).trans (bonusRange_upper_nonnegative_fiber hN hr0 hrh hmu hl j hw)
  · exact (min_le_right _ _).trans (bonusRange_upper_negative_fiber hN hr0 hrh hmu (by linarith) j hw)

/-- Exact shared-function Proposition 4.6(L), for the later remainder consumer. -/
theorem shared_bonusRange_lower {M : ℕ} (hN : 10 ≤ M + 2) {r mu : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hmu : 0 < mu) (j : ℤ)
    (hw : threeRangeW r M j ≤ 1) :
    min 2 (V22.templateT ((M : ℝ) / mu) (M : ℝ) - sharedLowerRemainder r mu M) ≤
      mu * (V22.fiberFunction ((1 + r) / 2) mu M j - V22.psi ((M : ℝ) / mu)) := by
  simpa only [shared_templateT_eq, shared_psi_eq, sharedLowerRemainder_eq] using
    bonusRange_lower hN hr0 hrh hmu j hw

theorem shared_bonusRange_upper {M : ℕ} (hN : 10 ≤ M + 2) {r mu : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hmu : 0 < mu) (j : ℤ)
    (hw : V22.gamma r ((M : ℝ) + 2) ≤ threeRangeW r M j) :
    min 2 (V22.templateT ((M : ℝ) / mu) (M : ℝ) - sharedUpperRemainderPrime r mu M) ≤
      mu * (V22.fiberFunction ((1 + r) / 2) mu M j - V22.psi ((M : ℝ) / mu)) := by
  simpa only [shared_templateT_eq, shared_psi_eq, sharedUpperRemainderPrime_eq] using
    bonusRange_upper hN hr0 hrh hmu j hw

end Erdos993Lean.Analytic.V22.Analysis
