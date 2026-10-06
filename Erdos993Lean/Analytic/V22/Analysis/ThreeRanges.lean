import Erdos993Lean.Analytic.V22.Analysis.GaussianLower
import Erdos993Lean.Analytic.V22.Analysis.AmplitudeShift
import Erdos993Lean.Analytic.V22.Analysis.SharedRoot
import Erdos993Lean.Analytic.V22.Analysis.MiddleRange

/-!
# The three exact ranges of the actual fiber

Source: frozen `SOURCE_V5_note.tex`, Proposition 4.5, lines 561--579.
The native prefactors below are the ones displayed in its proof. All final
comparisons retain every integer `j` and use only `N=M+2≥10`, `0≤r≤1/2`
and `mu>0`. In particular no positivity premise on `rhoU` is imposed here.
The bonus and square-offset bridges retain the actual kernel coordinates.
Compilation is owned by the root lane, not this drafting subagent.
-/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Erdos993Lean.Analytic.NoValley

/-- The standardized square of the actual atom `J=j+1`, with `N=M+2`. -/
noncomputable def threeRangeW (r : ℝ) (M : ℕ) (j : ℤ) : ℝ :=
  (sharedGaussianX r (M + 2) (j + 1)) ^ 2

noncomputable def threeRangeMass (r : ℝ) (M : ℕ) (j : ℤ) : ℝ :=
  Real.sqrt (1 - r ^ 2) / Erdos993Lean.Analytic.V22.centralAmplitude (M + 2) *
    binom (M + 2) ((1 + r) / 2) (j + 1)

/-- Proposition 4.5(L), the explicit native amplitude from its proof. -/
noncomputable def threeRangePL (r mu : ℝ) (M : ℕ) : ℝ :=
  shapeTemplatePrefactor mu ((M : ℝ) + 2)
      (Erdos993Lean.Analytic.V22.centralAmplitude (M + 2)) *
    Real.exp (-Erdos993Lean.Analytic.V22.c0 r ((M : ℝ) + 2) -
      Erdos993Lean.Analytic.V22.quarticError r ((M : ℝ) + 2) 1 -
      Erdos993Lean.Analytic.V22.epsilon r ((M : ℝ) + 2) / 2)

/-- Proposition 4.5(U), the explicit native amplitude from its proof. -/
noncomputable def threeRangePU (r mu : ℝ) (M : ℕ) : ℝ :=
  shapeTemplatePrefactor mu ((M : ℝ) + 2) (symmetricUpperPrefactor (M + 2)) *
    Real.exp (((M : ℝ) + 3) * Erdos993Lean.Analytic.V22.cr r -
      Erdos993Lean.Analytic.V22.c0Prime r ((M : ℝ) + 2) +
      Erdos993Lean.Analytic.V22.epsilonPrime r ((M : ℝ) + 2) *
        Real.sqrt (Erdos993Lean.Analytic.V22.gamma r ((M : ℝ) + 2)) / 2)

noncomputable def threeRangeRhoL (r N : ℝ) : ℝ :=
  Erdos993Lean.Analytic.V22.rho N + Erdos993Lean.Analytic.V22.epsilon r N

noncomputable def threeRangeLambdaL (r mu : ℝ) (M : ℕ) : ℝ :=
  Real.log ((((M : ℝ) + 2) / mu) *
    Real.exp (threeRangeRhoL r ((M : ℝ) + 2) *
      Erdos993Lean.Analytic.V22.gamma r ((M : ℝ) + 2) / 2) / threeRangePL r mu M)

noncomputable def threeRangeLambdaU (r mu : ℝ) (M : ℕ) : ℝ :=
  Real.log ((((M : ℝ) + 2) / mu) *
    Real.exp (Erdos993Lean.Analytic.V22.rhoU r ((M : ℝ) + 2) *
      Erdos993Lean.Analytic.V22.gamma r ((M : ℝ) + 2) / 2) / threeRangePU r mu M)

theorem threeRange_signedR_eq (r : ℝ) : signedR ((1 + r) / 2) = r := by
  unfold signedR
  ring

theorem threeRange_variance_eq (r : ℝ) :
    variance ((1 + r) / 2) = Erdos993Lean.Analytic.V22.varianceR r := by
  unfold variance Erdos993Lean.Analytic.V22.varianceR
  ring

theorem threeRange_offset_eq (r : ℝ) (M : ℕ) (j : ℤ) :
    offset ((1 + r) / 2) M j = sharedGaussianU r (M + 2) (j + 1) := by
  rw [offset_eq]
  unfold sharedGaussianU
  push_cast
  ring

/-- The exact bonus `gamma=1+Delta`, not an independent bonus parameter. -/
theorem threeRange_bonus_eq {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (M : ℕ) :
    bonus ((1 + r) / 2) M = Erdos993Lean.Analytic.V22.gamma r ((M : ℝ) + 2) := by
  have hv := shared_one_sub_sq_pos (by linarith : -1 < r) hr1
  have hn : (M : ℝ) + 2 ≠ 0 := by positivity
  unfold bonus Erdos993Lean.Analytic.V22.gamma Erdos993Lean.Analytic.V22.Delta
  rw [threeRange_signedR_eq]
  field_simp [hv.ne', hn] <;> ring

theorem threeRange_squareOffset_eq {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (M : ℕ) (j : ℤ) : squareOffset ((1 + r) / 2) M j = threeRangeW r M j := by
  have hn : 0 < ((M + 2 : ℕ) : ℝ) := by positivity
  unfold squareOffset threeRangeW sharedGaussianX
  rw [div_pow, shared_sN_sq hr0 hr1 hn, threeRange_offset_eq, threeRange_variance_eq]
  norm_num only [Nat.cast_add, Nat.cast_ofNat]

theorem threeRange_gamma_ge_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (M : ℕ) :
    1 ≤ Erdos993Lean.Analytic.V22.gamma r ((M : ℝ) + 2) := by
  rw [← threeRange_bonus_eq hr0 hr1 M]
  exact bonus_ge_one (by linarith) (by linarith) M

theorem threeRangePL_pos {mu : ℝ} (hmu : 0 < mu) (r : ℝ) (M : ℕ) :
    0 < threeRangePL r mu M := by
  unfold threeRangePL
  exact mul_pos (shapeTemplatePrefactor_pos (N := (M : ℝ) + 2) hmu
    (by linarith [Nat.cast_nonneg (α := ℝ) M])
    (shared_centralAmplitude_pos (M + 2))) (Real.exp_pos _)

/-- `PU` is positive without assuming `rhoU` positive. -/
theorem threeRangePU_pos {mu : ℝ} (hmu : 0 < mu) (r : ℝ) (M : ℕ) :
    0 < threeRangePU r mu M := by
  unfold threeRangePU
  exact mul_pos (shapeTemplatePrefactor_pos (N := (M : ℝ) + 2) hmu
    (by linarith [Nat.cast_nonneg (α := ℝ) M])
    (symmetricUpperPrefactor_pos (M + 2))) (Real.exp_pos _)

theorem threeRangeRhoL_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (M : ℕ) :
    0 < threeRangeRhoL r ((M : ℝ) + 2) := by
  have hn : 0 < (M : ℝ) + 2 := by positivity
  have he := shared_epsilon_nonneg hr0 hr1 hn
  have hr : 0 < Erdos993Lean.Analytic.V22.rho ((M : ℝ) + 2) := by
    unfold Erdos993Lean.Analytic.V22.rho
    positivity
  unfold threeRangeRhoL
  linarith

/-- The actual whole-integer fiber in the exact source coordinates. -/
theorem threeRange_fiber_eq {r mu : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hmu : 0 < mu) (M : ℕ) (j : ℤ) :
    Erdos993Lean.Analytic.V22.fiberFunction ((1 + r) / 2) mu M j =
      shapeTemplatePrefactor mu ((M : ℝ) + 2)
        (Erdos993Lean.Analytic.V22.centralAmplitude (M + 2)) * threeRangeMass r M j *
        (Erdos993Lean.Analytic.V22.gamma r ((M : ℝ) + 2) - threeRangeW r M j) +
      (((M : ℝ) + 2) / mu) * threeRangeW r M j := by
  rw [shared_fiberFunction_eq, fiber_eq (by linarith) (by linarith) hmu,
    threeRange_bonus_eq hr0 hr1, threeRange_squareOffset_eq hr0 hr1,
    threeRange_signedR_eq]
  have hc := (shared_centralAmplitude_pos (M + 2)).ne'
  have ha := shapeGaussianA_pos.ne'
  have hm : (M : ℝ) + 1 ≠ 0 := by positivity
  unfold shapeTemplatePrefactor threeRangeMass
  have hm' : 1 + (M : ℝ) ≠ 0 := by positivity
  field_simp [hc, ha, hm] <;> ring_nf <;> field_simp [hm'] <;> ring

private theorem threeRange_abs_tangent (x : ℝ) : |x| ≤ (x ^ 2 + 1) / 2 := by
  nlinarith [sq_nonneg (|x| - 1), sq_abs x]

private theorem threeRange_abs_gamma_tangent (x gamma : ℝ) (hg : 0 < gamma) :
    |x| ≤ (x ^ 2 + gamma) / (2 * Real.sqrt gamma) := by
  have hs := Real.sqrt_pos.2 hg
  have hsq := Real.sq_sqrt hg.le
  apply (le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt gamma)).2
  nlinarith [sq_nonneg (|x| - Real.sqrt gamma), sq_abs x]

private theorem threeRange_lower_coefficient {M : ℕ} (hN : 10 ≤ M + 2)
    {r mu : ℝ} (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hmu : 0 < mu)
    (j : ℤ) (hw : threeRangeW r M j ≤ 1) :
    threeRangePL r mu M * Real.exp (-threeRangeRhoL r ((M : ℝ) + 2) *
        threeRangeW r M j / 2) ≤
      shapeTemplatePrefactor mu ((M : ℝ) + 2)
        (Erdos993Lean.Analytic.V22.centralAmplitude (M + 2)) * threeRangeMass r M j := by
  have hr1 : r < 1 := by linarith
  have hn : 0 < (M : ℝ) + 2 := by positivity
  have heps := shared_epsilon_nonneg hr0 hr1 hn
  have ht := mul_le_mul_of_nonneg_left
    (threeRange_abs_tangent (sharedGaussianX r (M + 2) (j + 1))) heps
  have hmass := shared_binomial_lower_exponents hN hr0 hrh (j + 1) hw
  simp only [Nat.cast_add, Nat.cast_ofNat] at hmass
  change Real.exp (_) ≤ threeRangeMass r M j at hmass
  have hexp : Real.exp (-threeRangeRhoL r ((M : ℝ) + 2) * threeRangeW r M j / 2 -
        Erdos993Lean.Analytic.V22.c0 r ((M : ℝ) + 2) -
        Erdos993Lean.Analytic.V22.quarticError r ((M : ℝ) + 2) 1 -
        Erdos993Lean.Analytic.V22.epsilon r ((M : ℝ) + 2) / 2) ≤ threeRangeMass r M j := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hmass
    unfold threeRangeRhoL threeRangeW
    nlinarith
  have hp := (shapeTemplatePrefactor_pos (N := (M : ℝ) + 2) hmu
    (by linarith [Nat.cast_nonneg (α := ℝ) M])
    (shared_centralAmplitude_pos (M + 2))).le
  have h := mul_le_mul_of_nonneg_left hexp hp
  convert h using 1
  unfold threeRangePL
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Proposition 4.5(L), retaining the actual fiber and every integer index. -/
theorem threeRanges_lower {M : ℕ} (hN : 10 ≤ M + 2) {r mu : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hmu : 0 < mu) (j : ℤ)
    (hw : threeRangeW r M j ≤ 1) :
    rootMinorant (threeRangePL r mu M) (((M : ℝ) + 2) / mu)
      (threeRangeRhoL r ((M : ℝ) + 2))
      (Erdos993Lean.Analytic.V22.gamma r ((M : ℝ) + 2)) (threeRangeW r M j) ≤
      Erdos993Lean.Analytic.V22.fiberFunction ((1 + r) / 2) mu M j := by
  have hr1 : r < 1 := by linarith
  have hsgn : 0 ≤ Erdos993Lean.Analytic.V22.gamma r ((M : ℝ) + 2) - threeRangeW r M j :=
    sub_nonneg.mpr (hw.trans (threeRange_gamma_ge_one hr0 hr1 M))
  have h := mul_le_mul_of_nonneg_right (threeRange_lower_coefficient hN hr0 hrh hmu j hw) hsgn
  rw [threeRange_fiber_eq hr0 hr1 hmu]
  unfold rootMinorant
  nlinarith

/-- Proposition 4.5(M): the two displayed source comparisons. -/
theorem threeRanges_middle {M : ℕ} (_hN : 10 ≤ M + 2) {r mu : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hmu : 0 < mu) (j : ℤ)
    (hw0 : 1 ≤ threeRangeW r M j)
    (hw1 : threeRangeW r M j ≤ Erdos993Lean.Analytic.V22.gamma r ((M : ℝ) + 2)) :
    (((M : ℝ) + 2) / mu) * threeRangeW r M j ≤
        Erdos993Lean.Analytic.V22.fiberFunction ((1 + r) / 2) mu M j ∧
      ((M : ℝ) + 2) / mu ≤
        Erdos993Lean.Analytic.V22.fiberFunction ((1 + r) / 2) mu M j := by
  have hr1 : r < 1 := by linarith
  rw [← threeRange_squareOffset_eq hr0 hr1] at hw0 hw1 ⊢
  rw [← threeRange_bonus_eq hr0 hr1] at hw1
  rw [shared_fiberFunction_eq]
  exact fiber_middle_lower (by linarith) (by linarith) hmu M j hw0 hw1

private theorem threeRange_upper_coefficient {M : ℕ} (hN : 10 ≤ M + 2)
    {r mu : ℝ} (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hmu : 0 < mu) (j : ℤ) :
    shapeTemplatePrefactor mu ((M : ℝ) + 2)
        (Erdos993Lean.Analytic.V22.centralAmplitude (M + 2)) * threeRangeMass r M j ≤
      threeRangePU r mu M * Real.exp (-Erdos993Lean.Analytic.V22.rhoU r ((M : ℝ) + 2) *
        threeRangeW r M j / 2) := by
  have hr1 : r < 1 := by linarith
  have hn : 0 < (M : ℝ) + 2 := by positivity
  have hg : 0 < Erdos993Lean.Analytic.V22.gamma r ((M : ℝ) + 2) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (threeRange_gamma_ge_one hr0 hr1 M)
  have hs := Real.sqrt_pos.2 hg
  have hsq := Real.sq_sqrt hg.le
  have heps := shared_epsilonPrime_nonneg hr0 hr1 hn
  have ht := mul_le_mul_of_nonneg_left
    (threeRange_abs_gamma_tangent (sharedGaussianX r (M + 2) (j + 1)) _ hg) heps
  have hmass := shared_binomial_upper_exponents (by omega : 2 ≤ M + 2) hr0 hr1 (j + 1)
  simp only [Nat.cast_add, Nat.cast_ofNat] at hmass
  change threeRangeMass r M j ≤ _ at hmass
  have hp := (shapeTemplatePrefactor_pos (N := (M : ℝ) + 2) hmu
    (by linarith [Nat.cast_nonneg (α := ℝ) M])
    (shared_centralAmplitude_pos (M + 2))).le
  have hc := (shared_centralAmplitude_pos (M + 2)).ne'
  have hn1 : (M : ℝ) + 1 ≠ 0 := by positivity
  have heq : shapeTemplatePrefactor mu ((M : ℝ) + 2)
      (Erdos993Lean.Analytic.V22.centralAmplitude (M + 2)) *
      (symmetricUpperPrefactor (M + 2) / Erdos993Lean.Analytic.V22.centralAmplitude (M + 2)) =
      shapeTemplatePrefactor mu ((M : ℝ) + 2) (symmetricUpperPrefactor (M + 2)) := by
    unfold shapeTemplatePrefactor
    field_simp [hc, shapeGaussianA_pos.ne', hn1] <;> ring
  have hbound := mul_le_mul_of_nonneg_left hmass hp
  rw [← mul_assoc, heq] at hbound
  have hpow : ((M : ℝ) + 3) * Erdos993Lean.Analytic.V22.cr r -
        Erdos993Lean.Analytic.V22.c0Prime r ((M : ℝ) + 2) -
        (1 - r ^ 2) * Erdos993Lean.Analytic.V22.rho ((M : ℝ) + 2) / 2 * threeRangeW r M j +
        Erdos993Lean.Analytic.V22.epsilonPrime r ((M : ℝ) + 2) *
          ((threeRangeW r M j + Erdos993Lean.Analytic.V22.gamma r ((M : ℝ) + 2)) /
            (2 * Real.sqrt (Erdos993Lean.Analytic.V22.gamma r ((M : ℝ) + 2)))) =
      (((M : ℝ) + 3) * Erdos993Lean.Analytic.V22.cr r -
        Erdos993Lean.Analytic.V22.c0Prime r ((M : ℝ) + 2) +
        Erdos993Lean.Analytic.V22.epsilonPrime r ((M : ℝ) + 2) *
          Real.sqrt (Erdos993Lean.Analytic.V22.gamma r ((M : ℝ) + 2)) / 2) +
        (-Erdos993Lean.Analytic.V22.rhoU r ((M : ℝ) + 2) * threeRangeW r M j / 2) := by
    unfold Erdos993Lean.Analytic.V22.rhoU
    field_simp [hs.ne']
    ring_nf at hsq ⊢
    rw [hsq]
    ring
  apply hbound.trans
  unfold threeRangePU
  rw [mul_assoc, ← Real.exp_add, ← hpow]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
    (shapeTemplatePrefactor_pos (N := (M : ℝ) + 2) hmu
    (by linarith [Nat.cast_nonneg (α := ℝ) M]) (symmetricUpperPrefactor_pos (M + 2))).le
  unfold threeRangeW
  linarith

/-- Proposition 4.5(U); the coefficient comparison is multiplied by the
nonpositive actual factor `gamma-w`, so every exterior integer stays covered. -/
theorem threeRanges_upper {M : ℕ} (hN : 10 ≤ M + 2) {r mu : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hmu : 0 < mu) (j : ℤ)
    (hw : Erdos993Lean.Analytic.V22.gamma r ((M : ℝ) + 2) ≤ threeRangeW r M j) :
    rootMinorant (threeRangePU r mu M) (((M : ℝ) + 2) / mu)
      (Erdos993Lean.Analytic.V22.rhoU r ((M : ℝ) + 2))
      (Erdos993Lean.Analytic.V22.gamma r ((M : ℝ) + 2)) (threeRangeW r M j) ≤
      Erdos993Lean.Analytic.V22.fiberFunction ((1 + r) / 2) mu M j := by
  have hr1 : r < 1 := by linarith
  have h := mul_le_mul_of_nonpos_right (threeRange_upper_coefficient hN hr0 hrh hmu j)
    (sub_nonpos.mpr hw)
  rw [threeRange_fiber_eq hr0 hr1 hmu]
  unfold rootMinorant
  nlinarith

private theorem threeRange_log_ratio {P B rho gamma : ℝ} (hP : 0 < P) (hB : 0 < B) :
    Real.log (B * Real.exp (rho * gamma / 2) / P) =
      Real.log B + rho * gamma / 2 - Real.log P := by
  rw [Real.log_div (mul_pos hB (Real.exp_pos _)).ne' hP.ne',
    Real.log_mul hB.ne' (Real.exp_pos _).ne', Real.log_exp]

/-- Proposition 4.5(L), the original one-sided log-ratio error with `(E4-E0)+`. -/
theorem threeRanges_lambdaL_upper {M : ℕ} (hN : 10 ≤ M + 2) {r mu : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hmu : 0 < mu) :
    threeRangeLambdaL r mu M ≤
      shapeTemplateLambda mu ((M : ℝ) + 2) (symmetricLowerPrefactor (M + 2)) +
      threeRangeRhoL r ((M : ℝ) + 2) / 2 * Erdos993Lean.Analytic.V22.Delta r ((M : ℝ) + 2) +
      Erdos993Lean.Analytic.V22.eL r ((M : ℝ) + 2) := by
  have hb : 0 < ((M : ℝ) + 2) / mu := by positivity
  have hl := shapeTemplatePrefactor_pos (N := (M : ℝ) + 2) hmu
    (by linarith [Nat.cast_nonneg (α := ℝ) M])
    (symmetricLowerPrefactor_pos (by omega : 2 ≤ M + 2))
  have hc := shapeTemplatePrefactor_pos (N := (M : ℝ) + 2) hmu
    (by linarith [Nat.cast_nonneg (α := ℝ) M]) (shared_centralAmplitude_pos (M + 2))
  have hcentral := shared_centralAmplitude_lower (by omega : 2 ≤ M + 2)
  simp only [Nat.cast_add, Nat.cast_ofNat] at hcentral
  have hfactor : 0 ≤ mu ^ (3 / 2 : ℝ) / (2 * gaussianA * (((M : ℝ) + 2) - 1)) := by
    have ha := shapeGaussianA_pos
    have hden : 0 < ((M : ℝ) + 2) - 1 := by linarith [Nat.cast_nonneg (α := ℝ) M]
    positivity
  have hcp : shapeTemplatePrefactor mu ((M : ℝ) + 2) (symmetricLowerPrefactor (M + 2)) *
      Real.exp (Erdos993Lean.Analytic.V22.quarticErrorZero ((M : ℝ) + 2)) ≤
      shapeTemplatePrefactor mu ((M : ℝ) + 2)
        (Erdos993Lean.Analytic.V22.centralAmplitude (M + 2)) := by
    convert mul_le_mul_of_nonneg_left hcentral hfactor using 1 <;>
      unfold shapeTemplatePrefactor <;> ring
  have hlog := Real.log_le_log (mul_pos hl (Real.exp_pos _)) hcp
  rw [Real.log_mul hl.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  have hpl : Real.log (threeRangePL r mu M) =
      Real.log (shapeTemplatePrefactor mu ((M : ℝ) + 2)
        (Erdos993Lean.Analytic.V22.centralAmplitude (M + 2))) -
      Erdos993Lean.Analytic.V22.c0 r ((M : ℝ) + 2) -
      Erdos993Lean.Analytic.V22.quarticError r ((M : ℝ) + 2) 1 -
      Erdos993Lean.Analytic.V22.epsilon r ((M : ℝ) + 2) / 2 := by
    unfold threeRangePL
    rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  have ht : shapeTemplateLambda mu ((M : ℝ) + 2) (symmetricLowerPrefactor (M + 2)) =
      Real.log (((M : ℝ) + 2) / mu) + Erdos993Lean.Analytic.V22.rho ((M : ℝ) + 2) / 2 -
      Real.log (shapeTemplatePrefactor mu ((M : ℝ) + 2) (symmetricLowerPrefactor (M + 2))) := by
    unfold shapeTemplateLambda
    simpa only [mul_one, Erdos993Lean.Analytic.V22.rho] using
      (threeRange_log_ratio (rho := Erdos993Lean.Analytic.V22.rho ((M : ℝ) + 2))
        (gamma := 1) hl hb)
  have hident : shapeTemplateLambda mu ((M : ℝ) + 2) (symmetricLowerPrefactor (M + 2)) +
        threeRangeRhoL r ((M : ℝ) + 2) / 2 * Erdos993Lean.Analytic.V22.Delta r ((M : ℝ) + 2) +
        Erdos993Lean.Analytic.V22.eL r ((M : ℝ) + 2) - threeRangeLambdaL r mu M =
      (Real.log (shapeTemplatePrefactor mu ((M : ℝ) + 2)
          (Erdos993Lean.Analytic.V22.centralAmplitude (M + 2))) -
        Real.log (shapeTemplatePrefactor mu ((M : ℝ) + 2) (symmetricLowerPrefactor (M + 2))) -
        Erdos993Lean.Analytic.V22.quarticErrorZero ((M : ℝ) + 2)) +
      (Erdos993Lean.Analytic.V22.positivePart
          (Erdos993Lean.Analytic.V22.quarticError r ((M : ℝ) + 2) 1 -
            Erdos993Lean.Analytic.V22.quarticErrorZero ((M : ℝ) + 2)) -
        (Erdos993Lean.Analytic.V22.quarticError r ((M : ℝ) + 2) 1 -
          Erdos993Lean.Analytic.V22.quarticErrorZero ((M : ℝ) + 2))) := by
    unfold threeRangeLambdaL
    rw [threeRange_log_ratio (threeRangePL_pos hmu r M) hb, hpl, ht]
    unfold Erdos993Lean.Analytic.V22.eL threeRangeRhoL Erdos993Lean.Analytic.V22.gamma
    ring
  have hpart : Erdos993Lean.Analytic.V22.quarticError r ((M : ℝ) + 2) 1 -
      Erdos993Lean.Analytic.V22.quarticErrorZero ((M : ℝ) + 2) ≤
      Erdos993Lean.Analytic.V22.positivePart
        (Erdos993Lean.Analytic.V22.quarticError r ((M : ℝ) + 2) 1 -
          Erdos993Lean.Analytic.V22.quarticErrorZero ((M : ℝ) + 2)) :=
    le_max_left _ _
  linarith

/-- Proposition 4.5(U), the exact `eU` identity, retaining `-c0Prime`. -/
theorem threeRanges_lambdaU_eq {M : ℕ} (_hN : 10 ≤ M + 2) {r mu : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hmu : 0 < mu) :
    threeRangeLambdaU r mu M =
      shapeTemplateLambda mu ((M : ℝ) + 2) (symmetricUpperPrefactor (M + 2)) +
      Erdos993Lean.Analytic.V22.rhoU r ((M : ℝ) + 2) / 2 *
        Erdos993Lean.Analytic.V22.Delta r ((M : ℝ) + 2) -
      Erdos993Lean.Analytic.V22.eU r ((M : ℝ) + 2) := by
  have hb : 0 < ((M : ℝ) + 2) / mu := by positivity
  have hp := shapeTemplatePrefactor_pos (N := (M : ℝ) + 2) hmu
    (by linarith [Nat.cast_nonneg (α := ℝ) M]) (symmetricUpperPrefactor_pos (M + 2))
  have hr1 : r < 1 := by linarith
  have hs : 0 < Real.sqrt (Erdos993Lean.Analytic.V22.gamma r ((M : ℝ) + 2)) :=
    Real.sqrt_pos.2 (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (threeRange_gamma_ge_one hr0 hr1 M))
  have hpu : Real.log (threeRangePU r mu M) =
      Real.log (shapeTemplatePrefactor mu ((M : ℝ) + 2) (symmetricUpperPrefactor (M + 2))) +
        (((M : ℝ) + 3) * Erdos993Lean.Analytic.V22.cr r -
          Erdos993Lean.Analytic.V22.c0Prime r ((M : ℝ) + 2) +
          Erdos993Lean.Analytic.V22.epsilonPrime r ((M : ℝ) + 2) *
            Real.sqrt (Erdos993Lean.Analytic.V22.gamma r ((M : ℝ) + 2)) / 2) := by
    unfold threeRangePU
    rw [Real.log_mul hp.ne' (Real.exp_pos _).ne', Real.log_exp]
  have ht : shapeTemplateLambda mu ((M : ℝ) + 2) (symmetricUpperPrefactor (M + 2)) =
      Real.log (((M : ℝ) + 2) / mu) + Erdos993Lean.Analytic.V22.rho ((M : ℝ) + 2) / 2 -
      Real.log (shapeTemplatePrefactor mu ((M : ℝ) + 2) (symmetricUpperPrefactor (M + 2))) := by
    unfold shapeTemplateLambda
    simpa only [mul_one, Erdos993Lean.Analytic.V22.rho] using
      (threeRange_log_ratio (rho := Erdos993Lean.Analytic.V22.rho ((M : ℝ) + 2))
        (gamma := 1) hp hb)
  unfold threeRangeLambdaU
  rw [threeRange_log_ratio (threeRangePU_pos hmu r M) hb, hpu, ht]
  unfold Erdos993Lean.Analytic.V22.rhoU Erdos993Lean.Analytic.V22.eU
    Erdos993Lean.Analytic.V22.gamma
  unfold Erdos993Lean.Analytic.V22.gamma at hs
  have hsq := Real.sq_sqrt ((Real.sqrt_pos.mp hs).le)
  field_simp [hs.ne'] <;> ring_nf at hsq ⊢ <;> (rw [hsq] <;> ring)

end Erdos993Lean.Analytic.V22.Analysis
