import Erdos993Lean.Analytic.V22.Analysis.WindowTransfer
import Erdos993Lean.Analytic.V22.Checks.LateStatements

/-! Source: note Theorem 5.14, soundness of the exact D3 cell recipes.
The D3 upper recipe drops only the negative -c0Prime term as specified by
the finite interface. This file consumes actual fiber inequalities on every
integer atom; no finite-support substitute or interpolation is introduced.
Parent owns compilation. -/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

private theorem window_upper_cost_comparison {M : ℕ} {r mu Na rm Dlo l : ℝ}
    (hN : 10 ≤ M + 2) (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hmu : 0 < mu)
    (hstar : 0 < V22.rhoStar Na rm)
    (hstarU : V22.rhoStar Na rm ≤ V22.rhoU r ((M : ℝ) + 2))
    (hD : Dlo ≤ V22.Delta r ((M : ℝ) + 2)) (hl : l ≤ threeRangeLambdaU r mu M)
    (j : ℤ) (hw : V22.gamma r ((M : ℝ) + 2) ≤ threeRangeW r M j) :
    (((M : ℝ) + 2) / mu) * (1 + Dlo - 2 / V22.rhoStar Na rm * V22.G (min 0 l)) ≤
      V22.fiberFunction ((1 + r) / 2) mu M j := by
  have hb : 0 < ((M : ℝ) + 2) / mu := by positivity
  have hu := hstar.trans_le hstarU
  have hF := threeRanges_upper hN hr0 hrh hmu j hw
  rw [shared_G_eq]
  by_cases hlam : 0 ≤ threeRangeLambdaU r mu M
  · have hmin := bonusRange_upper_nonneg (threeRangePU_pos hmu r M) hb hu
      (threeRange_gamma_ge_one hr0 (by linarith : r < 1) M) hlam _ hw
    have hcost : 0 ≤ 2 / V22.rhoStar Na rm * rootG (min 0 l) := by
      exact mul_nonneg (by positivity) (rootG_nonneg _)
    have hcmp : 1 + Dlo - 2 / V22.rhoStar Na rm * rootG (min 0 l) ≤
        V22.gamma r ((M : ℝ) + 2) := by unfold V22.gamma; linarith
    exact (mul_le_mul_of_nonneg_left hcmp hb.le).trans (hmin.trans hF)
  · have hn : threeRangeLambdaU r mu M ≤ 0 := by linarith
    have hminNonpos : min 0 l ∈ Iic (0 : ℝ) := min_le_left 0 l
    have hactualNonpos : threeRangeLambdaU r mu M ∈ Iic (0 : ℝ) := hn
    have hG := rootG_antitoneOn_nonpos hminNonpos hactualNonpos ((min_le_right 0 l).trans hl)
    have hi := one_div_le_one_div_of_le hstar hstarU
    have hp := mul_le_mul hi hG (rootG_nonneg _) (by positivity : 0 ≤ 1 / V22.rhoStar Na rm)
    have hscaled : 2 / V22.rhoU r ((M : ℝ) + 2) * rootG (threeRangeLambdaU r mu M) ≤
        2 / V22.rhoStar Na rm * rootG (min 0 l) := by
      convert mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
    have hcmp : 1 + Dlo - 2 / V22.rhoStar Na rm * rootG (min 0 l) ≤
        V22.gamma r ((M : ℝ) + 2) - 2 / V22.rhoU r ((M : ℝ) + 2) * rootG (threeRangeLambdaU r mu M) := by
      unfold V22.gamma
      linarith only [hD, hscaled]
    exact (mul_le_mul_of_nonneg_left hcmp hb.le).trans
      ((rootMinorant_lower_bound (threeRangePU_pos hmu r M) hb hu _ _).trans hF)

theorem window_upper_cell_fiber {M : ℕ} {r ra rb mu Ns Na : ℝ}
    (hra : 0 < ra) (har : ra ≤ r) (hrrb : r ≤ rb) (hrb : rb ≤ 1 / 2)
    (hNs : 10 ≤ Ns) (hsa : Ns ≤ Na) (haN : Na ≤ (M : ℝ) + 2) (hmu : 0 < mu)
    (hguard : 0 < V22.uMonoDerivative r Ns) (j : ℤ)
    (hw : V22.gamma r ((M : ℝ) + 2) ≤ threeRangeW r M j) :
    (((M : ℝ) + 2) / mu) * (1 + V22.Delta ra Na - 2 / V22.rhoStar Na rb *
      V22.G (min 0 (V22.lambdaT ((M : ℝ) / mu) + (71 / 20) / (Na + 1) +
        V22.rhoU r Na * V22.Delta r Na / 2 - (V22.eU r Na + V22.c0Prime r Na)))) ≤
      V22.fiberFunction ((1 + r) / 2) mu M j := by
  have hr : 0 < r := hra.trans_le har
  have hrh := hrrb.trans hrb
  have ha := hNs.trans hsa
  have hNr := ha.trans haN
  have hN : 10 ≤ M + 2 := by exact_mod_cast hNr
  have hphi := (window_phiR_strictMonoOn hr hrh hNs hguard).monotoneOn hsa (hsa.trans haN) haN
  have hlam := window_lambdaU_lower hN hr.le hrh hmu
  have hc0 : 0 ≤ V22.c0Prime r Na := by unfold V22.c0Prime; positivity
  have hl : V22.lambdaT ((M : ℝ) / mu) + (71 / 20) / (Na + 1) +
      V22.rhoU r Na * V22.Delta r Na / 2 - (V22.eU r Na + V22.c0Prime r Na) ≤
        threeRangeLambdaU r mu M := by
    unfold V22.phiR at hphi
    change V22.lambdaT ((M : ℝ) / mu) + V22.phiR r ((M : ℝ) + 2) ≤ _ at hlam
    unfold V22.phiR at hlam
    linarith
  have hD := (window_delta_r_monotone hra.le har hrh (by linarith : 1 ≤ Na)).trans
    (window_delta_N_monotone hr.le hrh (by linarith : 1 ≤ Na) haN)
  have hstar := coefficient_rhoStar_pos ha (hra.le.trans (har.trans hrrb)) hrb
  have hstarU := (coefficient_rhoStar_monotone ha haN (hra.le.trans (har.trans hrrb)) hrb).trans
    (linearized_rhoU_lower hNr hr.le hrrb hrb)
  exact window_upper_cost_comparison hN hr.le hrh hmu hstar hstarU hD hl j hw

theorem window_class_cell_fiber {c : V22.V22Class} {cell : V22.V22Cell} {M : ℕ} {r mu : ℝ}
    (hra : 0 < (c.ra : ℝ)) (har : (c.ra : ℝ) ≤ r) (hrrb : r ≤ (c.rb : ℝ)) (hrb : (c.rb : ℝ) ≤ 1 / 2)
    (hNs : 10 ≤ (c.muD : ℝ) * (c.tau : ℝ) + 2)
    (hsa : (c.muD : ℝ) * (c.tau : ℝ) + 2 ≤ (c.muD : ℝ) * (cell.lo : ℝ) + 2)
    (haN : (c.muD : ℝ) * (cell.lo : ℝ) + 2 ≤ (M : ℝ) + 2) (hmu : 0 < mu)
    (hc : V22.persistentWindowConditions r ((c.muD : ℝ) * (c.tau : ℝ) + 2))
    (hguard : 0 < V22.uMonoDerivative r ((c.muD : ℝ) * (c.tau : ℝ) + 2)) (j : ℤ) :
    (((M : ℝ) + 2) / mu) * V22.Checks.windowCellMinimum c cell ((M : ℝ) / mu) r ≤
      V22.fiberFunction ((1 + r) / 2) mu M j := by
  let Ns : ℝ := (c.muD : ℝ) * (c.tau : ℝ) + 2
  let Na : ℝ := (c.muD : ℝ) * (cell.lo : ℝ) + 2
  let N : ℝ := (M : ℝ) + 2
  have hr0 : 0 ≤ r := (hra.trans_le har).le
  have hrh := hrrb.trans hrb
  have ha : 10 ≤ Na := hNs.trans hsa
  have hNr : 10 ≤ N := ha.trans haN
  have hN : 10 ≤ M + 2 := by
    have hNr' : (10 : ℝ) ≤ (M : ℝ) + 2 := hNr
    exact_mod_cast hNr'
  have hcNa := (window_conditions_persist hr0 hrh hNs hsa hc).1
  have hcN := (window_conditions_persist hr0 hrh hNs (hsa.trans haN) hc).2
  have hDlo : 0 ≤ V22.Delta c.ra Na := delta_nonneg (by linarith)
    (by nlinarith [coefficient_one_sub_rm_sq_pos hra.le (har.trans hrh)])
  have hD := (window_delta_r_monotone hra.le har hrh (by linarith : 1 ≤ Na)).trans
    (window_delta_N_monotone hr0 hrh (by linarith : 1 ≤ Na) haN)
  have hB : 0 ≤ N / mu := by positivity
  have hminL : V22.Checks.windowCellMinimum c cell ((M : ℝ) / mu) r ≤
      V22.Checks.windowCellLower c cell ((M : ℝ) / mu) r := min_le_left _ _
  have hminU : V22.Checks.windowCellMinimum c cell ((M : ℝ) / mu) r ≤
      V22.Checks.windowCellUpper c cell ((M : ℝ) / mu) r := (min_le_right _ _).trans (min_le_right _ _)
  have hmin3 : V22.Checks.windowCellMinimum c cell ((M : ℝ) / mu) r ≤ 3 :=
    (min_le_right _ _).trans (min_le_left _ _)
  by_cases hw : threeRangeW r M j ≤ min 3 (V22.gamma r N)
  · have hlower := window_lower_recipe_le hr0 hrh ha haN hmu hcNa hDlo hD
    change V22.Checks.windowCellLower c cell ((M : ℝ) / mu) r ≤ V22.xL r mu (M + 2) at hlower
    exact (mul_le_mul_of_nonneg_left (hminL.trans hlower) hB).trans
      (window_piece_bound hN hr0 hrh hmu hcN j hw)
  · by_cases hupper : V22.gamma r N ≤ threeRangeW r M j
    · have hu := window_upper_cell_fiber hra har hrrb hrb hNs hsa haN hmu hguard j hupper
      change (N / mu) * V22.Checks.windowCellUpper c cell ((M : ℝ) / mu) r ≤ _ at hu
      exact (mul_le_mul_of_nonneg_left hminU hB).trans hu
    · have hw3 : (3 : ℝ) ≤ threeRangeW r M j := by
        by_contra h
        have h3 : threeRangeW r M j ≤ 3 := by linarith
        exact hw (le_min h3 (by linarith))
      have hm := (threeRanges_middle hN hr0 hrh hmu j
        (by linarith : 1 ≤ threeRangeW r M j) (by linarith : threeRangeW r M j ≤ V22.gamma r N)).1
      exact (mul_le_mul_of_nonneg_left (hmin3.trans hw3) hB).trans hm

end Erdos993Lean.Analytic.V22.Analysis
