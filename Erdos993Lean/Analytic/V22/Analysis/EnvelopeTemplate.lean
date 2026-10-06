import Erdos993Lean.Analytic.V22.Analysis.EnvelopeCoverage

/-!
# Exact finite envelope comparison with the proved activity-one template

Source: Theorem4.15's endpoint envelope expression. The only finite inputs
are D7.2 and D7.3. Exact root identities identify its rational expressions
with the shared template; the nonnegative slack is supplied by Lemma3.12.
The envelope start remains `19*t(s_a)` and its radical cap is proved below6.
-/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

theorem envelope_coordinate_le_three {s : ℝ} (hs : -1 < s) (hsU : s ≤ 67 / 100) :
    V22.tOfS s ≤ 3 := by
  rw [shared_tOfS_eq, gaussian_coordinate_exp hs]
  have hLog := Real.log_le_sub_one_of_pos (show 0 < 1 + s by linarith)
  have hArg : (2 / 5 : ℝ) * rootEquation s ≤ 1 := by
    unfold rootEquation
    linarith
  exact (Real.exp_le_exp.mpr hArg).trans Real.exp_one_lt_three.le

theorem envelopeCell_start_coarse_upper {c : ℚ × ℚ} (hc : c ∈ Checks.envelopeCells) :
    19 * V22.tOfS c.1 + 2 ≤ 59 := by
  have hb := envelopeCell_bounds hc
  have h := envelope_coordinate_le_three (by linarith : -1 < (c.1 : ℝ)) (hb.2.1.trans hb.2.2)
  linarith

/-- The initial cap in D7.3 is exactly the uncapped radical it lists. -/
theorem envelopeCell_initial_cap {c : ℚ × ℚ} (hc : c ∈ Checks.envelopeCells) :
    min (6 : ℝ) ((1 / 4 : ℝ) * Real.sqrt (19 * V22.tOfS c.1 + 2)) =
      (1 / 4 : ℝ) * Real.sqrt (19 * V22.tOfS c.1 + 2) := by
  have hUp := envelopeCell_start_coarse_upper hc
  have hLow := (envelopeCell_start_domain hc).2
  have hs := Real.sq_sqrt (show 0 ≤ 19 * V22.tOfS c.1 + 2 by linarith)
  have hs0 := Real.sqrt_nonneg (19 * V22.tOfS c.1 + 2)
  apply min_eq_right
  nlinarith

theorem shared_coordinate_root {s : ℝ} (hs : -1 < s) :
    V22.rootMap (V22.lambdaT (V22.tOfS s)) = s := by
  rw [shared_rootMap_eq, shared_lambdaT_eq, shared_tOfS_eq]
  exact activityOneCoordinate_root hs

/-- Each finite endpoint expression is below its genuine template minus
the exact initial remainder maximum. -/
theorem envelopeExpression_le_template {c : ℚ × ℚ} (hc : c ∈ Checks.envelopeCells)
    (hQ : Checks.lemma_7_2) {s : ℝ} (hs : Checks.inCell c.1 c.2 s) (k : ℝ) :
    Checks.envelopeExpression s (19 * V22.tOfS c.1) k ≤
      V22.templateTerm (V22.tOfS s) (19 * V22.tOfS c.1) k -
        max (V22.dLbar (V22.tOfS s) (19 * V22.tOfS c.1 + 2)
          (19 * V22.tOfS c.1) (1 / 4) ((1 / 4) * Real.sqrt (19 * V22.tOfS c.1 + 2)))
          (if s < 0 then V22.dUbar (V22.tOfS s) (19 * V22.tOfS c.1 + 2)
            (19 * V22.tOfS c.1) (1 / 4) ((1 / 4) * Real.sqrt (19 * V22.tOfS c.1 + 2)) else 0) := by
  have hb := envelopeCell_bounds hc
  have hsL : -(66 / 125 : ℝ) ≤ s := hb.1.trans hs.1
  have hsU : s ≤ 67 / 100 := hs.2.trans hb.2.2
  have hsp : -1 < s := by linarith
  have hM0 := (envelopeCell_start_domain hc).1
  have hRoot := shared_coordinate_root hsp
  have hSlack : (if 0 ≤ s then (19 * V22.tOfS c.1) * s ^ 2 * V22.phi s else 0) ≤
      (19 * V22.tOfS c.1) * V22.gaussianSlack (V22.tOfS s) := by
    split_ifs with hs0
    · have h := mul_le_mul_of_nonneg_left (shared_gaussianSlack_positive hs0 hsU).1 hM0.le
      nlinarith
    · exact mul_nonneg hM0.le (shared_gaussianSlack_coordinate_nonneg hQ hsL hsU)
  have hIdentity : V22.templateTerm (V22.tOfS s) (19 * V22.tOfS c.1) k =
      (19 * V22.tOfS c.1) * V22.gaussianSlack (V22.tOfS s) + 2 -
      6 * s ^ 2 / (1 + s) - 2 * k * s / (1 + s) -
      k ^ 2 / ((1 + s) * (2 + s) * (19 * V22.tOfS c.1 + 3)) := by
    unfold V22.templateTerm V22.G V22.G1 V22.G2
    rw [hRoot]
    field_simp [show 1 + s ≠ 0 by linarith, show 2 + s ≠ 0 by linarith,
      show 19 * V22.tOfS c.1 + 3 ≠ 0 by linarith] <;> ring
  rw [hIdentity]
  unfold Checks.envelopeExpression
  dsimp only
  linarith

/-- The actual initial template bounds the printed remainder maximum;
there is no assumed activity-one envelope comparison. -/
theorem envelope_initial_template_pays (hQ : Checks.lemma_7_2) (hCells : Checks.lemma_7_3)
    {c : ℚ × ℚ} (hc : c ∈ Checks.envelopeCells) {s : ℝ} (hs : Checks.inCell c.1 c.2 s) :
    max (V22.dLbar (V22.tOfS s) (19 * V22.tOfS c.1 + 2)
          (19 * V22.tOfS c.1) (1 / 4) ((1 / 4) * Real.sqrt (19 * V22.tOfS c.1 + 2)))
      (if s < 0 then V22.dUbar (V22.tOfS s) (19 * V22.tOfS c.1 + 2)
          (19 * V22.tOfS c.1) (1 / 4) ((1 / 4) * Real.sqrt (19 * V22.tOfS c.1 + 2)) else 0) ≤
      V22.templateT (V22.tOfS s) (19 * V22.tOfS c.1) := by
  have hData := hCells c hc s hs
  have hEndpoints := hData.2.2.2.2.2
  unfold V22.templateT
  apply le_min
  · have hE := hEndpoints (71 / 20) (by simp)
    have hComp := envelopeExpression_le_template hc hQ hs (71 / 20)
    linarith
  · have hE := hEndpoints (V22.kbar (19 * V22.tOfS c.1)) (by simp)
    have hComp := envelopeExpression_le_template hc hQ hs (V22.kbar (19 * V22.tOfS c.1))
    linarith

end Erdos993Lean.Analytic.V22.Analysis
