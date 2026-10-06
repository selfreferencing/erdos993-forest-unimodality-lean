import Erdos993Lean.Analytic.V22.Analysis.WindowCoefficients

/-! Source: note Theorem 5.14, fixed-cell recipes at a real starting size.
All final fiber comparisons retain the actual integer central amplitude.
The comparisons below discharge the real-size transfer used by the finite
D3 interface; no transfer inequality is added as a final source premise.
Parent owns Lean verification. -/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

noncomputable def windowFrozenLower (t r Na Dlo : ℝ) : ℝ :=
  let Wlo := min 3 (1 + Dlo)
  let lhs := V22.lambdaT t + V22.hbar (Na - 2) + V22.windowEL r Na + V22.windowRhoLbar r Na
  let wc := if 2 ≤ Dlo then lhs ≤ Real.log (1 + V22.rho Na * (Dlo - 2) / 2) else lhs ≤ 0
  let split := 1 - 2 / V22.rho Na * V22.windowGhat t Na +
    Dlo / (1 + V22.windowSbar t r Na + V22.windowRhoLbar r Na * Dlo / 2) -
    2 * V22.windowEL r Na / V22.rho Na
  if wc then Wlo else min Wlo (max split (V22.windowLogAt t r Na))

theorem window_central_start_bounds {M : ℕ} {mu Na : ℝ}
    (ha : 10 ≤ Na) (haN : Na ≤ (M : ℝ) + 2) (hmu : 0 < mu) :
    V22.lambdaT ((M : ℝ) / mu) ≤ V22.lambdaTc mu (M + 2) ∧
    V22.lambdaTc mu (M + 2) ≤ V22.lambdaT ((M : ℝ) / mu) + V22.hbar (Na - 2) ∧
    V22.G (V22.lambdaTc mu (M + 2)) ≤ V22.windowGhat ((M : ℝ) / mu) Na := by
  have hN : 10 ≤ M + 2 := by exact_mod_cast ha.trans haN
  have henv := window_lambdaTc_enclosure hN hmu
  have hh := window_hbar_antitone (show 0 < Na - 2 from by linarith)
    (show Na - 2 ≤ (M : ℝ) from by linarith)
  have hMup : V22.lambdaTc mu (M + 2) ≤
      V22.lambdaT ((M : ℝ) / mu) + V22.hbar (M : ℝ) := by
    have h := henv.2.1.trans henv.2.2
    simpa only [V22.hbar, V22.kbar, shared_lambdaT_eq] using h
  have hupper : V22.lambdaTc mu (M + 2) ≤
      V22.lambdaT ((M : ℝ) / mu) + V22.hbar (Na - 2) := by linarith
  have hlower : V22.lambdaT ((M : ℝ) / mu) ≤ V22.lambdaTc mu (M + 2) := by
    simpa only [shared_lambdaT_eq] using henv.1
  have hconv := rootG_convex.le_max_of_mem_Icc (mem_univ _) (mem_univ _) ⟨hlower, hupper⟩
  refine ⟨hlower, hupper, ?_⟩
  simpa only [V22.windowGhat, V22.Ghat, shared_G_eq] using hconv

theorem window_start_comparisons {M : ℕ} {r mu Na : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (ha : 10 ≤ Na) (haN : Na ≤ (M : ℝ) + 2)
    (hmu : 0 < mu) (hc : V22.persistentWindowConditions r Na) :
    V22.lambdaTc mu (M + 2) + V22.windowEL r ((M : ℝ) + 2) ≤
      V22.lambdaT ((M : ℝ) / mu) + V22.hbar (Na - 2) + V22.windowEL r Na ∧
    V22.rho Na ≤ V22.windowRhoL r ((M : ℝ) + 2) ∧
    V22.windowRhoL r ((M : ℝ) + 2) ≤ V22.windowRhoLbar r Na := by
  have hlam := (window_central_start_bounds ha haN hmu).2.1
  have he := windowEL_antitone hr0 hrh ha haN hc
  have heps := window_epsilon_antitone hr0 (by linarith : r < 1) ha haN
  have heps0 := shared_epsilon_nonneg hr0 (by linarith : r < 1) (show 0 < (M : ℝ) + 2 from by positivity)
  have hrho := coefficient_rho_monotone ha haN
  have hrho1 : V22.rho ((M : ℝ) + 2) ≤ 1 := by
    unfold V22.rho
    apply (div_le_one (by positivity : 0 < (M : ℝ) + 2 + 1)).2
    linarith
  have hepsdiv := div_le_div_of_nonneg_right heps (Real.sqrt_nonneg (3 : ℝ))
  have he0 : 0 ≤ V22.epsilon r ((M : ℝ) + 2) / Real.sqrt 3 :=
    div_nonneg heps0 (Real.sqrt_nonneg _)
  refine ⟨by linarith, ?_, ?_⟩
  · unfold V22.windowRhoL
    linarith
  · unfold V22.windowRhoL V22.windowRhoLbar
    linarith

private theorem window_condition_iff {M : ℕ} {r mu : ℝ} :
    V22.windowCondition r mu (M + 2) ↔
      if 2 ≤ V22.Delta r ((M : ℝ) + 2) then
        V22.lambdaTc mu (M + 2) + V22.windowEL r ((M : ℝ) + 2) +
          V22.windowRhoL r ((M : ℝ) + 2) ≤
          Real.log (1 + V22.windowRhoL r ((M : ℝ) + 2) * (V22.Delta r ((M : ℝ) + 2) - 2) / 2)
      else V22.windowLambdaL r mu (M + 2) ≤ 0 := by
  simp only [V22.windowCondition, Nat.cast_add, Nat.cast_ofNat]
  unfold V22.gamma
  split_ifs with hD
  · rw [min_eq_left (by linarith : (3 : ℝ) ≤ 1 + V22.Delta r ((M : ℝ) + 2))]
    unfold V22.windowLambdaL
    simp only [Nat.cast_add, Nat.cast_ofNat]
    have hid : V22.windowRhoL r ((M : ℝ) + 2) / 2 * (1 + V22.Delta r ((M : ℝ) + 2) - 3) =
        V22.windowRhoL r ((M : ℝ) + 2) * (V22.Delta r ((M : ℝ) + 2) - 2) / 2 := by ring
    rw [hid]
    constructor <;> intro h <;> linarith
  · rw [min_eq_right (by linarith : 1 + V22.Delta r ((M : ℝ) + 2) ≤ (3 : ℝ))]
    simp

theorem window_persistent_condition_transfer {M : ℕ} {r mu Na Dlo : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (ha : 10 ≤ Na) (haN : Na ≤ (M : ℝ) + 2)
    (hmu : 0 < mu) (hc : V22.persistentWindowConditions r Na)
    (hD0 : 0 ≤ Dlo) (hD : Dlo ≤ V22.Delta r ((M : ℝ) + 2))
    (hcondition : if 2 ≤ Dlo then
      V22.lambdaT ((M : ℝ) / mu) + V22.hbar (Na - 2) + V22.windowEL r Na +
        V22.windowRhoLbar r Na ≤ Real.log (1 + V22.rho Na * (Dlo - 2) / 2)
      else V22.lambdaT ((M : ℝ) / mu) + V22.hbar (Na - 2) + V22.windowEL r Na +
        V22.windowRhoLbar r Na ≤ 0) : V22.windowCondition r mu (M + 2) := by
  have hcomp := window_start_comparisons hr0 hrh ha haN hmu hc
  have hR := windowRhoL_pos hr0 (by linarith : r < 1) (show 0 < (M : ℝ) + 2 from by positivity)
  have hRa : 0 < V22.rho Na := by unfold V22.rho; positivity
  apply window_condition_iff.mpr
  by_cases hbig : 2 ≤ V22.Delta r ((M : ℝ) + 2)
  · simp only [if_pos hbig]
    by_cases hlo : 2 ≤ Dlo
    · simp only [if_pos hlo] at hcondition
      have hDlo2 : 0 ≤ Dlo - 2 := sub_nonneg.mpr hlo
      have hprod := mul_le_mul hcomp.2.1 (show Dlo - 2 ≤ V22.Delta r ((M : ℝ) + 2) - 2 from by linarith)
        (by linarith : 0 ≤ Dlo - 2) hR.le
      have hlog := Real.log_le_log (show 0 < 1 + V22.rho Na * (Dlo - 2) / 2 from by positivity)
        (show 1 + V22.rho Na * (Dlo - 2) / 2 ≤
          1 + V22.windowRhoL r ((M : ℝ) + 2) * (V22.Delta r ((M : ℝ) + 2) - 2) / 2 from by linarith)
      linarith
    · simp only [if_neg hlo] at hcondition
      have harg : 1 ≤ 1 + V22.windowRhoL r ((M : ℝ) + 2) *
          (V22.Delta r ((M : ℝ) + 2) - 2) / 2 := by
        have hnonneg := div_nonneg
          (mul_nonneg hR.le (show 0 ≤ V22.Delta r ((M : ℝ) + 2) - 2 from by linarith))
          (by norm_num : (0 : ℝ) ≤ 2)
        linarith
      have hlog : 0 ≤ Real.log (1 + V22.windowRhoL r ((M : ℝ) + 2) *
          (V22.Delta r ((M : ℝ) + 2) - 2) / 2) := Real.log_nonneg harg
      linarith
  · simp only [if_neg hbig]
    have hlo : ¬ 2 ≤ Dlo := by linarith
    simp only [if_neg hlo] at hcondition
    have hprod : V22.windowRhoL r ((M : ℝ) + 2) / 2 * V22.Delta r ((M : ℝ) + 2) ≤
        V22.windowRhoL r ((M : ℝ) + 2) := by nlinarith
    unfold V22.windowLambdaL
    simp only [Nat.cast_add, Nat.cast_ofNat]
    linarith

private theorem window_fraction_monotone {a b c d : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    a / (1 + c + d * a / 2) ≤ b / (1 + c + d * b / 2) := by
  have hb := ha.trans hab
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) (show 0 ≤ 1 + c from by positivity)]

theorem window_split_start_lower {M : ℕ} {r mu Na Dlo : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (ha : 10 ≤ Na) (haN : Na ≤ (M : ℝ) + 2)
    (hmu : 0 < mu) (hc : V22.persistentWindowConditions r Na)
    (hD0 : 0 ≤ Dlo) (hD : Dlo ≤ V22.Delta r ((M : ℝ) + 2)) :
    1 - 2 / V22.rho Na * V22.windowGhat ((M : ℝ) / mu) Na +
        Dlo / (1 + V22.windowSbar ((M : ℝ) / mu) r Na + V22.windowRhoLbar r Na * Dlo / 2) -
        2 * V22.windowEL r Na / V22.rho Na ≤ V22.xSplit r mu (M + 2) := by
  have hN : 10 ≤ M + 2 := by exact_mod_cast ha.trans haN
  have hcN := (window_conditions_persist hr0 hrh ha haN hc).2
  have hcomp := window_start_comparisons hr0 hrh ha haN hmu hc
  have hcentral := window_central_start_bounds ha haN hmu
  have hRa : 0 < V22.rho Na := by unfold V22.rho; positivity
  have hRN : 0 < V22.rho ((M : ℝ) + 2) := by unfold V22.rho; positivity
  have hRhobar : 0 ≤ V22.windowRhoLbar r Na := by
    have he := shared_epsilon_nonneg hr0 (by linarith : r < 1) (show 0 < Na from by linarith)
    unfold V22.windowRhoLbar
    positivity
  have hDel : 0 ≤ V22.Delta r ((M : ℝ) + 2) := hD0.trans hD
  have hSbar : 0 ≤ V22.windowSbar ((M : ℝ) / mu) r Na := le_max_right _ _
  have hshift : V22.positivePart (V22.rootMap (V22.windowLambdaL r mu (M + 2))) ≤
      V22.windowSbar ((M : ℝ) / mu) r Na + V22.windowRhoLbar r Na * V22.Delta r ((M : ℝ) + 2) / 2 := by
    have hbonus := mul_le_mul_of_nonneg_right hcomp.2.2 hDel
    have hlam : V22.windowLambdaL r mu (M + 2) ≤
        V22.lambdaT ((M : ℝ) / mu) + V22.hbar (Na - 2) + V22.windowEL r Na +
          V22.windowRhoLbar r Na * V22.Delta r ((M : ℝ) + 2) / 2 := by
      unfold V22.windowLambdaL
      simp only [Nat.cast_add, Nat.cast_ofNat]
      linarith
    have hs := rootMap_monotone hlam
    have ht := rootMap_shift_le
      (V22.lambdaT ((M : ℝ) / mu) + V22.hbar (Na - 2) + V22.windowEL r Na)
      (V22.windowRhoLbar r Na * V22.Delta r ((M : ℝ) + 2) / 2) (by positivity)
    have hsbar : rootMap (V22.lambdaT ((M : ℝ) / mu) + V22.hbar (Na - 2) + V22.windowEL r Na) ≤
        V22.windowSbar ((M : ℝ) / mu) r Na := by
      simpa only [V22.windowSbar, V22.positivePart, shared_rootMap_eq] using
        le_max_left (rootMap (V22.lambdaT ((M : ℝ) / mu) + V22.hbar (Na - 2) + V22.windowEL r Na)) 0
    have hsbarShift : rootMap (V22.lambdaT ((M : ℝ) / mu) + V22.hbar (Na - 2) + V22.windowEL r Na) +
        V22.windowRhoLbar r Na * V22.Delta r ((M : ℝ) + 2) / 2 ≤
      V22.windowSbar ((M : ℝ) / mu) r Na +
        V22.windowRhoLbar r Na * V22.Delta r ((M : ℝ) + 2) / 2 :=
      add_le_add hsbar le_rfl
    have hrootBound := (hs.trans ht).trans hsbarShift
    have hgain0 : 0 ≤ V22.windowRhoLbar r Na * V22.Delta r ((M : ℝ) + 2) / 2 := by positivity
    simp only [V22.positivePart, shared_rootMap_eq]
    exact max_le hrootBound (add_nonneg hSbar hgain0)
  have hbonus1 := div_le_div_of_nonneg_left hDel
    (show 0 < 1 + V22.positivePart (V22.rootMap (V22.windowLambdaL r mu (M + 2))) from by
      unfold V22.positivePart; positivity)
    (show 1 + V22.positivePart (V22.rootMap (V22.windowLambdaL r mu (M + 2))) ≤
      1 + V22.windowSbar ((M : ℝ) / mu) r Na + V22.windowRhoLbar r Na * V22.Delta r ((M : ℝ) + 2) / 2 from by linarith)
  have hbonus2 := window_fraction_monotone hD0 hD hSbar hRhobar
  have hbonus := hbonus2.trans hbonus1
  have hrho := coefficient_rho_monotone ha haN
  have hGhat0 : 0 ≤ V22.windowGhat ((M : ℝ) / mu) Na := by
    unfold V22.windowGhat V22.Ghat
    rw [shared_G_eq, shared_G_eq]
    exact (rootG_nonneg _).trans (le_max_left _ _)
  have hG := div_le_div₀ hGhat0 hcentral.2.2 hRa hrho
  have heNa := windowEL_nonneg hr0 hrh ha (window_conditions_persist hr0 hrh ha le_rfl hc).2
  have he := div_le_div₀ heNa (windowEL_antitone hr0 hrh ha haN hc) hRa hrho
  have hG2 : 2 / V22.rho ((M : ℝ) + 2) * V22.G (V22.lambdaTc mu (M + 2)) ≤
      2 / V22.rho Na * V22.windowGhat ((M : ℝ) / mu) Na := by
    convert mul_le_mul_of_nonneg_left hG (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
  have he2 : 2 * V22.windowEL r ((M : ℝ) + 2) / V22.rho ((M : ℝ) + 2) ≤
      2 * V22.windowEL r Na / V22.rho Na := by
    convert mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
  unfold V22.xSplit
  simp only [Nat.cast_add, Nat.cast_ofNat]
  exact sub_le_sub (add_le_add (sub_le_sub_left hG2 1) hbonus) he2

theorem window_log_start_lower {M : ℕ} {r mu Na : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (ha : 10 ≤ Na) (haN : Na ≤ (M : ℝ) + 2)
    (hmu : 0 < mu) (hc : V22.persistentWindowConditions r Na) :
    V22.windowLogAt ((M : ℝ) / mu) r Na ≤ V22.xLog r mu (M + 2) := by
  have hcomp := window_start_comparisons hr0 hrh ha haN hmu hc
  have hR := windowRhoL_pos hr0 (by linarith : r < 1) (show 0 < (M : ℝ) + 2 from by positivity)
  have hRa : 0 < V22.rho Na := by unfold V22.rho; positivity
  have hRb : 0 < V22.windowRhoLbar r Na := hR.trans_le hcomp.2.2
  let q := V22.lambdaT ((M : ℝ) / mu) + V22.hbar (Na - 2) + V22.windowEL r Na
  have hq := hcomp.1
  change V22.lambdaTc mu (M + 2) + V22.windowEL r ((M : ℝ) + 2) ≤ q at hq
  unfold V22.windowLogAt V22.xLog
  simp only [Nat.cast_add, Nat.cast_ofNat]
  change (if 0 ≤ q then 1 - 2 * q / V22.rho Na else 1 - 2 * q / V22.windowRhoLbar r Na) ≤ _
  by_cases hq0 : 0 ≤ q
  · rw [if_pos hq0]
    have hdiv := div_le_div₀ hq0 hq hRa hcomp.2.1
    have hdouble : 2 / V22.windowRhoL r ((M : ℝ) + 2) *
        (V22.lambdaTc mu (M + 2) + V22.windowEL r ((M : ℝ) + 2)) ≤ 2 * q / V22.rho Na := by
      convert mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
    exact sub_le_sub_left hdouble 1
  · rw [if_neg hq0]
    have hqa : V22.lambdaTc mu (M + 2) + V22.windowEL r ((M : ℝ) + 2) ≤ 0 := by linarith
    have hcross : (V22.lambdaTc mu (M + 2) + V22.windowEL r ((M : ℝ) + 2)) * V22.windowRhoLbar r Na ≤
        q * V22.windowRhoL r ((M : ℝ) + 2) := by
      have h1 := mul_le_mul_of_nonneg_right hq hRb.le
      have h2 := mul_le_mul_of_nonpos_left hcomp.2.2 (show q ≤ 0 from by linarith)
      exact h1.trans h2
    have hdiv := (div_le_div_iff₀ hR hRb).2 hcross
    have hdouble : 2 / V22.windowRhoL r ((M : ℝ) + 2) *
        (V22.lambdaTc mu (M + 2) + V22.windowEL r ((M : ℝ) + 2)) ≤ 2 * q / V22.windowRhoLbar r Na := by
      convert mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
    exact sub_le_sub_left hdouble 1

theorem window_lower_recipe_le {M : ℕ} {r mu Na Dlo : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (ha : 10 ≤ Na) (haN : Na ≤ (M : ℝ) + 2)
    (hmu : 0 < mu) (hc : V22.persistentWindowConditions r Na)
    (hD0 : 0 ≤ Dlo) (hD : Dlo ≤ V22.Delta r ((M : ℝ) + 2)) :
    windowFrozenLower ((M : ℝ) / mu) r Na Dlo ≤ V22.xL r mu (M + 2) := by
  classical
  have hW : min 3 (1 + Dlo) ≤ min 3 (V22.gamma r ((M : ℝ) + 2)) := by
    apply min_le_min le_rfl
    unfold V22.gamma
    linarith
  let frozenCondition : Prop := if 2 ≤ Dlo then
    V22.lambdaT ((M : ℝ) / mu) + V22.hbar (Na - 2) + V22.windowEL r Na + V22.windowRhoLbar r Na ≤
      Real.log (1 + V22.rho Na * (Dlo - 2) / 2)
    else V22.lambdaT ((M : ℝ) / mu) + V22.hbar (Na - 2) + V22.windowEL r Na + V22.windowRhoLbar r Na ≤ 0
  change (if frozenCondition then min 3 (1 + Dlo) else min (min 3 (1 + Dlo))
    (max (1 - 2 / V22.rho Na * V22.windowGhat ((M : ℝ) / mu) Na +
      Dlo / (1 + V22.windowSbar ((M : ℝ) / mu) r Na + V22.windowRhoLbar r Na * Dlo / 2) -
      2 * V22.windowEL r Na / V22.rho Na) (V22.windowLogAt ((M : ℝ) / mu) r Na))) ≤ _
  by_cases hcond : frozenCondition
  · rw [if_pos hcond]
    have hactual := window_persistent_condition_transfer hr0 hrh ha haN hmu hc hD0 hD hcond
    unfold V22.xL
    rw [if_pos hactual]
    simp only [Nat.cast_add, Nat.cast_ofNat]
    exact hW
  · rw [if_neg hcond]
    have hcap := min_le_left (min 3 (1 + Dlo))
      (max (1 - 2 / V22.rho Na * V22.windowGhat ((M : ℝ) / mu) Na +
        Dlo / (1 + V22.windowSbar ((M : ℝ) / mu) r Na + V22.windowRhoLbar r Na * Dlo / 2) -
        2 * V22.windowEL r Na / V22.rho Na) (V22.windowLogAt ((M : ℝ) / mu) r Na))
    unfold V22.xL
    by_cases hactual : V22.windowCondition r mu (M + 2)
    · rw [if_pos hactual]
      simp only [Nat.cast_add, Nat.cast_ofNat]
      exact hcap.trans hW
    · rw [if_neg hactual]
      exact (min_le_right _ _).trans (max_le_max
        (window_split_start_lower hr0 hrh ha haN hmu hc hD0 hD)
        (window_log_start_lower hr0 hrh ha haN hmu hc))

end Erdos993Lean.Analytic.V22.Analysis
