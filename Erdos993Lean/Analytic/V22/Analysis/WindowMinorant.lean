import Erdos993Lean.Analytic.V22.Analysis.WindowShape

/-! Source: frozen note Lemma 5.11. The exact native window prefactor has
the shared log ratio `windowLambdaL`, and the range bound uses the original
turning-point condition and both split/logarithmic alternatives. Every actual
integer fiber comparison is retained. Parent owns compilation. -/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

noncomputable def windowPL (r mu : ℝ) (M : ℕ) : ℝ :=
  shapeTemplatePrefactor mu ((M : ℝ) + 2) (V22.centralAmplitude (M + 2)) *
    Real.exp (-V22.c0 r ((M : ℝ) + 2) - V22.quarticError r ((M : ℝ) + 2) 3 -
      V22.epsilon r ((M : ℝ) + 2) * Real.sqrt 3 / 2)

noncomputable def windowMinorant (r mu : ℝ) (M : ℕ) (w : ℝ) : ℝ :=
  rootMinorant (windowPL r mu M) (((M : ℝ) + 2) / mu)
    (V22.windowRhoL r ((M : ℝ) + 2)) (V22.gamma r ((M : ℝ) + 2)) w

theorem windowPL_pos {mu : ℝ} (hmu : 0 < mu) (r : ℝ) (M : ℕ) : 0 < windowPL r mu M := by
  have hN1 : 1 < (M : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) M]
  unfold windowPL
  exact mul_pos (shapeTemplatePrefactor_pos (N := (M : ℝ) + 2) hmu hN1
    (shared_centralAmplitude_pos (M + 2))) (Real.exp_pos _)

theorem windowRhoL_pos {r N : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hN : 0 < N) :
    0 < V22.windowRhoL r N := by
  have he := shared_epsilon_nonneg hr0 hr1 hN
  have hrho : 0 < V22.rho N := by unfold V22.rho; positivity
  unfold V22.windowRhoL
  positivity

theorem windowEL_nonneg {r N : ℝ} (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2)
    (hN : 10 ≤ N) (hc : V22.windowConditions r N) : 0 ≤ V22.windowEL r N := by
  have hn : 0 < N := by linarith
  have hr1 : r < 1 := by linarith
  have hd := shared_one_sub_sq_pos (by linarith : -1 < r) hr1
  have hv := shared_varianceR_pos hr0 hr1
  have hsN : 0 ≤ V22.sN r N := by
    unfold V22.sN
    exact Real.sqrt_nonneg _
  have hZL : 0 ≤ V22.ZL r N 3 := by unfold V22.ZL; positivity
  have hZR : 0 ≤ V22.ZR r N 3 := by unfold V22.ZR; positivity
  have hDL := shared_one_sub_sq_pos (by linarith : -1 < V22.ZL r N 3) hc.1
  have hDR := shared_one_sub_sq_pos (by linarith : -1 < r + V22.ZR r N 3) hc.2.1
  have hE : 0 ≤ V22.quarticError r N 3 := by
    unfold V22.quarticError
    apply le_trans _ (le_max_left _ _)
    positivity
  have hc0 : 0 ≤ V22.c0 r N := by unfold V22.c0; positivity
  have he := shared_epsilon_nonneg hr0 hr1 hn
  unfold V22.windowEL
  positivity

/-- The native window amplitude has exactly the source's shared log ratio. -/
theorem window_minorant_lambda_eq {M : ℕ} {mu : ℝ} (hmu : 0 < mu) (r : ℝ) :
    Real.log ((((M : ℝ) + 2) / mu) *
      Real.exp (V22.windowRhoL r ((M : ℝ) + 2) * V22.gamma r ((M : ℝ) + 2) / 2) /
        windowPL r mu M) = V22.windowLambdaL r mu (M + 2) := by
  have hb : 0 < ((M : ℝ) + 2) / mu := by positivity
  have hN1 : 1 < (M : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) M]
  have hp := shapeTemplatePrefactor_pos (N := (M : ℝ) + 2) hmu hN1
    (shared_centralAmplitude_pos (M + 2))
  have hs : Real.sqrt (3 : ℝ) ≠ 0 := by positivity
  unfold V22.windowLambdaL
  rw [shared_lambdaTc_eq]
  simp only [Nat.cast_add, Nat.cast_ofNat]
  unfold windowPL shapeTemplateLambda
  simp (disch := first | positivity | exact hp.ne') only [Real.log_div, Real.log_mul, Real.log_exp]
  unfold V22.windowRhoL V22.gamma V22.windowEL V22.rho
  field_simp [hs] <;> ring

private theorem window_abs_tangent (x : ℝ) : |x| ≤ (x ^ 2 + 3) / (2 * Real.sqrt 3) := by
  have hs : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  apply (le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt (3 : ℝ))).2
  nlinarith [sq_nonneg (|x| - Real.sqrt 3), sq_abs x]

/-- Lemma 5.11's actual-fiber minorant, under exactly its shape conditions. -/
theorem window_minorant_fiber {M : ℕ} (hN : 10 ≤ M + 2) {r mu : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hmu : 0 < mu)
    (hc : V22.windowConditions r ((M : ℝ) + 2)) (j : ℤ)
    (hw : threeRangeW r M j ≤ min 3 (V22.gamma r ((M : ℝ) + 2))) :
    windowMinorant r mu M (threeRangeW r M j) ≤ V22.fiberFunction ((1 + r) / 2) mu M j := by
  have hr1 : r < 1 := by linarith
  have hn : 0 < (M : ℝ) + 2 := by positivity
  have heps := shared_epsilon_nonneg hr0 hr1 hn
  have hw3 := hw.trans (min_le_left _ _)
  have hmass := (window_shape_bound hN hr0 hrh (by simpa only [Nat.cast_add, Nat.cast_ofNat] using hc)
    (j + 1) hw3).2
  simp only [Nat.cast_add, Nat.cast_ofNat] at hmass
  change Real.exp (_) ≤ threeRangeMass r M j at hmass
  have ht := mul_le_mul_of_nonneg_left (window_abs_tangent (sharedGaussianX r (M + 2) (j + 1))) heps
  have hs : Real.sqrt (3 : ℝ) ≠ 0 := by positivity
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hexact : -V22.windowRhoL r ((M : ℝ) + 2) * threeRangeW r M j / 2 -
      V22.c0 r ((M : ℝ) + 2) - V22.quarticError r ((M : ℝ) + 2) 3 -
      V22.epsilon r ((M : ℝ) + 2) * Real.sqrt 3 / 2 =
    -V22.rho ((M : ℝ) + 2) / 2 * threeRangeW r M j -
      V22.epsilon r ((M : ℝ) + 2) * ((threeRangeW r M j + 3) / (2 * Real.sqrt 3)) -
      V22.c0 r ((M : ℝ) + 2) - V22.quarticError r ((M : ℝ) + 2) 3 := by
    unfold V22.windowRhoL
    field_simp [hs]
    ring_nf
    rw [hsq]
    ring
  have hexp : Real.exp (-V22.windowRhoL r ((M : ℝ) + 2) * threeRangeW r M j / 2 -
      V22.c0 r ((M : ℝ) + 2) - V22.quarticError r ((M : ℝ) + 2) 3 -
      V22.epsilon r ((M : ℝ) + 2) * Real.sqrt 3 / 2) ≤ threeRangeMass r M j := by
    rw [hexact]
    apply le_trans (Real.exp_le_exp.mpr ?_) hmass
    unfold threeRangeW
    linarith
  have hN1 : 1 < (M : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) M]
  have hp := (shapeTemplatePrefactor_pos (N := (M : ℝ) + 2) hmu hN1
    (shared_centralAmplitude_pos (M + 2))).le
  have hcoef : windowPL r mu M * Real.exp (-V22.windowRhoL r ((M : ℝ) + 2) * threeRangeW r M j / 2) ≤
      shapeTemplatePrefactor mu ((M : ℝ) + 2) (V22.centralAmplitude (M + 2)) * threeRangeMass r M j := by
    convert mul_le_mul_of_nonneg_left hexp hp using 1
    unfold windowPL
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have h := mul_le_mul_of_nonneg_right hcoef (sub_nonneg.mpr (hw.trans (min_le_right _ _)))
  rw [threeRange_fiber_eq hr0 hr1 hmu]
  unfold windowMinorant rootMinorant
  nlinarith

private theorem window_split_algebra {lambda0 lambda rho rhoL Delta e : ℝ}
    (hrho : 0 < rho) (hrhoL : 0 < rhoL) (hrr : rho ≤ rhoL)
    (hD : 0 ≤ Delta) (he : 0 ≤ e) (hl : 0 < lambda)
    (heq : lambda = lambda0 + (rhoL / 2 * Delta + e)) :
    1 - 2 / rho * rootG lambda0 + Delta / (1 + max (rootMap lambda) 0) - 2 * e / rho ≤
      1 + Delta - 2 / rhoL * rootG lambda := by
  have hs := (rootMap_nonneg_le hl.le).1
  have hsig0 := rootGPrime_nonneg hl.le
  have hsig1 := (rootGPrime_lt_one lambda).le
  have ht := rootG_bonus_split lambda0 Delta e rhoL hrhoL hD
  dsimp only at ht
  rw [← heq] at ht
  have hi := one_div_le_one_div_of_le hrho hrr
  have hG := mul_le_mul_of_nonneg_right hi (rootG_nonneg lambda0)
  have hsig := mul_le_mul_of_nonneg_left hsig1 he
  have hsdiv : e * rootGPrime lambda / rhoL ≤ e / rhoL := by
    simpa only [mul_one] using div_le_div_of_nonneg_right hsig hrhoL.le
  have he1 : e * rootGPrime lambda / rhoL ≤ e / rho :=
    hsdiv.trans (div_le_div_of_nonneg_left he hrho hrr)
  have hbonus : Delta * (1 - rootGPrime lambda) = Delta / (1 + max (rootMap lambda) 0) := by
    rw [max_eq_left hs]
    unfold rootGPrime
    field_simp [ne_of_gt (by linarith : 0 < 1 + rootMap lambda)] <;> ring
  rw [hbonus] at ht
  have hG2 : 2 / rhoL * rootG lambda0 ≤ 2 / rho * rootG lambda0 := by
    convert mul_le_mul_of_nonneg_left hG (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
  have he2 : 2 / rhoL * e * rootGPrime lambda ≤ 2 * e / rho := by
    convert mul_le_mul_of_nonneg_left he1 (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
  calc
    1 - 2 / rho * rootG lambda0 + Delta / (1 + max (rootMap lambda) 0) - 2 * e / rho ≤
        1 - 2 / rhoL * rootG lambda0 + Delta / (1 + max (rootMap lambda) 0) -
          2 / rhoL * e * rootGPrime lambda :=
      sub_le_sub (add_le_add (sub_le_sub_left hG2 1)
        (le_refl (Delta / (1 + max (rootMap lambda) 0)))) he2
    _ ≤ 1 + Delta - 2 / rhoL * rootG lambda := ht

/-- Lemma 5.11: the full real-window minimum bound, with its exact branch. -/
theorem window_minorant_bound {M : ℕ} (hN : 10 ≤ M + 2) {r mu : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hmu : 0 < mu)
    (hc : V22.windowConditions r ((M : ℝ) + 2)) (w : ℝ) (_hw0 : 0 ≤ w)
    (hw1 : w ≤ min 3 (V22.gamma r ((M : ℝ) + 2))) :
    (((M : ℝ) + 2) / mu) * V22.xL r mu (M + 2) ≤ windowMinorant r mu M w := by
  let N : ℝ := (M : ℝ) + 2
  let rhoL := V22.windowRhoL r N
  let W := min 3 (V22.gamma r N)
  let lambda := V22.windowLambdaL r mu (M + 2)
  let y := rhoL / 2 * (V22.gamma r N - W)
  have hNr : 10 ≤ N := by dsimp [N]; exact_mod_cast hN
  have hn : 0 < N := by linarith
  have hr1 : r < 1 := by linarith
  have hrL : 0 < rhoL := windowRhoL_pos hr0 hr1 hn
  have hb : 0 < N / mu := by positivity
  have hp := windowPL_pos hmu r M
  have hD := delta_nonneg (by linarith : 1 ≤ N) (by nlinarith : r ^ 2 < 1)
  have he := windowEL_nonneg hr0 hrh hNr hc
  have hrho : 0 < V22.rho N := by unfold V22.rho; positivity
  have heps := shared_epsilon_nonneg hr0 hr1 hn
  have hrr : V22.rho N ≤ rhoL := by
    have h : 0 ≤ V22.epsilon r N / Real.sqrt 3 := by positivity
    dsimp [rhoL, V22.windowRhoL]
    linarith
  have hy : 0 ≤ y := by dsimp [y]; exact mul_nonneg (by positivity) (sub_nonneg.mpr (min_le_right _ _))
  have hlambda := window_minorant_lambda_eq (M := M) hmu r
  have heq : lambda = V22.lambdaTc mu (M + 2) + (rhoL / 2 * V22.Delta r N + V22.windowEL r N) := by
    dsimp [lambda, V22.windowLambdaL, rhoL, N]
    simp only [Nat.cast_add, Nat.cast_ofNat]
    ring
  unfold V22.xL
  split_ifs with hcond
  · have hl : lambda ≤ y + Real.log (1 + y) := by
      simpa only [V22.windowCondition, Nat.cast_add, Nat.cast_ofNat] using hcond
    have hyroot : rootMap (y + Real.log (1 + y)) = y :=
      rootMap_eq_of_equation (by linarith) rfl
    have hs : rootMap lambda ≤ y := by simpa only [hyroot] using rootMap_monotone hl
    have harg : W ≤ rootMinorantArgmin rhoL (V22.gamma r N) (rootMap lambda) := by
      unfold rootMinorantArgmin
      dsimp [y] at hs
      apply (le_sub_iff_add_le).2
      have h := (div_le_iff₀ hrL).2 (show 2 * rootMap lambda ≤ (V22.gamma r N - W) * rhoL by nlinarith)
      linarith
    have hrootEquation : rootEquation (rootMap lambda) =
        Real.log (N / mu * Real.exp (rhoL * V22.gamma r N / 2) / windowPL r mu M) := by
      calc
        rootEquation (rootMap lambda) = lambda := rootMap_equation lambda
        _ = Real.log (N / mu * Real.exp (rhoL * V22.gamma r N / 2) / windowPL r mu M) := hlambda.symm
    have hm := (rootMinorant_monotonicity_of_root (gamma := V22.gamma r N)
      hp hb hrL (rootMap_gt_neg_one lambda) hrootEquation).1
    have h := hm (show w ∈ Iic (rootMinorantArgmin rhoL (V22.gamma r N) (rootMap lambda)) by exact hw1.trans harg)
      (show W ∈ Iic (rootMinorantArgmin rhoL (V22.gamma r N) (rootMap lambda)) by exact harg) hw1
    have hW : (N / mu) * W ≤ rootMinorant (windowPL r mu M) (N / mu) rhoL (V22.gamma r N) W := by
      have hterm : 0 ≤ windowPL r mu M * (V22.gamma r N - W) * Real.exp (-rhoL * W / 2) :=
        mul_nonneg (mul_nonneg hp.le (sub_nonneg.mpr (min_le_right _ _)))
          (Real.exp_pos (-rhoL * W / 2)).le
      unfold rootMinorant
      linarith
    simpa only [Nat.cast_add, Nat.cast_ofNat, windowMinorant] using hW.trans h
  · have hl : y + Real.log (1 + y) < lambda := by
      have h : ¬lambda ≤ y + Real.log (1 + y) := by
        simpa only [V22.windowCondition, Nat.cast_add, Nat.cast_ofNat] using hcond
      exact lt_of_not_ge h
    have hl0 : 0 < lambda := by linarith [Real.log_nonneg (show 1 ≤ 1 + y by linarith)]
    have hmin := rootMinorant_lower_bound hp hb hrL (V22.gamma r N) w
    rw [hlambda] at hmin
    have hsplit := window_split_algebra hrho hrL hrr hD he hl0 heq
    have hsplitShared : V22.xSplit r mu (M + 2) ≤ V22.gamma r N - 2 / rhoL * rootG lambda := by
      simpa only [V22.xSplit, Nat.cast_add, Nat.cast_ofNat, shared_G_eq,
        shared_rootMap_eq, V22.positivePart, V22.gamma] using hsplit
    have hG := rootG_le_lambda_sub_log hl0.le
    have hscaled := mul_le_mul_of_nonneg_left hG (show 0 ≤ 2 / rhoL by positivity)
    have hlog := Real.log_nonneg (show 1 ≤ 1 + lambda by linarith)
    have hid : V22.gamma r N - 2 / rhoL * lambda =
        1 - 2 / rhoL * (V22.lambdaTc mu (M + 2) + V22.windowEL r N) := by
      rw [heq]
      unfold V22.gamma
      field_simp [hrL.ne'] <;> ring
    have hlogShared : V22.xLog r mu (M + 2) ≤ V22.gamma r N - 2 / rhoL * rootG lambda := by
      simp only [V22.xLog, Nat.cast_add, Nat.cast_ofNat]
      have h := mul_nonneg (show 0 ≤ 2 / rhoL by positivity) hlog
      nlinarith
    have hx := max_le hsplitShared hlogShared
    have hbound := mul_le_mul_of_nonneg_left hx hb.le
    simpa only [Nat.cast_add, Nat.cast_ofNat, windowMinorant] using hbound.trans hmin

/-- The full source window piece applied to every actual integer atom. -/
theorem window_piece_bound {M : ℕ} (hN : 10 ≤ M + 2) {r mu : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hmu : 0 < mu)
    (hc : V22.windowConditions r ((M : ℝ) + 2)) (j : ℤ)
    (hw : threeRangeW r M j ≤ min 3 (V22.gamma r ((M : ℝ) + 2))) :
    (((M : ℝ) + 2) / mu) * V22.xL r mu (M + 2) ≤ V22.fiberFunction ((1 + r) / 2) mu M j := by
  exact (window_minorant_bound hN hr0 hrh hmu hc _ (sq_nonneg _) hw).trans
    (window_minorant_fiber hN hr0 hrh hmu hc j hw)

end Erdos993Lean.Analytic.V22.Analysis
