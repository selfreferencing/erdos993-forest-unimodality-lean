import Erdos993Lean.Analytic.V22.Analysis.LargeNuUpper
import Erdos993Lean.Analytic.V22.Analysis.BonusRangeBounds
import Erdos993Lean.Analytic.V22.Checks.EarlyStatements
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Paper v2.2, Lemma 4.13: the bonus preserves the activity log bound

The exact finite `bonusConditions` certify the pre-cap derivative and the
fixed-coefficient tail. Continuity of the actual function is proved here;
nonzero certified derivatives supply interior differentiability. The native
fiber conclusions retain `M`, `mu`, `r` and every integer index.
-/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

private theorem lambdaBonus_continuousAt {N rm : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ rm) (hrh : rm ≤ 1 / 2) :
    ContinuousAt (fun n => V22.lambdaBonusF n rm) N := by
  have hn : 0 < N := by linarith
  have hn1 : 0 < N + 1 := by linarith
  have hd := coefficient_one_sub_rm_sq_pos hr0 hrh
  have hc : 0 < V22.cCoef N := by linarith [(coefficient_cCoef_bounds hN).1]
  have hs := Real.sqrt_pos.2 hc
  have hcdirect : 0 < 1 - 1 / N := by simpa only [V22.cCoef] using hc
  have hsdirect : 0 < Real.sqrt (1 - 1 / N) := Real.sqrt_pos.2 hcdirect
  unfold V22.lambdaBonusF V22.E2 V22.e2 V22.e3 V22.e4 V22.e5
    V22.rhoStar V22.rho V22.cCoef
  fun_prop (disch := positivity)

/-- Positivity of the exact `f(N)` over the entire pre-cap interval. -/
theorem lambdaBonus_pre_cap_pos {rm Nlo N : ℝ}
    (hc : V22.Checks.bonusConditions rm Nlo) (hrp : 0 < rm) (hrh : rm ≤ 1 / 2)
    (hlo : 10 ≤ Nlo) (hNlo : Nlo ≤ N) (hNcap : N ≤ (6 / rm) ^ 2) :
    0 < V22.lambdaBonusF N rm := by
  have hcont : ContinuousOn (fun n => V22.lambdaBonusF n rm) (Icc Nlo ((6 / rm) ^ 2)) := by
    intro n hn
    exact (lambdaBonus_continuousAt (hlo.trans hn.1) hrp.le hrh).continuousWithinAt
  have hderiv (n : ℝ) (hn : n ∈ interior (Icc Nlo ((6 / rm) ^ 2))) :
      0 < deriv (fun n => V22.lambdaBonusF n rm) n := by
    have hni : Nlo < n ∧ n < (6 / rm) ^ 2 := by simpa only [interior_Icc, mem_Ioo] using hn
    have hd := hc.2.2.1 n ⟨hni.1.le, hni.2.le⟩
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hni.1 hni.2)] at hd
    exact hc.2.1.trans_le hd
  have hmono : MonotoneOn (fun n => V22.lambdaBonusF n rm) (Icc Nlo ((6 / rm) ^ 2)) :=
    monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcont
      (fun n hn => (differentiableAt_of_deriv_ne_zero (hderiv n hn).ne').differentiableWithinAt)
      (fun n hn => (hderiv n hn).le)
  exact hc.1.trans_le (hmono ⟨le_rfl, hNlo.trans hNcap⟩ ⟨hNlo, hNcap⟩ hNlo)

theorem lambdaBonus_E2_antitone {N M rm nm : ℝ} (hN : 10 ≤ N) (hNM : N ≤ M) :
    V22.E2 M rm nm ≤ V22.E2 N rm nm := by
  have h := mul_le_mul_of_nonneg_right (coefficient_e4_antitone (rm := rm) hN hNM) (sq_nonneg nm)
  unfold V22.E2
  linarith

theorem lambdaBonus_cap_identity {rm : ℝ} (hrp : 0 < rm) :
    rm * Real.sqrt ((6 / rm) ^ 2) = (6 : ℝ) := by
  rw [Real.sqrt_sq (by positivity : 0 ≤ (6 : ℝ) / rm)]
  field_simp [hrp.ne']

/-- Positivity of `f` beyond the cap, using the source's fixed tail. -/
theorem lambdaBonus_tail_pos {rm Nlo N : ℝ}
    (hc : V22.Checks.bonusConditions rm Nlo) (hrp : 0 < rm) (hrh : rm ≤ 1 / 2)
    (hNcap : (6 / rm) ^ 2 ≤ N) : 0 < V22.lambdaBonusF N rm := by
  let Nc : ℝ := (6 / rm) ^ 2
  have hNc144 : (144 : ℝ) ≤ Nc := by
    have hdiv : (12 : ℝ) ≤ 6 / rm := (le_div_iff₀ hrp).2 (by linarith)
    dsimp [Nc]
    nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 6) hrp.le]
  have hNc : 10 ≤ Nc := by linarith
  have hn : 0 < N := by linarith
  have hnm : 0 ≤ N - 1 := by linarith
  have hroot := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hNcap) hrp.le
  rw [lambdaBonus_cap_identity hrp] at hroot
  have hmin : min (6 : ℝ) (rm * Real.sqrt N) = 6 := min_eq_left hroot
  have hRho := coefficient_rhoStar_monotone hNc hNcap hrp.le hrh
  have hE := lambdaBonus_E2_antitone (rm := rm) (nm := 6) hNc hNcap
  have hprod := mul_le_mul_of_nonneg_left hRho
    (show 0 ≤ N * (N - 1) / 2 by positivity)
  have hEprod := mul_le_mul_of_nonneg_left hE hn.le
  have htail := hc.2.2.2.2.2.1 N hNcap
  have hbound : V22.Checks.bonusTail rm N ≤ N * V22.lambdaBonusF N rm := by
    calc
      _ = N * (N - 1) / 2 * V22.rhoStar Nc rm - N * V22.E2 Nc rm 6 -
          (N + 1) / (71 / 20 : ℝ) := by
        unfold V22.Checks.bonusTail
        dsimp [Nc]
        ring
      _ ≤ N * (N - 1) / 2 * V22.rhoStar N rm - N * V22.E2 N rm 6 -
          (N + 1) / (71 / 20 : ℝ) := by
        linarith only [hprod, hEprod]
      _ = _ := by
        unfold V22.lambdaBonusF
        rw [hmin]
        field_simp [hn.ne'] <;> ring
  have hpositive : 0 < N * V22.lambdaBonusF N rm := htail.trans_le hbound
  exact (mul_pos_iff_of_pos_left hn).1 hpositive

/-- The exact all-real-`N` coefficient check used by the native consumer. -/
theorem lambdaBonus_f_pos {rm Nlo N : ℝ}
    (hc : V22.Checks.bonusConditions rm Nlo) (hrp : 0 < rm) (hrh : rm ≤ 1 / 2)
    (hlo : 10 ≤ Nlo) (hNlo : Nlo ≤ N) : 0 < V22.lambdaBonusF N rm := by
  rcases le_total N ((6 / rm) ^ 2) with h | h
  · exact lambdaBonus_pre_cap_pos hc hrp hrh hlo hNlo h
  · exact lambdaBonus_tail_pos hc hrp hrh h

/-- The bounded higher powers are paid by the exact source `E2`. -/
theorem lambdaBonus_E_capped {N rm nu nm : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ rm) (hrh : rm ≤ 1 / 2) (hnu : 0 ≤ nu) (hcap : nu ≤ nm) :
    V22.E N rm nu ≤ 2 * nu + V22.E2 N rm nm * nu ^ 2 := by
  have hnm : 0 ≤ nm := hnu.trans hcap
  have hn : 0 < N := by linarith
  have hd := coefficient_one_sub_rm_sq_pos hr0 hrh
  have he3 : 0 ≤ V22.e3 rm := by unfold V22.e3; positivity
  have he4 : 0 ≤ V22.e4 N rm := by unfold V22.e4; positivity
  have he5 : 0 ≤ V22.e5 rm := by unfold V22.e5; positivity
  have hp2 := pow_le_pow_left₀ hnu hcap 2
  have hp3 := pow_le_pow_left₀ hnu hcap 3
  have h3 := mul_le_mul_of_nonneg_left hcap (mul_nonneg he3 (sq_nonneg nu))
  have h4 := mul_le_mul_of_nonneg_left hp2 (mul_nonneg he4 (sq_nonneg nu))
  have h5 := mul_le_mul_of_nonneg_left hp3 (mul_nonneg he5 (sq_nonneg nu))
  unfold V22.E V22.E2
  nlinarith only [h3, h4, h5]

private theorem lambdaBonus_quadratic {N q nu : ℝ} (hN : 0 < N)
    (hq : (N + 1) / ((71 / 20 : ℝ) * N ^ 2) ≤ q) :
    0 ≤ (71 / 20 : ℝ) / (N + 1) + q * nu ^ 2 - 2 * nu / N := by
  have hmul := mul_le_mul_of_nonneg_right hq (sq_nonneg nu)
  have hid : (71 / 20 : ℝ) / (N + 1) +
      (N + 1) / ((71 / 20 : ℝ) * N ^ 2) * nu ^ 2 - 2 * nu / N =
      ((71 / 20 : ℝ) * N - (N + 1) * nu) ^ 2 /
        ((71 / 20 : ℝ) * N ^ 2 * (N + 1)) := by
    field_simp [hN.ne', (show N + 1 ≠ 0 by linarith)]; ring
  have hzero : 0 ≤ (71 / 20 : ℝ) / (N + 1) +
      (N + 1) / ((71 / 20 : ℝ) * N ^ 2) * nu ^ 2 - 2 * nu / N := by
    rw [hid]
    positivity
  linarith

/-- Lemma 4.13 for the genuine native upper template, assuming precisely
its finite source conditions and no additional analytic bound. -/
theorem lambdaBonus_source {M : ℕ} {r rm mu Nlo : ℝ}
    (hc : V22.Checks.bonusConditions rm Nlo) (hrm : 0 < rm) (hrmh : rm ≤ 1 / 2)
    (hlo : 10 ≤ Nlo) (hNlo : Nlo ≤ (M : ℝ) + 2)
    (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hmu : 0 < mu) :
    V22.lambdaT ((M : ℝ) / mu) ≤ threeRangeLambdaU r mu M := by
  let N : ℝ := (M : ℝ) + 2
  let nu := activityNu r N
  let nm := min (6 : ℝ) (rm * Real.sqrt N)
  let q := V22.rhoStar N rm * (N - 1) / (2 * N) - V22.E2 N rm nm / N
  have hN : 10 ≤ N := hlo.trans hNlo
  have hNN : 10 ≤ M + 2 := by
    have hNr : (10 : ℝ) ≤ (M : ℝ) + 2 := hN
    exact_mod_cast hNr
  have hn : 0 < N := by linarith
  have hnu0 : 0 ≤ nu := activityNu_nonneg hr0
  by_cases hlarge : 6 ≤ nu
  · have hg := largeNu_upper_source hNN hr0 (hrrm.trans hrmh) hlarge hmu
    exact le_trans (by nlinarith [sq_nonneg nu]) hg
  · have hnu6 : nu ≤ 6 := by linarith
    have hnum : nu ≤ rm * Real.sqrt N := by
      dsimp [nu, activityNu]
      exact mul_le_mul_of_nonneg_right hrrm (Real.sqrt_nonneg N)
    have hcap : nu ≤ nm := le_min hnu6 hnum
    have hf := (lambdaBonus_f_pos hc hrm hrmh hlo hNlo).le
    have hq : (N + 1) / ((71 / 20 : ℝ) * N ^ 2) ≤ q := by
      dsimp [q, nm, N]
      unfold V22.lambdaBonusF at hf
      apply (div_le_iff₀ (by positivity : 0 < (71 / 20 : ℝ) * ((M : ℝ) + 2) ^ 2)).2
      field_simp [(show (M : ℝ) + 2 ≠ 0 by positivity)] at hf ⊢
      nlinarith only [hf]
    have hquad := lambdaBonus_quadratic hn hq (nu := nu)
    have hU := linearized_rhoU_lower hN hr0 hrrm hrmh
    have hstar := coefficient_rhoStar_pos hN hrm.le hrmh
    have hdelta := scaled_delta_lower hN (show r ^ 2 < 1 by
      nlinarith [(coefficient_rm_sq_bounds hr0 (hrrm.trans hrmh)).2.1])
    have hdeltalo : (N - 1) / N * nu ^ 2 ≤ V22.Delta r N := by
      have hdiv : (N - 1) * nu ^ 2 / N ≤ V22.Delta r N := by
        apply (div_le_iff₀ hn).2
        nlinarith only [hdelta]
      convert hdiv using 1 <;> ring
    have hdelta0 := delta_nonneg (by linarith : 1 ≤ N)
      (show r ^ 2 < 1 by nlinarith [(coefficient_rm_sq_bounds hr0 (hrrm.trans hrmh)).2.1])
    have hprod := mul_le_mul hU hdeltalo
      (mul_nonneg (div_nonneg (by linarith : 0 ≤ N - 1) hn.le) (sq_nonneg nu))
      (hstar.trans_le hU).le
    have hE := (linearized_eU_upper hN hr0 hrrm hrmh).trans
      (lambdaBonus_E_capped hN hrm.le hrmh hnu0 hcap)
    have he : V22.eU r N ≤ (2 * nu + V22.E2 N rm nm * nu ^ 2) / N := by
      apply (le_div_iff₀ hn).2
      nlinarith only [hE]
    have hk := (activityOneK_bounds (by omega : 8 ≤ M) ActivityOneSide.U).1
    have hks := div_le_div_of_nonneg_right hk (show 0 ≤ (M : ℝ) + 3 by positivity)
    have htshift := activityOneLambda_shift (by omega : 1 ≤ M) hmu ActivityOneSide.U
    have ht : V22.lambdaT ((M : ℝ) / mu) + (71 / 20 : ℝ) / (N + 1) ≤
        activityOneLambda M mu ActivityOneSide.U := by
      have hden : N + 1 = (M : ℝ) + 3 := by dsimp [N]; ring
      rw [hden]
      change activityOneLambda_t ((M : ℝ) / mu) + (71 / 20 : ℝ) / ((M : ℝ) + 3) ≤ _
      rw [htshift]
      exact add_le_add le_rfl hks
    rw [threeRanges_lambdaU_eq hNN hr0 (hrrm.trans hrmh) hmu]
    change V22.lambdaT ((M : ℝ) / mu) ≤ activityOneLambda M mu .U +
      V22.rhoU r N / 2 * V22.Delta r N - V22.eU r N
    dsimp [q] at hquad
    have hprodHalf : V22.rhoStar N rm * (N - 1) / (2 * N) * nu ^ 2 ≤
        V22.rhoU r N / 2 * V22.Delta r N := by
      have hhalf := div_le_div_of_nonneg_right hprod (by norm_num : (0 : ℝ) ≤ 2)
      convert hhalf using 1 <;> field_simp [hn.ne'] <;> ring
    have hquadExact : 0 ≤ (71 / 20 : ℝ) / (N + 1) +
        V22.rhoStar N rm * (N - 1) / (2 * N) * nu ^ 2 -
          (2 * nu + V22.E2 N rm nm * nu ^ 2) / N := by
      convert hquad using 1 <;> ring
    have hpaid : V22.rhoStar N rm * (N - 1) / (2 * N) * nu ^ 2 -
        (2 * nu + V22.E2 N rm nm * nu ^ 2) / N ≤
          V22.rhoU r N / 2 * V22.Delta r N - V22.eU r N := by
      linarith only [hprodHalf, he]
    have hgain : 0 ≤ (71 / 20 : ℝ) / (N + 1) +
        V22.rhoU r N / 2 * V22.Delta r N - V22.eU r N := by
      linarith only [hquadExact, hpaid]
    linarith only [ht, hgain]

/-- The source derivative control in the negative upper branch. -/
theorem lambdaBonus_sigma_bound {M : ℕ} {r rm mu Nlo : ℝ}
    (hc : V22.Checks.bonusConditions rm Nlo) (hrm : 0 < rm) (hrmh : rm ≤ 1 / 2)
    (hlo : 10 ≤ Nlo) (hNlo : Nlo ≤ (M : ℝ) + 2)
    (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hmu : 0 < mu) (hl : threeRangeLambdaU r mu M < 0) :
    |rootGPrime (threeRangeLambdaU r mu M)| ≤ |V22.G1 (V22.lambdaT ((M : ℝ) / mu))| := by
  have hcomp := lambdaBonus_source hc hrm hrmh hlo hNlo hr0 hrrm hmu
  have hderiv := rootGPrime_strictMono.monotone hcomp
  have hsig := bonusRange_upper_sigma_negative hl
  have hbase : rootGPrime (V22.lambdaT ((M : ℝ) / mu)) < 0 := lt_of_le_of_lt hderiv hsig
  rw [shared_G1_eq, abs_of_neg hsig, abs_of_neg hbase]
  linarith

/-- The source's two-unit native upper-range consequence for `t>=1`. -/
theorem lambdaBonus_upper_fiber {M : ℕ} {r rm mu Nlo : ℝ}
    (hc : V22.Checks.bonusConditions rm Nlo) (hrm : 0 < rm) (hrmh : rm ≤ 1 / 2)
    (hlo : 10 ≤ Nlo) (hNlo : Nlo ≤ (M : ℝ) + 2)
    (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hmu : 0 < mu) (ht : (1 : ℝ) ≤ (M : ℝ) / mu)
    (j : ℤ) (hw : V22.gamma r ((M : ℝ) + 2) ≤ threeRangeW r M j) :
    2 ≤ mu * (V22.fiberFunction ((1 + r) / 2) mu M j - V22.psi ((M : ℝ) / mu)) := by
  have hN : 10 ≤ M + 2 := by exact_mod_cast (hlo.trans hNlo)
  have hlog : 0 ≤ V22.lambdaT ((M : ℝ) / mu) := by
    unfold V22.lambdaT
    exact mul_nonneg (by norm_num) (Real.log_nonneg ht)
  have hlam := lambdaBonus_source hc hrm hrmh hlo hNlo hr0 hrrm hmu
  simpa only [activityOnePsi, V22.psi] using
    bonusRange_upper_nonnegative_fiber hN hr0 (hrrm.trans hrmh) hmu (hlog.trans hlam) j hw

end Erdos993Lean.Analytic.V22.Analysis
