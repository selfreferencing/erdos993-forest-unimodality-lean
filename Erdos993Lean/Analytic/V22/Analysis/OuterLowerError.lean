import Erdos993Lean.Analytic.V22.Analysis.OuterCells
import Erdos993Lean.Analytic.V22.Analysis.LinearizedLowerBounds

/-! Source: Lemma 7.13 and the zero contribution of range L in the
spike proof of Corollary 5.15. The generic helper also consumes the central
7.13 entry without adding an analytical premise to its final source wrapper.
Parent owns Lean verification. -/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

theorem outer_lower_error_from_slack (hB2 : V22.Checks.lemma_7_13)
    {M : ℕ} {r rm mu thi Ns : ℝ} (hM : 8 ≤ M) (hmu : 0 < mu)
    (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hrmh : rm ≤ 1 / 2)
    (hNs : 10 ≤ Ns) (hNsN : Ns ≤ (M : ℝ) + 2)
    (ht : (M : ℝ) / mu ≤ thi) (hthi : thi ≤ 1)
    (hslack : 0 < V22.Checks.spikeLowerSlack rm thi Ns) :
    (2 * ((M : ℝ) / mu) / (M : ℝ)) * ((M : ℝ) + 3) * V22.eL r ((M : ℝ) + 2) ≤
      (9 / 2 : ℝ) * ((M : ℝ) / mu - 1) ^ 2 := by
  let t : ℝ := (M : ℝ) / mu
  let N : ℝ := (M : ℝ) + 2
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have hMp : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M from by omega)
  have hrm0 := hr0.trans hrrm
  have hN : 10 ≤ N := hNs.trans hNsN
  have hthi0 : 0 ≤ thi := ht0.trans ht
  have hmonoT : (9 / 2 : ℝ) * (1 - t) ^ 2 - V22.Checks.spikeLowerSlack rm t N ≤
      (9 / 2 : ℝ) * (1 - thi) ^ 2 - V22.Checks.spikeLowerSlack rm thi N :=
    hB2.2.2.1 rm ⟨hrm0, hrmh⟩ N hN ht0 hthi0 ht
  have hmonoN : (9 / 2 : ℝ) * (1 - thi) ^ 2 - V22.Checks.spikeLowerSlack rm thi N ≤
      (9 / 2 : ℝ) * (1 - thi) ^ 2 - V22.Checks.spikeLowerSlack rm thi Ns :=
    hB2.2.2.2 rm ⟨hrm0, hrmh⟩ thi hthi0 hNs hN hNsN
  have hsq : (1 - thi) ^ 2 ≤ (1 - t) ^ 2 := by
    exact (sq_le_sq₀ (by linarith : 0 ≤ 1 - thi) (by linarith : 0 ≤ 1 - t)).2 (by linarith)
  have hcap : (N + 1) * V22.eL r N ≤
      V22.alpha1 N rm * (rm * Real.sqrt N) + V22.alpha2 N rm * (rm * Real.sqrt N) ^ 2 := by
    have he := linearized_eL_upper hN hr0 hrrm hrmh
    have hnu0 := activityNu_nonneg (N := N) hr0
    have hnucap : activityNu r N ≤ rm * Real.sqrt N :=
      mul_le_mul_of_nonneg_right hrrm (Real.sqrt_nonneg N)
    have hsqcap := (sq_le_sq₀ hnu0 (hnu0.trans hnucap)).2 hnucap
    obtain ⟨ha1, ha2⟩ := coefficient_alpha_nonneg hN hrm0 hrmh
    exact he.trans (add_le_add (mul_le_mul_of_nonneg_left hnucap ha1)
      (mul_le_mul_of_nonneg_left hsqcap ha2))
  have hscaled := mul_le_mul_of_nonneg_left hcap (show 0 ≤ 2 * t / (N - 2) from by
    dsimp [N]; norm_num only [add_sub_cancel_right]; positivity)
  have hκ : (2 * t / (N - 2)) *
      (V22.alpha1 N rm * (rm * Real.sqrt N) + V22.alpha2 N rm * (rm * Real.sqrt N) ^ 2) =
      (9 / 2 : ℝ) * (1 - t) ^ 2 - V22.Checks.spikeLowerSlack rm t N := by
    unfold V22.Checks.spikeLowerSlack
    dsimp only
    ring
  rw [hκ] at hscaled
  have hcost : (2 * t / (N - 2)) * ((N + 1) * V22.eL r N) ≤ (9 / 2 : ℝ) * (t - 1) ^ 2 := by
    calc
      (2 * t / (N - 2)) * ((N + 1) * V22.eL r N) ≤
          (9 / 2 : ℝ) * (1 - t) ^ 2 - V22.Checks.spikeLowerSlack rm t N := hscaled
      _ ≤ (9 / 2 : ℝ) * (1 - thi) ^ 2 - V22.Checks.spikeLowerSlack rm thi N := hmonoT
      _ ≤ (9 / 2 : ℝ) * (1 - thi) ^ 2 - V22.Checks.spikeLowerSlack rm thi Ns := hmonoN
      _ ≤ (9 / 2 : ℝ) * (1 - thi) ^ 2 := by linarith only [hslack]
      _ ≤ (9 / 2 : ℝ) * (1 - t) ^ 2 := mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ = (9 / 2 : ℝ) * (t - 1) ^ 2 := by ring
  convert hcost using 1 <;> dsimp [t, N] <;>
    simp only [add_sub_cancel_right] <;> ring

theorem outer_lower_error_paid (hB2 : V22.Checks.lemma_7_13)
    {c : V22.V22SpikeCell} (hc : c ∈ V22.spikeCells) {k : V22.V22Class}
    (hk : k ∈ V22.classes) (hid : k.classId = c.classId)
    {M : ℕ} {r mu : ℝ} (hM : 8 ≤ M) (har : (k.ra : ℝ) ≤ r) (hrrb : r ≤ (k.rb : ℝ))
    (hmuD : (k.muD : ℝ) ≤ mu) (ht : V22.Checks.inCell c.lo c.hi ((M : ℝ) / mu)) :
    (2 * ((M : ℝ) / mu) / (M : ℝ)) * ((M : ℝ) + 3) * V22.eL r ((M : ℝ) + 2) ≤
      (9 / 2 : ℝ) * ((M : ℝ) / mu - 1) ^ 2 := by
  obtain ⟨hra, hrb, _, _, _, _, _, htau1, _, _, hmu40, _, _⟩ := window_class_domains hk
  obtain ⟨hc0, hrm, hmean⟩ := outer_cell_class_fields hk hid
  obtain ⟨hlo, hhi, _, hma, hmaeq⟩ := outer_cell_metadata hc hk hid
  have hmu : 0 < mu := by linarith
  have hMlo := (le_div_iff₀ hmu).1 ht.1
  have hmaM : (c.ma : ℝ) ≤ (M : ℝ) := by rw [hmaeq]; nlinarith
  let Ns : ℝ := max 10 (V22.spikeMean c * (c.lo : ℝ) + 2)
  have hNs : 10 ≤ Ns := le_max_left _ _
  have hNsN : Ns ≤ (M : ℝ) + 2 := by
    dsimp [Ns]
    apply max_le
    · exact_mod_cast (show 10 ≤ M + 2 from by omega)
    · rw [hmean]
      rw [← hmaeq]
      linarith
  have hslack := hB2.2.1 c hc hc0
  change 0 < V22.Checks.spikeLowerSlack (V22.spikeRm c) c.hi Ns at hslack
  rw [hrm] at hslack
  exact outer_lower_error_from_slack hB2 hM hmu (hra.trans_le har).le hrrb hrb hNs hNsN
    ht.2 (hhi.trans htau1.le) hslack

end Erdos993Lean.Analytic.V22.Analysis
