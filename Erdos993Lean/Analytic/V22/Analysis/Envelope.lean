import Erdos993Lean.Analytic.V22.Analysis.EnvelopeTemplate
import Erdos993Lean.Analytic.V22.Analysis.CappedRemainderMonotonicity
import Erdos993Lean.Analytic.V22.Analysis.LambdaBonus
import Erdos993Lean.Analytic.V22.Analysis.LargeTFiber
import Erdos993Lean.Analytic.V22.Analysis.Symmetry

/-!
# Paper v2.2, Theorem 4.15

Every indexed binomial atom is retained. The finite premises are precisely
named Section 7 propositions. Initial sizes and radical splits are exact.
This source is a proof draft until its root-owned sequential check passes.
-/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

private theorem envelope_upper_den_monotone {t N P M0 rm : ℝ}
    (hN : 10 ≤ N) (hNP : N ≤ P) (hr0 : 0 ≤ rm) (hrh : rm ≤ 1 / 2) :
    N - 1 - V22.kappaA N rm * V22.Ghat t M0 / V22.rhoStar N rm ≤
      P - 1 - V22.kappaA P rm * V22.Ghat t M0 / V22.rhoStar P rm := by
  have hs := coefficient_rhoStar_monotone hN hNP hr0 hrh
  have hs0 := coefficient_rhoStar_pos hN hr0 hrh
  have hk := coefficient_kappaA_antitone hN hNP hr0 hrh
  have hk0 := (coefficient_remaining_nonneg hN hr0 hrh).1
  have hG : 0 ≤ V22.Ghat t M0 := by
    unfold V22.Ghat
    rw [shared_G_eq, shared_G_eq]
    exact (rootG_nonneg _).trans (le_max_left _ _)
  have hRatio := div_le_div₀ (mul_nonneg hk0 hG)
    (mul_le_mul_of_nonneg_right hk hG) hs0 hs
  linarith

/-- The exact nine-cell transport supplies both native remainders. The upper
remainder is consumed only in its source negative-log branch. -/
theorem envelope_cell_payment (hQ : Checks.lemma_7_2) (hCells : Checks.lemma_7_3)
    (hBeta : Checks.lemma_7_5) (hBonus : Checks.lemma_7_6)
    {c : ℚ × ℚ} (hc : c ∈ Checks.envelopeCells) {s r mu : ℝ} {M : ℕ}
    (hs : Checks.inCell c.1 c.2 s) (hr0 : 0 ≤ r) (hrm : r ≤ 1 / 4)
    (hmu : 19 ≤ mu) (ht : V22.tOfS s = (M : ℝ) / mu)
    (hN : (14 : ℝ) ≤ (M : ℝ) + 2)
    (hnu : activityNu r ((M : ℝ) + 2) ≤ 6) :
    bonusRangeDL r mu M ≤ activityOneT ((M : ℝ) / mu) (M : ℝ) ∧
    (threeRangeLambdaU r mu M < 0 →
      bonusRangeDUPrime r mu M ≤ activityOneT ((M : ℝ) / mu) (M : ℝ)) := by
  let M0 : ℝ := 19 * V22.tOfS c.1
  let N0 : ℝ := M0 + 2
  let N : ℝ := (M : ℝ) + 2
  let t : ℝ := (M : ℝ) / mu
  have hM : 8 ≤ M := by exact_mod_cast (show (8 : ℝ) ≤ M by linarith)
  have hmu0 : 0 < mu := by linarith
  have hM0p : 0 < M0 := (envelopeCell_start_domain hc).1
  have hM0 : 8 ≤ M0 := (envelopeCell_start_domain hc).2
  have hM0M : M0 ≤ (M : ℝ) := envelopeCell_start_le_fiber hc hs hmu ht
  have hN0 : 10 ≤ N0 := by dsimp [N0]; linarith
  have hN0N : N0 ≤ N := by dsimp [N0, N]; linarith
  have hNN : 10 ≤ N := by dsimp [N]; linarith
  have hData := hCells c hc s hs
  have hCap0 : cappedNu (1 / 4) N0 = (1 / 4) * Real.sqrt N0 :=
    envelopeCell_initial_cap hc
  have hBetaL0 : 0 < V22.betaL t N0 M0 (1 / 4) (cappedNu (1 / 4) N0) := by
    dsimp [t]
    rw [hCap0, ← ht]
    exact hData.1
  have hBetaL := cappedNu_betaL_monotone hN0 hN0N (by norm_num) (by norm_num) hBetaL0
  have hCap : activityNu r N ≤ cappedNu (1 / 4) N := by
    apply le_min hnu
    exact mul_le_mul_of_nonneg_right hrm (Real.sqrt_nonneg N)
  have hS : 0 ≤ V22.gaussianSlack t := by
    dsimp [t]
    rw [← ht]
    have hb := envelopeCell_bounds hc
    exact shared_gaussianSlack_coordinate_nonneg hQ (hb.1.trans hs.1) (hs.2.trans hb.2.2)
  have hT : V22.templateT t M0 ≤ V22.templateT t M :=
    shared_templateT_mono hM0p hM0M hS
  have hInitial := envelope_initial_template_pays hQ hCells hc hs
  rw [ht] at hInitial
  have hInitialL : V22.dLbar t N0 M0 (1 / 4) (cappedNu (1 / 4) N0) ≤ V22.templateT t M0 := by
    rw [hCap0]
    exact (le_max_left _ _).trans hInitial
  have hDL := source_closed_lower_remainder hM hmu0 hr0 hrm (by norm_num) hM0 hM0M
    hCap (hBetaL0.trans_le hBetaL)
  have hDLmono := cappedNu_dLbar_antitone hN0 hN0N (by norm_num) (by norm_num) hBetaL0
  constructor
  · rw [← shared_templateT_eq]
    exact hDL.trans (hDLmono.trans (hInitialL.trans hT))
  · intro hUNeg
    have hUL := lambdaBonus_source hBonus (by norm_num) (by norm_num)
      (by norm_num) (show (67 / 5 : ℝ) ≤ (M : ℝ) + 2 by linarith) hr0 hrm hmu0
    have hsNeg : s < 0 := by
      have hLambda : V22.lambdaT (V22.tOfS s) < 0 := by rw [ht]; exact lt_of_le_of_lt hUL hUNeg
      have hRoot := (rootMap_neg_iff _).2 hLambda
      rw [← shared_rootMap_eq, shared_coordinate_root (by
        have hb := envelopeCell_bounds hc
        linarith [hb.1, hs.1])] at hRoot
      exact hRoot
    obtain ⟨hRho, hBetaE0raw, hDen0⟩ := hData.2.2.1 hsNeg
    have hBetaE0 : 0 < V22.betaE N0 (1 / 4) (cappedNu (1 / 4) N0) := by
      rw [hCap0]
      exact hBetaE0raw
    have hFirst : 19 * V22.tOfS (-(66 / 125 : ℝ)) + 2 ≤ N0 := by
      have hb := envelopeCell_bounds hc
      have hmono := shared_tOfS_strictMonoOn.monotoneOn (show -1 < -(66 / 125 : ℝ) by norm_num)
        (show -1 < (c.1 : ℝ) by linarith [hb.1]) hb.1
      dsimp [N0, M0]
      linarith
    have hEndpoint : (-66 / 125 : ℝ) = -(66 / 125 : ℝ) := by ring
    have hFirstI : N0 ∈ Ici (19 * V22.tOfS (-66 / 125) + 2) := by
      change 19 * V22.tOfS (-66 / 125) + 2 ≤ N0
      rw [hEndpoint]
      exact hFirst
    have hNextI : N ∈ Ici (19 * V22.tOfS (-66 / 125) + 2) := by
      change 19 * V22.tOfS (-66 / 125) + 2 ≤ N
      rw [hEndpoint]
      exact hFirst.trans hN0N
    have hBetaRange := hBeta.2.2.2.1.1
    have hBetaE : V22.betaE N0 (1 / 4) (cappedNu (1 / 4) N0) ≤
        V22.betaE N (1 / 4) (cappedNu (1 / 4) N) :=
      hBetaRange hFirstI hNextI hN0N
    have hDen0' : 0 < N0 - 1 - V22.kappaA N0 (1 / 4) * V22.Ghat t M0 / V22.rhoStar N0 (1 / 4) := by
      dsimp [t]
      rw [← ht]
      exact hDen0
    have hDen := envelope_upper_den_monotone (t := t) (M0 := M0) hN0 hN0N
      (show (0 : ℝ) ≤ 1 / 4 by norm_num) (by norm_num)
    have hDU := source_closed_upper_remainder hM hmu0 hr0 hrm (by norm_num) hM0 hM0M hCap
      hUL hUNeg (hBetaE0.trans_le hBetaE) (hDen0'.trans_le hDen)
    have hDUmono := cappedNu_dUbar_antitone (t := t) (M0 := M0) hN0 hN0N
      (by norm_num) (by norm_num) hBetaE hBetaE0 hDen0'
    have hInitialU : V22.dUbar t N0 M0 (1 / 4) (cappedNu (1 / 4) N0) ≤ V22.templateT t M0 := by
      rw [hCap0]
      have hNegT := hsNeg
      simp only [if_pos hNegT] at hInitial
      exact (le_max_right _ _).trans hInitial
    rw [← shared_templateT_eq]
    exact hDU.trans (hDUmono.trans (hInitialU.trans hT))

/-- Nonnegative template on the full exact coordinate cover. -/
theorem envelope_template_nonnegative (hQ : Checks.lemma_7_2) (hCells : Checks.lemma_7_3)
    {c : ℚ × ℚ} (hc : c ∈ Checks.envelopeCells) {s mu : ℝ} {M : ℕ}
    (hs : Checks.inCell c.1 c.2 s) (hmu : 19 ≤ mu)
    (ht : V22.tOfS s = (M : ℝ) / mu) :
    0 ≤ activityOneT ((M : ℝ) / mu) (M : ℝ) := by
  have hData := hCells c hc s hs
  have hL : 0 ≤ V22.dLbar (V22.tOfS s) (19 * V22.tOfS c.1 + 2)
      (19 * V22.tOfS c.1) (1 / 4) ((1 / 4) * Real.sqrt (19 * V22.tOfS c.1 + 2)) := by
    unfold V22.dLbar
    exact div_nonneg (sq_nonneg _) hData.1.le
  have hInitial := hL.trans ((le_max_left _ _).trans (envelope_initial_template_pays hQ hCells hc hs))
  have hb := envelopeCell_bounds hc
  have hS := shared_gaussianSlack_coordinate_nonneg hQ (hb.1.trans hs.1) (hs.2.trans hb.2.2)
  have hT := shared_templateT_mono (envelopeCell_start_domain hc).1
    (envelopeCell_start_le_fiber hc hs hmu ht) hS
  simpa only [ht, shared_templateT_eq] using hInitial.trans hT

/-- The positive-side all-integer envelope; the native fiber itself occurs in
its conclusion, with no assumed Gaussian or template estimates. -/
theorem fiber_inequality_positive (hQ : Checks.lemma_7_2) (hCells : Checks.lemma_7_3)
    (hBeta : Checks.lemma_7_5) (hBonus : Checks.lemma_7_6) (hLargeT : Checks.lemma_7_10)
    {r mu : ℝ} {M : ℕ} (hr0 : 0 ≤ r) (hrm : r ≤ 1 / 4) (hmu : 19 ≤ mu)
    (htlo : (3 / 5 : ℝ) ≤ (M : ℝ) / mu) (j : ℤ) :
    V22.psi ((M : ℝ) / mu) ≤ V22.fiberFunction ((1 + r) / 2) mu M j := by
  have hmu0 : 0 < mu := by linarith
  have hMReal : (57 / 5 : ℝ) ≤ (M : ℝ) := by
    have hM := (le_div_iff₀ hmu0).1 htlo
    linarith
  have hM : 12 ≤ M := by
    have hMr : (11 : ℝ) < M := by linarith
    have hMn : 11 < M := by exact_mod_cast hMr
    omega
  have hN : 10 ≤ M + 2 := by omega
  have hNReal : (14 : ℝ) ≤ (M : ℝ) + 2 := by exact_mod_cast (show 14 ≤ M + 2 by omega)
  have hrh : r ≤ 1 / 2 := by linarith
  by_cases htlarge : (8 / 5 : ℝ) ≤ (M : ℝ) / mu
  · have hNstar : (162 / 5 : ℝ) ≤ (M : ℝ) + 2 := by
      have hMul := (le_div_iff₀ hmu0).1 htlarge
      nlinarith
    have h := largeT_fiber_source hLargeT (by norm_num) (by norm_num) (by norm_num)
      hNstar hr0 hrm hmu0 htlarge j
    exact h.2.le.trans h.1
  · have hthi : (M : ℝ) / mu ≤ 321 / 200 := by linarith
    let s := rootMap (activityOneLambda_t ((M : ℝ) / mu))
    have hs : -1 < s := rootMap_gt_neg_one _
    have htpos : 0 < (M : ℝ) / mu := by linarith
    have hcoord : V22.tOfS s = (M : ℝ) / mu := gaussian_coordinate_rootMap htpos
    have hsL : -(66 / 125 : ℝ) ≤ s := by
      by_contra! hlt
      have hmono := shared_tOfS_strictMonoOn hs (show -1 < -(66 / 125 : ℝ) by norm_num) hlt
      rw [hcoord] at hmono
      linarith [shared_gaussianSlack_endpoints.1]
    have hsU : s ≤ 67 / 100 := by
      by_contra! hlt
      have hmono := shared_tOfS_strictMonoOn (show -1 < (67 / 100 : ℝ) by norm_num) hs hlt
      rw [hcoord] at hmono
      linarith [shared_gaussianSlack_endpoints.2]
    obtain ⟨c, hc, hsc⟩ := envelopeCells_cover hsL hsU
    have hT0 := envelope_template_nonnegative hQ hCells hc hsc hmu hcoord
    have hMargin : 0 ≤ mu * (V22.fiberFunction ((1 + r) / 2) mu M j -
        activityOnePsi ((M : ℝ) / mu)) := by
      by_cases hlarge : 6 ≤ activityNu r ((M : ℝ) + 2)
      · have hDL0raw := (largeNu_lower_source hN hr0 hrh hlarge hmu0 hthi ActivityOneSide.L).2.2.2
        have hDL0 : bonusRangeDL r mu M = 0 := by
          simpa only [bonusRangeDL, largeNuLowerRemainder, V22.positivePart,
            shared_rootMap_eq, show ((M : ℝ) + 2) + 1 = (M : ℝ) + 3 by ring] using hDL0raw
        by_cases hw : threeRangeW r M j ≤ 1
        · have h := bonusRange_lower hN hr0 hrh hmu0 j hw
          rw [hDL0] at h
          simp only [sub_zero] at h
          exact (le_min (by norm_num) hT0).trans h
        · by_cases hwU : V22.gamma r ((M : ℝ) + 2) ≤ threeRangeW r M j
          · have hl := (largeNu_upper_positive hN hr0 hrh hlarge hmu0
              (ta := (3 / 5 : ℝ)) (by norm_num) htlo).2
            exact (show (0 : ℝ) ≤ 2 by norm_num).trans
              (bonusRange_upper_nonnegative_fiber hN hr0 hrh hmu0 hl.le j hwU)
          · exact (show (0 : ℝ) ≤ 2 by norm_num).trans
              (bonusRange_middle hN hr0 hrh hmu0 j (by linarith) (by linarith))
      · have hnu : activityNu r ((M : ℝ) + 2) ≤ 6 := by linarith
        have hPay := envelope_cell_payment hQ hCells hBeta hBonus hc hsc hr0 hrm hmu hcoord hNReal hnu
        by_cases hw : threeRangeW r M j ≤ 1
        · exact (le_min (by norm_num) (by linarith [hPay.1])).trans
            (bonusRange_lower hN hr0 hrh hmu0 j hw)
        · by_cases hwU : V22.gamma r ((M : ℝ) + 2) ≤ threeRangeW r M j
          · by_cases hl : 0 ≤ threeRangeLambdaU r mu M
            · exact (show (0 : ℝ) ≤ 2 by norm_num).trans
                (bonusRange_upper_nonnegative_fiber hN hr0 hrh hmu0 hl j hwU)
            · have hneg : threeRangeLambdaU r mu M < 0 := by linarith
              exact (show 0 ≤ activityOneT ((M : ℝ) / mu) (M : ℝ) - bonusRangeDUPrime r mu M by
                linarith [hPay.2 hneg]).trans
                (bonusRange_upper_negative_fiber hN hr0 hrh hmu0 hneg j hwU)
          · exact (show (0 : ℝ) ≤ 2 by norm_num).trans
              (bonusRange_middle hN hr0 hrh hmu0 j (by linarith) (by linarith))
    have hDiff := (mul_nonneg_iff_of_pos_left hmu0).1 hMargin
    rw [← shared_psi_eq] at hDiff
    exact sub_nonneg.mp hDiff

/-- Paper v2.2 Theorem4.15, both activities and every integer atom.
The finite source statements remain explicit and can be discharged by lane D. -/
theorem fiber_inequality_source (hQ : Checks.lemma_7_2) (hCells : Checks.lemma_7_3)
    (hBeta : Checks.lemma_7_5) (hBonus : Checks.lemma_7_6) (hLargeT : Checks.lemma_7_10)
    {q mu : ℝ} {M : ℕ} (hr : |2 * q - 1| ≤ 1 / 4) (hmu : 19 ≤ mu)
    (ht : (3 / 5 : ℝ) ≤ (M : ℝ) / mu) (j : ℤ) :
    V22.psi ((M : ℝ) / mu) ≤ V22.fiberFunction q mu M j := by
  have hq : 0 < q ∧ q < 1 := by
    have h := abs_le.mp hr
    constructor <;> linarith
  by_cases hhalf : 1 / 2 ≤ q
  · have hr0 : 0 ≤ 2 * q - 1 := by linarith
    have he : (1 + (2 * q - 1)) / 2 = q := by ring
    have h := fiber_inequality_positive hQ hCells hBeta hBonus hLargeT hr0
      ((le_abs_self _).trans hr) hmu ht j
    simpa only [he] using h
  · have hr0 : 0 ≤ 1 - 2 * q := by linarith
    have hrm : 1 - 2 * q ≤ 1 / 4 := by
      have h := abs_le.mp hr
      linarith
    have he : (1 + (1 - 2 * q)) / 2 = 1 - q := by ring
    have h := fiber_inequality_positive hQ hCells hBeta hBonus hLargeT hr0 hrm hmu ht ((M : ℤ) - j)
    rw [he, shared_fiberFunction_eq, fiber_reflection hq.1 hq.2, ← shared_fiberFunction_eq] at h
    exact h

end Erdos993Lean.Analytic.V22.Analysis
