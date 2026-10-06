import Erdos993Lean.Analytic.V22.Analysis.CentralSpikeCells
import Erdos993Lean.Analytic.V22.Analysis.Envelope
import Erdos993Lean.Analytic.V22.Analysis.InterfaceDefinitions

/-! Paper v2.2 Theorem5.6: full central source no-valley conclusion.
The sole certificate premise is the named D finite-check bundle. All native
mixture/moment/zero-tilt hypotheses remain in NoValleyAtMGF2; the actual row,
activity, and real mean survive. Parent owns Lean verification. -/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set Erdos993Lean.Analytic.NoValley

theorem source_central_noValley (hfin : V22.FiniteChecks)
    {p : ℕ} (hp0 : 6 ≤ p) (hp1 : p ≤ 30) {q mu : ℝ}
    (hqlo : V22.Checks.rowQa p ≤ q) (hqhi : q ≤ V22.Checks.rowQb p)
    (hmu : V22.startingMean p ≤ mu) :
    NoValleyAtMGF2 q mu ((V22.pieceV22 p).theta : ℝ) ((V22.pieceV22 p).D : ℝ)
      [(1 - q, Real.exp (-V22.Checks.rowEll0 p * mu))] := by
  rcases hfin with ⟨_, hQ, hEnv, hA3, hBeta, hBonus, hBonusPairs, _, _, hLargeT, _,
    hB1, hB2, _, hB3, _, _, _, _, _, _, hRows⟩
  have hp : p < 55 := by omega
  have hp39 : p ≤ 39 := by omega
  have hCell := central_row_cell_deficits hA3 hBonusPairs hB2 hB3 hp0 hp39 hqlo hqhi hmu
  obtain ⟨hnone, hwingnone, _, _, _, _⟩ := e6_central_tableQ p hp ⟨hp0, hp1⟩
  have hCut : V22.spikeCutoff p = (3 / 5 : ℝ) := by
    simp only [V22.spikeCutoff, hnone, hwingnone]
  have hExcess : V22.excess p = 0 := by simp only [V22.excess, hnone]
  obtain ⟨hMean, _⟩ := e6_startingMean_bounds hp
  have hr := central_row_r_cap hp0 hp39 hqlo hqhi
  apply row_noValley_of_cell_deficits hB1 hRows hp hqlo hqhi hmu (by norm_num : (0 : ℝ) ≤ 0) hCell
  intro M hM j
  have ht : (3 / 5 : ℝ) ≤ (M : ℝ) / mu := by
    apply (le_div_iff₀ (show 0 < mu by linarith)).2
    simpa only [hCut] using hM
  have h := fiber_inequality_source hQ hEnv hBeta hBonus hLargeT hr (by linarith : 19 ≤ mu) ht j
  simpa only [hExcess, V22.targetLine, zero_mul, add_zero, zero_add] using h

end Erdos993Lean.Analytic.V22.Analysis
