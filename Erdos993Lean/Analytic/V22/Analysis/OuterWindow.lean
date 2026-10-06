import Erdos993Lean.Analytic.V22.Analysis.OuterSpikePhi
import Erdos993Lean.Analytic.V22.Analysis.SpikedWindowBridge
import Erdos993Lean.Analytic.V22.Analysis.RowPriceBook
import Erdos993Lean.Analytic.V22.Analysis.InterfaceDefinitions

/-! Source: frozen note Corollary 5.15. Every inherited outer row retains
its actual q, mean, theta/D caps, zero-tilt MGF constraint, exact class,
spike cutoff, certified cell log bounds, and original integer fibers.
The final source statement has only the original finite-check premise,
row/activity domain, and mean bound. Parent owns Lean verification. -/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set Erdos993Lean.Analytic.NoValley

noncomputable section

/-- The Table 1 class enclosure for every actual q in an inherited outer
row. The endpoint convention and row identity remain unchanged. -/
theorem outer_row_class {p : ℕ} (hp : p < 55) (houter : p ≤ 5 ∨ 40 ≤ p)
    {q : ℝ} (hqa : V22.Checks.rowQa p ≤ q) (hqb : q ≤ V22.Checks.rowQb p) :
    ∃ k ∈ V22.classes, V22.classForPiece p = some k ∧ p ∈ k.iotas ∧
      V22.Checks.inCell k.ra k.rb |2*q-1| ∧
      (k.muD : ℝ) ≤ V22.startingMean p ∧ V22.excess p = (k.b : ℝ) ∧
      V22.spikeCutoff p = (k.tau : ℝ) := by
  have h := e6_outer_tableQ p hp houter
  unfold e6OuterTableQ at h
  cases he : V22.classForPiece p with
  | none => simp [he] at h
  | some k =>
    simp only [he] at h
    obtain ⟨hk, hpi, hsign, ha, hb, hm, _⟩ := h
    have ha' : (k.ra : ℝ) ≤ min |2*V22.Checks.rowQa p-1| |2*V22.Checks.rowQb p-1| := by
      rw [e6_rowQa_cast, e6_rowQb_cast]
      exact_mod_cast ha
    have hb' : V22.Checks.rowRhi p ≤ (k.rb : ℝ) := by
      unfold V22.Checks.rowRhi
      rw [e6_rowQa_cast, e6_rowQb_cast]
      exact_mod_cast hb
    have hlo : (k.ra : ℝ) ≤ |2*q-1| := by
      rcases hsign with hneg | hpos
      · have hneg' : V22.Checks.rowQb p ≤ 1/2 := by
          rw [e6_rowQb_cast]
          have hcast := (Rat.cast_le (K := ℝ)).2 hneg
          norm_num at hcast
          exact hcast
        have hab := ha'.trans (min_le_right _ _)
        rw [abs_of_nonpos (by linarith : 2*V22.Checks.rowQb p-1 ≤ 0)] at hab
        rw [abs_of_nonpos (by linarith : 2*q-1 ≤ 0)]
        linarith
      · have hpos' : 1/2 ≤ V22.Checks.rowQa p := by
          rw [e6_rowQa_cast]
          have hcast := (Rat.cast_le (K := ℝ)).2 hpos
          norm_num at hcast
          exact hcast
        have hab := ha'.trans (min_le_left _ _)
        rw [abs_of_nonneg (by linarith : 0 ≤ 2*V22.Checks.rowQa p-1)] at hab
        rw [abs_of_nonneg (by linarith : 0 ≤ 2*q-1)]
        linarith
    have hhi : |2*q-1| ≤ V22.Checks.rowRhi p := by
      have ha0 := neg_abs_le (2*V22.Checks.rowQa p-1)
      have hb0 := le_abs_self (2*V22.Checks.rowQb p-1)
      have hma := le_max_left |2*V22.Checks.rowQa p-1| |2*V22.Checks.rowQb p-1|
      have hmb := le_max_right |2*V22.Checks.rowQa p-1| |2*V22.Checks.rowQb p-1|
      unfold V22.Checks.rowRhi
      apply abs_le.mpr
      constructor <;> linarith
    refine ⟨k, hk, rfl, hpi, ⟨hlo, hhi.trans hb'⟩, ?_, ?_, ?_⟩
    · change (k.muD : ℝ) ≤ ((V22.mu0Data.getD p 0 : ℚ) : ℝ)
      exact_mod_cast hm
    · simp [V22.excess, he]
    · simp [V22.spikeCutoff, he]

/-- Constructing the full source cell/block deficit family for ROW-v21.
The repaired marked-cell min(Phi,Def_g) is consumed inside the native cell
theorem; no unlicensed Phi projection occurs. -/
theorem outer_row_cell_deficits (hA3p : V22.Checks.lemma_7_5)
    (hA4p : V22.Checks.lemma_7_7) (hA4d : V22.Checks.lemma_7_8)
    (hA4m : V22.Checks.lemma_7_9) (hB2 : V22.Checks.lemma_7_13)
    (hB3 : V22.Checks.lemma_7_14_certified) (hD2 : V22.Checks.lemma_7_19)
    {p : ℕ} (hp : p < 55) {k : V22.V22Class} (hk : k ∈ V22.classes)
    (he : V22.classForPiece p = some k) {q mu : ℝ}
    (hq : V22.Checks.inCell (1/4) (3/4) q)
    (hr : V22.Checks.inCell k.ra k.rb |2*q-1|)
    (hmuD : (k.muD : ℝ) ≤ mu) : rowPriceCellDeficits p q mu k.beta := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hmu40, _, _⟩ := window_class_domains hk
  have hmu : 0 < mu := by linarith
  have hb : V22.excess p = (k.b : ℝ) := by simp [V22.excess, he]
  have hcut : V22.spikeCutoff p = (k.tau : ℝ) := by simp [V22.spikeCutoff, he]
  intro M hM ht0 ht1
  rw [hcut] at ht1
  obtain ⟨cell, hc, hid, ht⟩ := outer_spike_cells_cover hk ht0 ht1.le
  obtain ⟨hlo, _, _, hma, hmaeq⟩ := outer_cell_metadata hc hk hid
  have hmaM : (cell.ma : ℝ) ≤ (M : ℝ) := by
    have hMlo := (le_div_iff₀ hmu).1 ht.1
    have hmulo := mul_le_mul_of_nonneg_right hmuD (show 0 ≤ (cell.lo : ℝ) from by linarith)
    nlinarith
  obtain ⟨i, hi, hblock⟩ := outer_spike_blocks_cover (by linarith : 0 < (cell.ma : ℝ)) hmaM
  have hD := outer_spike_cell_deficit hA3p hA4p hA4d hA4m hB2 hB3 hD2
    hc hk hid hi hM hr hq hmuD ht hblock
  refine ⟨cell, hc, ?_, by linarith, ht, i, hi, hblock, ?_⟩
  · simpa only [V22.Checks.rowUsesCell, he] using hid.symm
  · rw [hb]
    linarith

/-- Full paper-v2.2 Corollary 5.15 for all original outer subintervals,
every actual q in the inherited row interval, and every mean above the
Table 2 starting mean. Only the original zero-tilt constraint is used. -/
theorem source_outer_noValley (hFinite : V22.FiniteChecks)
    {p : ℕ} (hp : p < 55) (houter : p ≤ 5 ∨ 40 ≤ p) {q mu : ℝ}
    (hqa : V22.Checks.rowQa p ≤ q) (hqb : q ≤ V22.Checks.rowQb p)
    (hmu : V22.startingMean p ≤ mu) :
    NoValleyAtMGF2 q mu ((V22.pieceV22 p).theta : ℝ) ((V22.pieceV22 p).D : ℝ)
      [(1-q, Real.exp (-V22.Checks.rowEll0 p*mu))] := by
  rcases hFinite with ⟨h71, h72, h73, h74, h75, h76, h77, h78, h79, h710,
    h711, h712, h713, h714, h714c, h715, h716, h717, h718, h719, h720, h721⟩
  obtain ⟨k, hk, he, hpi, hr, hmean, hb, hcut⟩ := outer_row_class hp houter hqa hqb
  obtain ⟨hqa0, _, hqb1, _, _, _, _, hmean19, _⟩ := e6_row_bounds hp
  have hq : V22.Checks.inCell (1/4) (3/4) q := ⟨hqa0.trans hqa, by linarith⟩
  have hmuD := hmean.trans hmu
  have hmup : 0 < mu := by linarith
  have hbeta : 0 ≤ (k.beta : ℝ) := (window_class_domains hk).2.2.2.2.1
  have hCells := outer_row_cell_deficits h75 h77 h78 h79 h713 h714c h719 hp hk he hq hr hmuD
  have hf : ∀ M : ℕ, V22.spikeCutoff p*mu ≤ (M : ℝ) → ∀ j : ℤ,
      V22.psi ((M : ℝ)/mu) + V22.targetLine (V22.excess p) k.beta ((M : ℝ)/mu) ≤
        V22.fiberFunction q mu M j := by
    intro M hM j
    have ht : (k.tau : ℝ) ≤ (M : ℝ)/mu := by
      apply (le_div_iff₀ hmup).2
      simpa only [hcut] using hM
    have hF := window_theorem_source h711 h716 h717 h718 h719 h720 hk hr hmuD ht j
    simpa only [hb, V22.targetLine, add_assoc] using hF
  exact row_noValley_of_cell_deficits h712 h721 hp hqa hqb hmu hbeta hCells hf

end

end Erdos993Lean.Analytic.V22.Analysis
