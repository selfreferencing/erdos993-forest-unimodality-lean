import Erdos993Lean.Analytic.V22.Analysis.WingBounds
import Erdos993Lean.Analytic.V22.Analysis.CentralTheorem

/-! Paper v2.2 Theorem5.8: exact three wing classes and actual-mixture
no-valley consumer. The sole final certificate premise is V22.FiniteChecks.
Every actual activity, integer atom, real mean, cell, and inherited row survives.
Parent exclusively owns Lean verification. -/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set Erdos993Lean.Analytic.NoValley

noncomputable section

-- Exact definitional views preserve every native class and cell field.
private def wingClassesLiteral : List V22.V22WingClass := [
  ⟨1, "W1", (283 / 5000 : ℚ), (741 / 10000 : ℚ), (29 / 50 : ℚ), (19 / 1 : ℚ), [31, 32], [(29 / 50 : ℚ), (59 / 100 : ℚ), (3 / 5 : ℚ)]⟩,
  ⟨2, "W2", (37 / 500 : ℚ), (139 / 1250 : ℚ), (11 / 20 : ℚ), (20 / 1 : ℚ), [33, 34, 35, 36], [(11 / 20 : ℚ), (14 / 25 : ℚ), (57 / 100 : ℚ), (117 / 200 : ℚ), (3 / 5 : ℚ)]⟩,
  ⟨3, "W3", (1111 / 10000 : ℚ), (1667 / 10000 : ℚ), (13 / 25 : ℚ), (26 / 1 : ℚ), [37, 38, 39], [(13 / 25 : ℚ), (53 / 100 : ℚ), (27 / 50 : ℚ), (111 / 200 : ℚ), (23 / 40 : ℚ), (3 / 5 : ℚ)]⟩
]

private theorem wingClassesLiteral_eq : V22.wingClasses = wingClassesLiteral := by decide +kernel

private def wingCellsLiteral : List V22.V22Cell := [
  ⟨1, (29 / 50 : ℚ), (59 / 100 : ℚ)⟩,
  ⟨1, (59 / 100 : ℚ), (3 / 5 : ℚ)⟩,
  ⟨2, (11 / 20 : ℚ), (14 / 25 : ℚ)⟩,
  ⟨2, (14 / 25 : ℚ), (57 / 100 : ℚ)⟩,
  ⟨2, (57 / 100 : ℚ), (117 / 200 : ℚ)⟩,
  ⟨2, (117 / 200 : ℚ), (3 / 5 : ℚ)⟩,
  ⟨3, (13 / 25 : ℚ), (53 / 100 : ℚ)⟩,
  ⟨3, (53 / 100 : ℚ), (27 / 50 : ℚ)⟩,
  ⟨3, (27 / 50 : ℚ), (111 / 200 : ℚ)⟩,
  ⟨3, (111 / 200 : ℚ), (23 / 40 : ℚ)⟩,
  ⟨3, (23 / 40 : ℚ), (3 / 5 : ℚ)⟩
]

private theorem wingCellsLiteral_eq : V22.wingCells = wingCellsLiteral := by decide +kernel


theorem wing_class_domains {c : V22.V22WingClass} (hc : c ∈ V22.wingClasses) :
    0 < (c.ra : ℝ) ∧ (c.ra : ℝ) ≤ c.rb ∧ (c.rb : ℝ) ≤ 1 / 4 ∧
    (13 / 25 : ℝ) ≤ c.tau ∧ (c.tau : ℝ) ≤ 3 / 5 ∧
    19 ≤ (c.muW : ℝ) ∧ 8 ≤ (c.muW : ℝ) * (c.tau : ℝ) := by
  rw [wingClassesLiteral_eq] at hc
  simp only [wingClassesLiteral, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> norm_num

theorem wing_cell_domains {c : V22.V22WingClass} (hc : c ∈ V22.wingClasses)
    {cell : V22.V22Cell} (hcell : cell ∈ V22.wingCells) (hid : cell.classId = c.classId) :
    (c.tau : ℝ) ≤ cell.lo ∧ (cell.hi : ℝ) ≤ 3 / 5 ∧
    0 < (cell.lo : ℝ) ∧ 8 ≤ (c.muW : ℝ) * (cell.lo : ℝ) := by
  rw [wingClassesLiteral_eq] at hc
  simp only [wingClassesLiteral, List.mem_cons, List.not_mem_nil, or_false] at hc
  rw [wingCellsLiteral_eq] at hcell
  simp only [wingCellsLiteral, List.mem_cons, List.not_mem_nil, or_false] at hcell
  rcases hc with rfl | rfl | rfl <;>
    rcases hcell with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num at hid <;> norm_num

theorem wing_cells_cover {c : V22.V22WingClass} (hc : c ∈ V22.wingClasses)
    {t : ℝ} (ht0 : (c.tau : ℝ) ≤ t) (ht1 : t ≤ 3 / 5) :
    ∃ cell ∈ V22.wingCells, cell.classId = c.classId ∧ V22.Checks.inCell cell.lo cell.hi t := by
  rw [wingClassesLiteral_eq] at hc
  simp only [wingClassesLiteral, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · norm_num at ht0
    by_cases h0 : t ≤ (59 / 100 : ℝ)
    · refine ⟨V22.wingCells.getD 0 ⟨0, 0, 0⟩, by norm_num [wingCellsLiteral_eq, wingCellsLiteral], ?_⟩
      norm_num [wingCellsLiteral_eq, wingCellsLiteral, V22.Checks.inCell]
      exact ⟨ht0, h0⟩
    refine ⟨V22.wingCells.getD 1 ⟨0, 0, 0⟩, by norm_num [wingCellsLiteral_eq, wingCellsLiteral], ?_⟩
    norm_num [wingCellsLiteral_eq, wingCellsLiteral, V22.Checks.inCell]
    exact ⟨(lt_of_not_ge h0).le, ht1⟩
  · norm_num at ht0
    by_cases h0 : t ≤ (14 / 25 : ℝ)
    · refine ⟨V22.wingCells.getD 2 ⟨0, 0, 0⟩, by norm_num [wingCellsLiteral_eq, wingCellsLiteral], ?_⟩
      norm_num [wingCellsLiteral_eq, wingCellsLiteral, V22.Checks.inCell]
      exact ⟨ht0, h0⟩
    by_cases h1 : t ≤ (57 / 100 : ℝ)
    · refine ⟨V22.wingCells.getD 3 ⟨0, 0, 0⟩, by norm_num [wingCellsLiteral_eq, wingCellsLiteral], ?_⟩
      norm_num [wingCellsLiteral_eq, wingCellsLiteral, V22.Checks.inCell]
      exact ⟨(lt_of_not_ge h0).le, h1⟩
    by_cases h2 : t ≤ (117 / 200 : ℝ)
    · refine ⟨V22.wingCells.getD 4 ⟨0, 0, 0⟩, by norm_num [wingCellsLiteral_eq, wingCellsLiteral], ?_⟩
      norm_num [wingCellsLiteral_eq, wingCellsLiteral, V22.Checks.inCell]
      exact ⟨(lt_of_not_ge h1).le, h2⟩
    refine ⟨V22.wingCells.getD 5 ⟨0, 0, 0⟩, by norm_num [wingCellsLiteral_eq, wingCellsLiteral], ?_⟩
    norm_num [wingCellsLiteral_eq, wingCellsLiteral, V22.Checks.inCell]
    exact ⟨(lt_of_not_ge h2).le, ht1⟩
  · norm_num at ht0
    by_cases h0 : t ≤ (53 / 100 : ℝ)
    · refine ⟨V22.wingCells.getD 6 ⟨0, 0, 0⟩, by norm_num [wingCellsLiteral_eq, wingCellsLiteral], ?_⟩
      norm_num [wingCellsLiteral_eq, wingCellsLiteral, V22.Checks.inCell]
      exact ⟨ht0, h0⟩
    by_cases h1 : t ≤ (27 / 50 : ℝ)
    · refine ⟨V22.wingCells.getD 7 ⟨0, 0, 0⟩, by norm_num [wingCellsLiteral_eq, wingCellsLiteral], ?_⟩
      norm_num [wingCellsLiteral_eq, wingCellsLiteral, V22.Checks.inCell]
      exact ⟨(lt_of_not_ge h0).le, h1⟩
    by_cases h2 : t ≤ (111 / 200 : ℝ)
    · refine ⟨V22.wingCells.getD 8 ⟨0, 0, 0⟩, by norm_num [wingCellsLiteral_eq, wingCellsLiteral], ?_⟩
      norm_num [wingCellsLiteral_eq, wingCellsLiteral, V22.Checks.inCell]
      exact ⟨(lt_of_not_ge h1).le, h2⟩
    by_cases h3 : t ≤ (23 / 40 : ℝ)
    · refine ⟨V22.wingCells.getD 9 ⟨0, 0, 0⟩, by norm_num [wingCellsLiteral_eq, wingCellsLiteral], ?_⟩
      norm_num [wingCellsLiteral_eq, wingCellsLiteral, V22.Checks.inCell]
      exact ⟨(lt_of_not_ge h2).le, h3⟩
    refine ⟨V22.wingCells.getD 10 ⟨0, 0, 0⟩, by norm_num [wingCellsLiteral_eq, wingCellsLiteral], ?_⟩
    norm_num [wingCellsLiteral_eq, wingCellsLiteral, V22.Checks.inCell]
    exact ⟨(lt_of_not_ge h3).le, ht1⟩

theorem shared_wingC_eq (c : V22.V22WingClass) (cell : V22.V22Cell) (t N : ℝ) :
    V22.Checks.wingC c cell t N = wingC t ((c.muW : ℝ) * (cell.lo : ℝ)) c.ra c.rb N := by
  simp only [V22.Checks.wingC, V22.Checks.wingKPrime, V22.Checks.wingN0,
    wingC, wingKPrime, add_sub_cancel_right]

theorem shared_wingBPrime_eq (c : V22.V22WingClass) (cell : V22.V22Cell) (t : ℝ) :
    V22.Checks.wingBPrime c cell t = wingBPrime t ((c.muW : ℝ) * (cell.lo : ℝ)) c.rb := by
  simp only [V22.Checks.wingBPrime, V22.Checks.wingN0, wingBPrime, add_sub_cancel_right]

theorem shared_wingW_eq (c : V22.V22WingClass) (cell : V22.V22Cell) (t N : ℝ) :
    V22.Checks.wingW c cell t N = wingW t ((c.muW : ℝ) * (cell.lo : ℝ)) c.ra c.rb N := by
  simp only [V22.Checks.wingW, V22.Checks.wingTau1, V22.Checks.wingC,
    V22.Checks.wingKPrime, V22.Checks.wingBPrime, V22.Checks.wingDe,
    V22.Checks.wingNuMax, V22.Checks.wingN0, wingW, wingTau1, wingC,
    wingKPrime, wingBPrime, wingDe, cappedNu, add_sub_cancel_right]

theorem wing_class_beta_monotone (hBeta : V22.Checks.lemma_7_5)
    {c : V22.V22WingClass} (hc : c ∈ V22.wingClasses) :
    MonotoneOn (V22.Checks.cappedBeta c.rb) (Ici ((c.muW : ℝ) * (c.tau : ℝ) + 2)) := by
  rw [wingClassesLiteral_eq] at hc
  simp only [wingClassesLiteral, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · convert hBeta.1.1 using 1 <;> norm_num
  · convert hBeta.2.1.1 using 1 <;> norm_num
  · convert hBeta.2.2.1.1 using 1 <;> norm_num

theorem wing_cell_beta_monotone (hBeta : V22.Checks.lemma_7_5)
    {c : V22.V22WingClass} (hc : c ∈ V22.wingClasses)
    {cell : V22.V22Cell} (hcell : cell ∈ V22.wingCells) (hid : cell.classId = c.classId) :
    MonotoneOn (V22.Checks.cappedBeta c.rb) (Ici (V22.Checks.wingN0 c cell)) := by
  have hBase := wing_class_beta_monotone hBeta hc
  have hMu : 0 ≤ (c.muW : ℝ) := by obtain ⟨_, _, _, _, _, hm, _⟩ := wing_class_domains hc; linarith
  have hLo := (wing_cell_domains hc hcell hid).1
  have hStart := mul_le_mul_of_nonneg_left hLo hMu
  intro x hx y hy hxy
  apply hBase _ _ hxy
  · have h := hx; change V22.Checks.wingN0 c cell ≤ x at h
    unfold V22.Checks.wingN0 at h
    change (c.muW : ℝ) * (c.tau : ℝ) + 2 ≤ x
    linarith only [h, hStart]
  · have h := hy; change V22.Checks.wingN0 c cell ≤ y at h
    unfold V22.Checks.wingN0 at h
    change (c.muW : ℝ) * (c.tau : ℝ) + 2 ≤ y
    linarith only [h, hStart]

theorem wing_fiber_positive (hBeta : V22.Checks.lemma_7_5) (hBonus : V22.Checks.lemma_7_7)
    (hB2 : V22.Checks.lemma_7_13) (hWing : V22.Checks.lemma_7_15)
    {c : V22.V22WingClass} (hc : c ∈ V22.wingClasses) {r mu : ℝ} {M : ℕ}
    (hra : (c.ra : ℝ) ≤ r) (hrb : r ≤ (c.rb : ℝ)) (hmu : (c.muW : ℝ) ≤ mu)
    (ht0 : (c.tau : ℝ) ≤ (M : ℝ) / mu) (ht1 : (M : ℝ) / mu ≤ 3 / 5) (j : ℤ) :
    V22.psi ((M : ℝ) / mu) ≤ V22.fiberFunction ((1 + r) / 2) mu M j := by
  obtain ⟨hra0, hrarb, hrbh, htau, _, hmuW, hStart8⟩ := wing_class_domains hc
  have hmup : 0 < mu := by linarith
  have hr0 : 0 ≤ r := hra0.le.trans hra
  have hrh : r ≤ 1 / 2 := by linarith
  have hMq : (c.tau : ℝ) * mu ≤ M := (le_div_iff₀ hmup).1 ht0
  have hMuStart := mul_le_mul_of_nonneg_left hmu (by linarith : 0 ≤ (c.tau : ℝ))
  have hMr : (8 : ℝ) ≤ M := by nlinarith
  have hM : 8 ≤ M := by exact_mod_cast hMr
  have hN : 10 ≤ M + 2 := by omega
  have hL := outer_lower_error_from_slack hB2 hM hmup hr0 (hrb.trans hrbh) (by norm_num)
    (by norm_num) (by exact_mod_cast hN : (10 : ℝ) ≤ (M : ℝ) + 2)
    ht1 (by norm_num) hB2.1
  by_cases hwl : threeRangeW r M j ≤ 1
  · have h := source_spike_lower_range hN hr0 hrh hmup (by linarith : (M : ℝ) / mu ≤ 69 / 100) j hwl
    rw [max_eq_right (by linarith)] at h
    simpa only [sub_zero] using h
  by_cases hwm : threeRangeW r M j ≤ V22.gamma r ((M : ℝ) + 2)
  · have h := bonusRange_middle hN hr0 hrh hmup j (by linarith) hwm
    rw [← shared_psi_eq] at h
    nlinarith
  obtain ⟨cell, hcell, hid, ht⟩ := wing_cells_cover hc ht0 ht1
  obtain ⟨_, hhi, hlo0, hM0⟩ := wing_cell_domains hc hcell hid
  let M0 := (c.muW : ℝ) * (cell.lo : ℝ)
  have hMlo : M0 ≤ (M : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hmu hlo0.le
    have h2 := (le_div_iff₀ hmup).1 ht.1
    dsimp [M0]
    nlinarith
  have hNlo : V22.Checks.wingN0 c cell ≤ (M : ℝ) + 2 := by
    unfold V22.Checks.wingN0
    dsimp [M0] at hMlo
    linarith
  obtain ⟨hC, hVertex, _, _, hWmin⟩ := hWing c hc cell hcell hid ((M : ℝ) / mu) ht.1 ht.2
  rw [shared_wingC_eq] at hC
  rw [shared_wingBPrime_eq, shared_wingC_eq] at hVertex
  have hBetaCell := wing_cell_beta_monotone hBeta hc hcell hid
  have hUpper := source_wing_upper hBonus hM0 hMlo hra0 hra hrb hrbh hmup
    (by linarith : (387 / 2500 : ℝ) ≤ (M : ℝ) / mu) ht1 hBetaCell hC hVertex j (by linarith)
  have hW := hWmin ((M : ℝ) + 2) hNlo
  rw [shared_wingW_eq] at hW
  have hMin : 0 ≤ min 2 (wingW ((M : ℝ) / mu) M0 c.ra c.rb ((M : ℝ) + 2)) :=
    le_min (by norm_num) hW
  nlinarith

/-- Full source Theorem5.8 fiber domain, both activities and every integer. -/
theorem source_wing_fiber (hfin : V22.FiniteChecks) {c : V22.V22WingClass}
    (hc : c ∈ V22.wingClasses) {q mu : ℝ} {M : ℕ}
    (hra : (c.ra : ℝ) ≤ |2 * q - 1|) (hrb : |2 * q - 1| ≤ (c.rb : ℝ))
    (hmu : (c.muW : ℝ) ≤ mu) (ht0 : (c.tau : ℝ) ≤ (M : ℝ) / mu)
    (ht1 : (M : ℝ) / mu ≤ 3 / 5) (j : ℤ) :
    V22.psi ((M : ℝ) / mu) ≤ V22.fiberFunction q mu M j := by
  rcases hfin with ⟨_, _, _, _, hBeta, _, hBonus, _, _, _, _, _, hB2, _, _, hWing, _⟩
  obtain ⟨_, _, hrbh, _, _, _, _⟩ := wing_class_domains hc
  have hcap : |2 * q - 1| ≤ 1 / 4 := hrb.trans hrbh
  have hq : 0 < q ∧ q < 1 := by have h := abs_le.mp hcap; constructor <;> linarith
  by_cases hhalf : 1 / 2 ≤ q
  · have ha : (c.ra : ℝ) ≤ 2 * q - 1 := by simpa only [abs_of_nonneg (by linarith : 0 ≤ 2 * q - 1)] using hra
    have hb : 2 * q - 1 ≤ (c.rb : ℝ) := (le_abs_self _).trans hrb
    have h := wing_fiber_positive hBeta hBonus hB2 hWing hc ha hb hmu ht0 ht1 j
    simpa only [show (1 + (2 * q - 1)) / 2 = q by ring] using h
  · have ha : (c.ra : ℝ) ≤ 1 - 2 * q := by
      have h := hra
      rw [abs_of_nonpos (by linarith : 2 * q - 1 ≤ 0)] at h
      linarith
    have hb : 1 - 2 * q ≤ (c.rb : ℝ) := by have h := abs_le.mp hrb; linarith
    have h := wing_fiber_positive hBeta hBonus hB2 hWing hc ha hb hmu ht0 ht1 ((M : ℤ) - j)
    have he : (1 + (1 - 2 * q)) / 2 = 1 - q := by ring
    rw [he, shared_fiberFunction_eq, fiber_reflection hq.1 hq.2, ← shared_fiberFunction_eq] at h
    exact h

theorem wing_row_metadata {p : ℕ} (hp0 : 31 ≤ p) (hp1 : p ≤ 39) {q : ℝ}
    (hqlo : V22.Checks.rowQa p ≤ q) (hqhi : q ≤ V22.Checks.rowQb p) :
    ∃ c ∈ V22.wingClasses, (c.ra : ℝ) ≤ |2 * q - 1| ∧ |2 * q - 1| ≤ (c.rb : ℝ) ∧
      (c.muW : ℝ) ≤ V22.startingMean p ∧ V22.spikeCutoff p = (c.tau : ℝ) := by
  have h := e6_wing_tableQ p (by omega) ⟨hp0, hp1⟩
  unfold e6WingTableQ at h
  cases he : V22.wingForPiece p with
  | none => simp only [he] at h
  | some c =>
    simp only [he] at h
    obtain ⟨hc, _, hn, ha, hb, hm, hra, _, _, _, _⟩ := h
    have ha' : (c.ra : ℝ) ≤ 2 * V22.Checks.rowQa p - 1 := by rw [e6_rowQa_cast]; exact_mod_cast ha
    have hb' : 2 * V22.Checks.rowQb p - 1 ≤ (c.rb : ℝ) := by rw [e6_rowQb_cast]; exact_mod_cast hb
    have hra' : 0 < (c.ra : ℝ) := by exact_mod_cast hra
    have hs : 0 ≤ 2 * q - 1 := by linarith
    refine ⟨c, hc, ?_, ?_, ?_, ?_⟩
    · rw [abs_of_nonneg hs]; linarith
    · rw [abs_of_nonneg hs]; linarith
    · unfold V22.startingMean; exact_mod_cast hm
    · simp only [V22.spikeCutoff, hn, he]

/-- The actual inherited row and only its zero-tilt MGF constraint are
retained in the full wing source no-valley conclusion. -/
theorem source_wing_noValley (hfin : V22.FiniteChecks)
    {p : ℕ} (hp0 : 31 ≤ p) (hp1 : p ≤ 39) {q mu : ℝ}
    (hqlo : V22.Checks.rowQa p ≤ q) (hqhi : q ≤ V22.Checks.rowQb p)
    (hmu : V22.startingMean p ≤ mu) :
    NoValleyAtMGF2 q mu ((V22.pieceV22 p).theta : ℝ) ((V22.pieceV22 p).D : ℝ)
      [(1 - q, Real.exp (-V22.Checks.rowEll0 p * mu))] := by
  have hfinCopy := hfin
  rcases hfin with ⟨_, hQ, hEnv, hA3, hBeta, hBonus, hBonusPairs, _, _, hLargeT, _,
    hB1, hB2, _, hB3, _, _, _, _, _, _, hRows⟩
  have hp : p < 55 := by omega
  have hp6 : 6 ≤ p := by omega
  have hCell := central_row_cell_deficits hA3 hBonusPairs hB2 hB3 hp6 hp1 hqlo hqhi hmu
  obtain ⟨_, hExcess, _, _, _⟩ := central_row_metadata hp6 hp1
  obtain ⟨c, hc, hra, hrb, hmuW, hCut⟩ := wing_row_metadata hp0 hp1 hqlo hqhi
  obtain ⟨hMean, _⟩ := e6_startingMean_bounds hp
  have hr := central_row_r_cap hp6 hp1 hqlo hqhi
  have hmup : 0 < mu := by linarith
  apply row_noValley_of_cell_deficits hB1 hRows hp hqlo hqhi hmu (by norm_num : (0 : ℝ) ≤ 0) hCell
  intro M hM j
  have htWing : (c.tau : ℝ) ≤ (M : ℝ) / mu := by
    apply (le_div_iff₀ hmup).2
    simpa only [hCut] using hM
  by_cases htCentral : (3 / 5 : ℝ) ≤ (M : ℝ) / mu
  · have h := fiber_inequality_source hQ hEnv hBeta hBonus hLargeT hr (by linarith : 19 ≤ mu) htCentral j
    simpa only [hExcess, V22.targetLine, zero_mul, add_zero, zero_add] using h
  · have h := source_wing_fiber hfinCopy hc hra hrb (hmuW.trans hmu) htWing (le_of_not_ge htCentral) j
    simpa only [hExcess, V22.targetLine, zero_mul, add_zero, zero_add] using h

end

end Erdos993Lean.Analytic.V22.Analysis
