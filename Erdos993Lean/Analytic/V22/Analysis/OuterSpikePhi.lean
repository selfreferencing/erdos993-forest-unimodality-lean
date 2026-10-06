import Erdos993Lean.Analytic.V22.Analysis.OuterLogRatio
import Erdos993Lean.Analytic.V22.Analysis.OuterLowerError
import Erdos993Lean.Analytic.V22.Analysis.OuterDeficits

/-! Source: note Corollary 5.15. Every source analytical proviso of the
finite and infinite Phi blocks is discharged from the original finite
statements and native class/cell/mean domains. The final cell theorem consumes
the repaired certified min(Phi,Def_g) interface. Parent owns compilation. -/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

/-- Exact native ordinary deficit-to-Phi transport on an outer spike block.
The coefficient validity is the numerical license exported with B3. -/
theorem outer_spike_phi_positive (hA3p : V22.Checks.lemma_7_5)
    (hA4p : V22.Checks.lemma_7_7) (hA4d : V22.Checks.lemma_7_8)
    (hA4m : V22.Checks.lemma_7_9) (hB2 : V22.Checks.lemma_7_13)
    (hD2 : V22.Checks.lemma_7_19)
    {c : V22.V22SpikeCell} (hc : c ∈ V22.spikeCells) {k : V22.V22Class}
    (hk : k ∈ V22.classes) (hid : k.classId = c.classId) {i : ℕ} (hi : i < 5)
    {M : ℕ} {r mu : ℝ} (hM : 8 ≤ M) (har : (k.ra : ℝ) ≤ r) (hrrb : r ≤ (k.rb : ℝ))
    (hmuD : (k.muD : ℝ) ≤ mu) (ht : V22.Checks.inCell c.lo c.hi ((M : ℝ) / mu))
    (hblock : V22.inSpikeBlock c i (M : ℝ))
    (hvalid : V22.Checks.spikePhiCoefficientsValid c i ((M : ℝ) / mu)) :
    V22.deficitG ((1 + r) / 2) mu 0 0 M ≤ V22.Checks.spikePhi c i ((M : ℝ) / mu) M := by
  obtain ⟨hra, hrb, _, _, _, _, _, _, _, _, hmu40, _, _⟩ := window_class_domains hk
  obtain ⟨hc0, hrm, _⟩ := outer_cell_class_fields hk hid
  obtain ⟨hlo, _, hhi, hma, _⟩ := outer_cell_metadata hc hk hid
  have hmu : 0 < mu := by linarith
  have hr0 := (hra.trans_le har).le
  have ht0 : (387/2500 : ℝ) ≤ (M : ℝ) / mu := by linarith [ht.1]
  have ht1 : (M : ℝ) / mu ≤ 69/100 := ht.2.trans hhi
  have hUL := outer_lambdaU_lower hA4p hA4d hA4m hD2 hk har hrrb hmuD (hlo.trans ht.1)
  have hL := outer_lower_error_paid hB2 hc hk hid hM har hrrb hmuD ht
  let M1 : ℝ := (V22.blockMultipliers.getD i 0 : ℕ) * (c.ma : ℝ)
  have hmult := outer_block_multiplier_ge_one hi
  have hma1 : (c.ma : ℝ) ≤ M1 := by
    have hm := mul_le_mul_of_nonneg_right hmult (show 0 ≤ (c.ma : ℝ) from by linarith)
    simpa only [one_mul] using hm
  have hM1 : 8 ≤ M1 := hma.trans hma1
  have hM1M : M1 ≤ (M : ℝ) := hblock.1
  by_cases h4 : i = 4
  · have hM1eq : M1 = 16 * (c.ma : ℝ) := by
      dsimp [M1]
      rw [h4]
      norm_num [V22.blockMultipliers]
    have hvalid' : V22.phiInfiniteBlockCoefficientsValid ((M : ℝ) / mu) M1 k.rb := by
      simpa only [V22.Checks.spikePhiCoefficientsValid, h4, if_pos, hrm, M1] using hvalid
    obtain ⟨_, _, _, _, _, hOuterBeta⟩ := hA3p
    have hBeta0 := (hOuterBeta c hc hc0).1.1
    have hBeta : ∀ N : ℝ, M1 + 2 ≤ N →
        V22.betaE (M1 + 2) k.rb (cappedNu k.rb (M1 + 2)) ≤
          V22.betaE N k.rb (cappedNu k.rb N) := by
      intro N hN
      have hm := hBeta0 (show 16 * (c.ma : ℝ) + 2 ∈ Ici (16 * (c.ma : ℝ) + 2) from by simp only [mem_Ici]; exact le_rfl)
        (show N ∈ Ici (16 * (c.ma : ℝ) + 2) from by simp only [mem_Ici]; rw [hM1eq] at hN; exact hN)
        (show 16 * (c.ma : ℝ) + 2 ≤ N from by rw [hM1eq] at hN; exact hN)
      rw [hrm] at hm
      simpa only [V22.Checks.cappedBeta, cappedNu, hM1eq] using hm
    have hPhi := source_spike_infinite_block hM hmu hM1 hM1M hr0 hrrb hrb ht0 ht1 hvalid' hBeta hUL hL
    simpa only [V22.Checks.spikePhi, h4, if_pos, hrm, M1] using hPhi
  · have hMhi : (M : ℝ) ≤ 2 * M1 := by
      rcases hblock.2 with h | h
      · exact False.elim (h4 h)
      · simpa only [M1, mul_assoc] using h
    have hvalid' : V22.phiBlockCoefficientsValid M1 (2 * M1) k.rb := by
      simpa only [V22.Checks.spikePhiCoefficientsValid, if_neg h4, hrm, M1] using hvalid
    have hPhi := source_spike_finite_block hM hmu hM1 hM1M hMhi hr0 hrrb hrb ht0 ht1 hvalid' hUL hL
    simpa only [V22.Checks.spikePhi, if_neg h4, hrm, M1] using hPhi

/-- The exact ordinary deficit-to-Phi comparison on both activity halves. -/
theorem outer_spike_phi_bound (hA3p : V22.Checks.lemma_7_5)
    (hA4p : V22.Checks.lemma_7_7) (hA4d : V22.Checks.lemma_7_8)
    (hA4m : V22.Checks.lemma_7_9) (hB2 : V22.Checks.lemma_7_13)
    (hD2 : V22.Checks.lemma_7_19)
    {c : V22.V22SpikeCell} (hc : c ∈ V22.spikeCells) {k : V22.V22Class}
    (hk : k ∈ V22.classes) (hid : k.classId = c.classId) {i : ℕ} (hi : i < 5)
    {M : ℕ} {q mu : ℝ} (hM : 8 ≤ M) (hr : V22.Checks.inCell k.ra k.rb |2*q-1|)
    (hmuD : (k.muD : ℝ) ≤ mu) (ht : V22.Checks.inCell c.lo c.hi ((M : ℝ) / mu))
    (hblock : V22.inSpikeBlock c i (M : ℝ))
    (hvalid : V22.Checks.spikePhiCoefficientsValid c i ((M : ℝ) / mu)) :
    V22.deficitG q mu 0 0 M ≤ V22.Checks.spikePhi c i ((M : ℝ) / mu) M := by
  obtain ⟨_, hrb, _⟩ := window_class_domains hk
  have hq : 0 < q ∧ q < 1 := by
    have h := abs_le.mp (hr.2.trans hrb)
    constructor <;> linarith
  by_cases hhalf : 1/2 ≤ q
  · rw [abs_of_nonneg (by linarith : 0 ≤ 2*q-1)] at hr
    have h := outer_spike_phi_positive hA3p hA4p hA4d hA4m hB2 hD2 hc hk hid hi
      hM hr.1 hr.2 hmuD ht hblock hvalid
    have he : (1 + (2*q-1))/2 = q := by ring
    simpa only [he] using h
  · rw [abs_of_nonpos (by linarith : 2*q-1 ≤ 0)] at hr
    have hlo : (k.ra : ℝ) ≤ 1-2*q := by linarith [hr.1]
    have hhi : 1-2*q ≤ (k.rb : ℝ) := by linarith [hr.2]
    have h := outer_spike_phi_positive hA3p hA4p hA4d hA4m hB2 hD2 hc hk hid hi
      hM hlo hhi hmuD ht hblock hvalid
    have he : (1 + (1-2*q))/2 = 1-q := by ring
    rw [he, shared_deficitG_reflection hq.1 hq.2] at h
    exact h

/-- Public native Corollary 5.15 price bridge for lane D: exact class, cell,
M block, real mean, both activity halves, and certified upward export.
All analytical Phi provisos are proved; the marked minimum is retained. -/
theorem outer_spike_cell_deficit (hA3p : V22.Checks.lemma_7_5)
    (hA4p : V22.Checks.lemma_7_7) (hA4d : V22.Checks.lemma_7_8)
    (hA4m : V22.Checks.lemma_7_9) (hB2 : V22.Checks.lemma_7_13)
    (hB3 : V22.Checks.lemma_7_14_certified) (hD2 : V22.Checks.lemma_7_19)
    {c : V22.V22SpikeCell} (hc : c ∈ V22.spikeCells) {k : V22.V22Class}
    (hk : k ∈ V22.classes) (hid : k.classId = c.classId) {i : ℕ} (hi : i < 5)
    {M : ℕ} {q mu : ℝ} (hM : 8 ≤ M) (hr : V22.Checks.inCell k.ra k.rb |2*q-1|)
    (hq : V22.Checks.inCell (1/4) (3/4) q) (hmuD : (k.muD : ℝ) ≤ mu)
    (ht : V22.Checks.inCell c.lo c.hi ((M : ℝ) / mu))
    (hblock : V22.inSpikeBlock c i (M : ℝ)) :
    V22.deficitG q mu k.b k.beta M ≤ (k.b : ℝ) + (c.logBounds.getD i 0 : ℝ) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hmu40, _, _⟩ := window_class_domains hk
  have hmu : 0 < mu := by linarith
  have hMp : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M from by omega)
  have he : (M : ℝ) / ((M : ℝ) / mu) = mu := by field_simp [hMp.ne', hmu.ne']
  have hvalid : V22.Checks.spikePhiCoefficientsValid c i ((M : ℝ) / mu) := by
    by_cases hmark : c.window = true
    · have hcert := hB3.2.1 c hc hmark k hk hid i hi ((M : ℝ) / mu) q M ht hr hq hblock
        (by simpa only [he] using hmuD)
      exact hcert.1
    · have hfalse : c.window = false := Bool.eq_false_of_not_eq_true hmark
      exact (hB3.1 c hc hfalse i hi ((M : ℝ) / mu) M ht hblock).1
  have hPhi := outer_spike_phi_bound hA3p hA4p hA4d hA4m hB2 hD2 hc hk hid hi
    hM hr hmuD ht hblock hvalid
  exact outer_certified_cell_bound hB3 hc hk hid hi hmu hM ht hr hq hblock hmuD hPhi

end Erdos993Lean.Analytic.V22.Analysis
