import Erdos993Lean.Analytic.V22.Analysis.SpikeAveraging
import Erdos993Lean.Analytic.V22.Analysis.E6ProfileDomains

/-!
# Section 5: the exact ROW-v21 spike-price book

The retained row, actual activity, integer fiber M, source spike cell, and
block index survive every transport. The cell deficit family below is an
intermediate interface: the source central/wing/outer consumers must prove it
from the named B3 certificates and native block bounds. A window-marked
certificate continues to mean min(Phi,Def_g), never Phi alone. All prices use
the certified logBounds, not display-rounded table entries. Parent owns Lean.
-/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set Erdos993Lean.Analytic.NoValley

noncomputable section

theorem row_fold_max_initial_le (a : ℝ) (xs : List ℝ) : a ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => simp
  | cons b xs ih =>
    simpa only [List.foldl_cons] using (le_max_left a b).trans (ih (max a b))

theorem row_fold_max_mem_le {xs : List ℝ} {x : ℝ} (a : ℝ) (hx : x ∈ xs) :
    x ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => simp at hx
  | cons b xs ih =>
    simp only [List.mem_cons] at hx
    rcases hx with hxb | hx
    · rw [hxb]
      simpa only [List.foldl_cons] using (le_max_right a b).trans (row_fold_max_initial_le (max a b) xs)
    · simpa only [List.foldl_cons] using ih (max a b) hx

theorem row_maxList_nonneg (xs : List ℝ) : 0 ≤ V22.Checks.maxList xs :=
  row_fold_max_initial_le 0 xs

theorem row_smallPrice_le_Za {p M : ℕ} (hM : M < 8) :
    V22.Checks.rowSmallPrice p M ≤ V22.Checks.rowZa p := by
  unfold V22.Checks.rowZa V22.Checks.maxList
  exact row_fold_max_mem_le 0 (List.mem_map.mpr ⟨M, List.mem_range.mpr hM, rfl⟩)

theorem row_blockPrice_le_Zb {p i : ℕ} {cell : V22.V22SpikeCell}
    (hc : cell ∈ V22.spikeCells) (hUsed : V22.Checks.rowUsesCell p cell) (hi : i < 5) :
    V22.Checks.rowBlockPrice p cell i ≤ V22.Checks.rowZb p := by
  unfold V22.Checks.rowZb V22.Checks.maxList
  apply row_fold_max_mem_le 0
  apply List.mem_flatMap.mpr
  refine ⟨cell, hc, ?_⟩
  rw [if_pos hUsed]
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

def rowCutoffQ (p : ℕ) : ℚ := match V22.classForPiece p with
  | some c => c.tau
  | none => match V22.wingForPiece p with
    | some c => c.tau
    | none => 3 / 5

theorem row_cutoff_tableQ : ∀ p < 55, 0 < rowCutoffQ p ∧ rowCutoffQ p ≤ 1 := by
  decide +kernel

theorem row_cutoff_eq_cast (p : ℕ) : V22.spikeCutoff p = (rowCutoffQ p : ℝ) := by
  unfold V22.spikeCutoff rowCutoffQ
  cases V22.classForPiece p with
  | some c => rfl
  | none =>
    cases V22.wingForPiece p with
    | some c => rfl
    | none => norm_num

theorem row_cutoff_bounds {p : ℕ} (hp : p < 55) :
    0 < V22.spikeCutoff p ∧ V22.spikeCutoff p ≤ 1 := by
  rw [row_cutoff_eq_cast]
  obtain ⟨h0, h1⟩ := row_cutoff_tableQ p hp
  constructor
  · exact_mod_cast h0
  · exact_mod_cast h1

/-- Dropping the nonnegative target slope is valid only below t=1. -/
theorem row_spike_price_beta_zero {q mu b beta ell : ℝ} {M : ℕ}
    (hq : q < 1) (hbeta : 0 ≤ beta) (ht : (M : ℝ) / mu ≤ 1) :
    spikeAtomPrice q mu b beta ell M ≤ spikeAtomPrice q mu b 0 ell M := by
  have hg := mul_nonpos_of_nonneg_of_nonpos hbeta (show (M : ℝ) / mu - 1 ≤ 0 by linarith only [ht])
  have hd : V22.deficitG q mu b beta M ≤ V22.deficitG q mu b 0 M := by
    unfold V22.deficitG V22.targetLine V22.positivePart
    apply max_le_max _ le_rfl
    norm_num only [zero_mul, add_zero]
    linarith only [hg]
  unfold spikeAtomPrice
  exact mul_le_mul_of_nonneg_left hd (mul_nonneg
    (div_nonneg (by norm_num) (pow_nonneg (by linarith only [hq]) _)) (Real.exp_pos _).le)

/-- The exact small-M branches and provisos in ROW-v21 discharge Lemma5.3. -/
theorem row_small_spike_price (hB1 : V22.Checks.lemma_7_12) (hRows : V22.Checks.lemma_7_21)
    {p M : ℕ} (hp : p < 55) (hM : M < 8) {q mu beta : ℝ}
    (hqlo : V22.Checks.rowQa p ≤ q) (hqhi : q ≤ V22.Checks.rowQb p)
    (hmu : V22.startingMean p ≤ mu) (hbeta : 0 ≤ beta) :
    spikeAtomPrice q mu (V22.excess p) beta (V22.Checks.rowEll0 p) M ≤ V22.Checks.rowSmallPrice p M := by
  obtain ⟨hqa, _, hqb, _, _, _, _, _, _, _⟩ := e6_row_bounds hp
  obtain ⟨hm0, hb0, hb1, hell, _, hsmall, _, _, _⟩ := hRows p hp
  have hmup : 0 < mu := by linarith only [hm0, hmu]
  have hq : q < 1 := by linarith only [hqb, hqhi]
  have hMr : (M : ℝ) < 8 := by exact_mod_cast hM
  have ht : (M : ℝ) / mu ≤ 1 := (div_le_iff₀ hmup).2 (by linarith only [hMr, hm0, hmu])
  have hdrop := row_spike_price_beta_zero (M := M) (b := V22.excess p)
    (ell := V22.Checks.rowEll0 p) hq hbeta ht
  have hsource := source_small_spike_price hB1 (by omega : M ≤ 7)
    hqa (by linarith only [hqb] : V22.Checks.rowQb p ≤ 3 / 4) hqlo hqhi hm0 hmu hell hb0 hb1
  have hA : V22.Checks.smallFiberK M /
      (4 * gaussianA * Real.sqrt (min (V22.Checks.rowQa p * (1 - V22.Checks.rowQa p))
        (V22.Checks.rowQb p * (1 - V22.Checks.rowQb p)))) = V22.Checks.rowA p M := by
    simp only [V22.Checks.rowA, V22.Checks.rowVmin, shared_gaussianAmplitude_eq]
  simp only [hA] at hsource
  have hside := hsmall M hM
  have hbaseq : 0 ≤ 1 - V22.Checks.rowQb p := by linarith only [hqb]
  have hpower : Real.rpow (1 - V22.Checks.rowQb p) (-(M : ℝ)) =
      1 / (1 - V22.Checks.rowQb p) ^ M := by
    simpa only [Real.rpow_natCast, one_div] using
      (Real.rpow_neg hbaseq (M : ℝ))
  by_cases hbase : 0 < V22.Checks.rowSmallBase p M
  · have hstart := hside.1 hbase
    have hbound := hsource.1 (by simpa only [V22.Checks.rowSmallBase] using hstart)
    have he : V22.Checks.rowSmallPrice p M =
        V22.Checks.rowSmallBase p M * (1 / (1 - V22.Checks.rowQb p) ^ M) *
          Real.exp (-V22.Checks.rowEll0 p * V22.startingMean p) := by
      simp only [V22.Checks.rowSmallPrice, if_pos hbase, hpower]
    change spikeAtomPrice q mu (V22.excess p) 0 (V22.Checks.rowEll0 p) M ≤
      max (V22.Checks.rowSmallBase p M) 0 * (1 / (1 - V22.Checks.rowQb p) ^ M) *
        Real.exp (-V22.Checks.rowEll0 p * V22.startingMean p) at hbound
    rw [max_eq_left hbase.le] at hbound
    rw [he]
    exact hdrop.trans hbound
  · have hbase0 : V22.Checks.rowSmallBase p M ≤ 0 := le_of_not_gt hbase
    have hbound := hsource.2 (by simpa only [V22.Checks.rowSmallBase] using hbase0) (hside.2 hbase0)
    have he : V22.Checks.rowSmallPrice p M =
        (V22.Checks.rowA p M * (V22.startingMean p) ^ (3 / 2 : ℝ)) *
          (1 / (1 - V22.Checks.rowQb p) ^ M) * Real.exp (-V22.Checks.rowEll0 p * V22.startingMean p) := by
      simp only [V22.Checks.rowSmallPrice, if_neg hbase, hpower, Real.rpow_eq_pow]
    rw [he]
    exact hdrop.trans hbound

theorem row_very_small_spike_price (hRows : V22.Checks.lemma_7_21)
    {p M : ℕ} (hp : p < 55) (hM : 8 ≤ M) {q mu beta : ℝ}
    (hqlo : V22.Checks.rowQa p ≤ q) (hqhi : q ≤ V22.Checks.rowQb p)
    (hmu : V22.startingMean p ≤ mu) (hbeta : 0 ≤ beta)
    (hcut : (M : ℝ) / mu < 11 / 50) :
    spikeAtomPrice q mu (V22.excess p) beta (V22.Checks.rowEll0 p) M ≤ V22.Checks.rowZc p := by
  obtain ⟨hqa, _, hqb, _, _, _, _, _, _, _⟩ := e6_row_bounds hp
  obtain ⟨hm0, hb0, _, _, _, _, hdecay, _, _⟩ := hRows p hp
  have hmup : 0 < mu := by linarith only [hm0, hmu]
  have hdrop := row_spike_price_beta_zero (q := q) (mu := mu) (beta := beta)
    (M := M) (b := V22.excess p)
    (ell := V22.Checks.rowEll0 p) (by linarith only [hqb, hqhi] : q < 1) hbeta
      (by linarith only [hcut])
  have hsource := source_very_small_spike_price (qa := V22.Checks.rowQa p)
    (qb := V22.Checks.rowQb p) (q := q) (mu := mu) (mu0 := V22.startingMean p)
    (ell := V22.Checks.rowEll0 p) (b := V22.excess p) (M := M)
    hqa (by linarith only [hqb] : V22.Checks.rowQb p ≤ 3 / 4)
    hqlo hqhi hb0 hmu hM ((div_lt_iff₀ hmup).1 hcut)
    (by simpa only [V22.Checks.rowSmallRate, V22.Checks.rowMc, V22.Checks.rowLb] using hdecay)
  exact hdrop.trans (by
    simpa only [V22.Checks.rowZc, V22.Checks.rowMc, V22.Checks.rowVmin,
      V22.Checks.rowSmallRate, V22.Checks.rowLb, shared_gaussianAmplitude_eq] using hsource)

/-- The two exact exponential transport exponents of the row recipe. -/
theorem row_block_weight {p M : ℕ} {cell : V22.V22SpikeCell} {i : ℕ} {q mu : ℝ}
    (hqlo : V22.Checks.rowQa p ≤ q) (hqhi : q ≤ V22.Checks.rowQb p)
    (hqa : 1 / 4 ≤ V22.Checks.rowQa p) (hqb : V22.Checks.rowQb p ≤ 3 / 4)
    (hmu0 : 0 < V22.startingMean p) (hmu : V22.startingMean p ≤ mu)
    (hM : 8 ≤ M) (hlo : 0 ≤ (cell.lo : ℝ))
    (ht : V22.Checks.inCell cell.lo cell.hi ((M : ℝ) / mu))
    (hblock : V22.inSpikeBlock cell i (M : ℝ)) (hell : 0 < V22.Checks.rowEll0 p)
    (hdecay : V22.Checks.rowLb p < V22.Checks.rowEll0 p / (cell.hi : ℝ)) :
    (1 / (1 - q) ^ M) * Real.exp (-V22.Checks.rowEll0 p * mu) ≤
      Real.exp (-V22.Checks.rowBlockExponent p cell i) := by
  have hmup : 0 < mu := hmu0.trans_le hmu
  have hMr : (8 : ℝ) ≤ M := by exact_mod_cast hM
  have hMp : 0 < (M : ℝ) := by linarith only [hMr]
  have htb : 0 < (cell.hi : ℝ) := (div_pos hMp hmup).trans_le ht.2
  have hq0 : 0 ≤ q := by linarith only [hqa, hqlo]
  have hq1 : q < 1 := by linarith only [hqb, hqhi]
  have hqb1 : V22.Checks.rowQb p < 1 := by linarith only [hqb]
  have hLB : 0 ≤ V22.Checks.rowLb p := by
    unfold V22.Checks.rowLb
    have hlog := Real.log_le_log (show 0 < 1 - V22.Checks.rowQb p by linarith only [hqb1])
      (show 1 - V22.Checks.rowQb p ≤ 1 by linarith only [hqa, hqlo, hqhi])
    simpa only [Real.log_one, neg_nonneg] using hlog
  have hlog : -Real.log (1 - q) ≤ V22.Checks.rowLb p :=
    neg_le_neg (Real.log_le_log (by linarith only [hqb1] : 0 < 1 - V22.Checks.rowQb p)
      (by linarith only [hqhi] : 1 - V22.Checks.rowQb p ≤ 1 - q))
  have hML : V22.Checks.rowBlockMlow p cell i ≤ (M : ℝ) := by
    have htaMu : (cell.lo : ℝ) * mu ≤ M := (le_div_iff₀ hmup).1 ht.1
    have htaStart := mul_le_mul_of_nonneg_left hmu hlo
    unfold V22.Checks.rowBlockMlow
    exact max_le (max_le hblock.1 hMr) (htaStart.trans htaMu)
  have hRate1 : 0 ≤ V22.Checks.rowEll0 p / (cell.hi : ℝ) - V22.Checks.rowLb p :=
    sub_nonneg.mpr hdecay.le
  have hRate2 : 0 ≤ V22.Checks.rowEll0 p - (cell.hi : ℝ) * V22.Checks.rowLb p := by
    have hdecay' := (lt_div_iff₀ htb).1 hdecay
    nlinarith only [hdecay']
  have hMhi : (M : ℝ) / (cell.hi : ℝ) ≤ mu := by
    apply (div_le_iff₀ htb).2
    have h := (div_le_iff₀ hmup).1 ht.2
    simpa only [mul_comm] using h
  have hExp1 : (V22.Checks.rowEll0 p / (cell.hi : ℝ) - V22.Checks.rowLb p) *
      V22.Checks.rowBlockMlow p cell i ≤ V22.Checks.rowEll0 p * mu - V22.Checks.rowLb p * M := by
    have h1 := mul_le_mul_of_nonneg_left hML hRate1
    have h2 := mul_le_mul_of_nonneg_left hMhi hell.le
    have he : V22.Checks.rowEll0 p * ((M : ℝ) / (cell.hi : ℝ)) =
        V22.Checks.rowEll0 p / (cell.hi : ℝ) * M := by ring
    rw [he] at h2
    calc
      (V22.Checks.rowEll0 p / (cell.hi : ℝ) - V22.Checks.rowLb p) *
          V22.Checks.rowBlockMlow p cell i ≤
          (V22.Checks.rowEll0 p / (cell.hi : ℝ) - V22.Checks.rowLb p) * M := h1
      _ = V22.Checks.rowEll0 p / (cell.hi : ℝ) * M - V22.Checks.rowLb p * M := by ring
      _ ≤ V22.Checks.rowEll0 p * mu - V22.Checks.rowLb p * M := sub_le_sub_right h2 _
  have hExp2 : (V22.Checks.rowEll0 p - (cell.hi : ℝ) * V22.Checks.rowLb p) * V22.startingMean p ≤
      V22.Checks.rowEll0 p * mu - V22.Checks.rowLb p * M := by
    have h1 := mul_le_mul_of_nonneg_left hmu hRate2
    have h2 := mul_le_mul_of_nonneg_left ((div_le_iff₀ hmup).1 ht.2) hLB
    calc
      (V22.Checks.rowEll0 p - (cell.hi : ℝ) * V22.Checks.rowLb p) * V22.startingMean p ≤
          (V22.Checks.rowEll0 p - (cell.hi : ℝ) * V22.Checks.rowLb p) * mu := h1
      _ = V22.Checks.rowEll0 p * mu - V22.Checks.rowLb p * ((cell.hi : ℝ) * mu) := by ring
      _ ≤ V22.Checks.rowEll0 p * mu - V22.Checks.rowLb p * M := sub_le_sub_left h2 _
  have hMax := max_le hExp1 hExp2
  have hlogM := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
  have hInv : 1 / (1 - q) ^ M = Real.exp (-(M : ℝ) * Real.log (1 - q)) := by
    rw [show -(M : ℝ) * Real.log (1 - q) = -Real.log ((1 - q) ^ M) by
        rw [Real.log_pow] <;> ring,
      Real.exp_neg, Real.exp_log (pow_pos (sub_pos.mpr hq1) M)] <;>
      simp only [one_div]
  rw [hInv, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  calc
    -(M : ℝ) * Real.log (1 - q) + -V22.Checks.rowEll0 p * mu =
        (M : ℝ) * (-Real.log (1 - q)) - V22.Checks.rowEll0 p * mu := by ring
    _ ≤ (M : ℝ) * V22.Checks.rowLb p - V22.Checks.rowEll0 p * mu :=
      sub_le_sub_right hlogM _
    _ = -(V22.Checks.rowEll0 p * mu - V22.Checks.rowLb p * M) := by ring
    _ ≤ -V22.Checks.rowBlockExponent p cell i := neg_le_neg hMax

/-- The actual deficit certificate supplies positivity of its total price;
no lossy projection from a window-marked minimum is made here. -/
theorem row_block_spike_price {p M : ℕ} {cell : V22.V22SpikeCell} {i : ℕ} {q mu beta : ℝ}
    (hqlo : V22.Checks.rowQa p ≤ q) (hqhi : q ≤ V22.Checks.rowQb p)
    (hqa : 1 / 4 ≤ V22.Checks.rowQa p) (hqb : V22.Checks.rowQb p ≤ 3 / 4)
    (hmu0 : 0 < V22.startingMean p) (hmu : V22.startingMean p ≤ mu)
    (hM : 8 ≤ M) (hlo : 0 ≤ (cell.lo : ℝ))
    (ht : V22.Checks.inCell cell.lo cell.hi ((M : ℝ) / mu))
    (hblock : V22.inSpikeBlock cell i (M : ℝ)) (hell : 0 < V22.Checks.rowEll0 p)
    (hdecay : V22.Checks.rowLb p < V22.Checks.rowEll0 p / (cell.hi : ℝ))
    (hDef : V22.deficitG q mu (V22.excess p) beta M ≤ (cell.logBounds.getD i 0 : ℝ) + V22.excess p) :
    spikeAtomPrice q mu (V22.excess p) beta (V22.Checks.rowEll0 p) M ≤ V22.Checks.rowBlockPrice p cell i := by
  have hDef0 : 0 ≤ V22.deficitG q mu (V22.excess p) beta M := le_max_right _ _
  have hC0 : 0 ≤ (cell.logBounds.getD i 0 : ℝ) + V22.excess p := hDef0.trans hDef
  have hw := row_block_weight hqlo hqhi hqa hqb hmu0 hmu hM hlo ht hblock hell hdecay
  have hW0 : 0 ≤ (1 / (1 - q) ^ M) * Real.exp (-V22.Checks.rowEll0 p * mu) :=
    mul_nonneg (div_nonneg (by norm_num) (pow_nonneg (by linarith only [hqhi, hqb]) _)) (Real.exp_pos _).le
  have hD := mul_le_mul_of_nonneg_left hDef hW0
  have hP := mul_le_mul_of_nonneg_right hw hC0
  unfold spikeAtomPrice V22.Checks.rowBlockPrice
  refine hD.trans ?_
  calc
    _ ≤ Real.exp (-V22.Checks.rowBlockExponent p cell i) *
        ((cell.logBounds.getD i 0 : ℝ) + V22.excess p) := hP
    _ = ((cell.logBounds.getD i 0 : ℝ) + V22.excess p) *
        Real.exp (-V22.Checks.rowBlockExponent p cell i) := mul_comm _ _

/-- A retained cell/block deficit family. Central, wing, and outer final
theorems construct this family from the named source certificates. -/
def rowPriceCellDeficits (p : ℕ) (q mu beta : ℝ) : Prop :=
  ∀ M : ℕ, 8 ≤ M → (21 / 100 : ℝ) ≤ (M : ℝ) / mu →
    (M : ℝ) / mu < V22.spikeCutoff p →
    ∃ cell ∈ V22.spikeCells, V22.Checks.rowUsesCell p cell ∧
      0 ≤ (cell.lo : ℝ) ∧ V22.Checks.inCell cell.lo cell.hi ((M : ℝ) / mu) ∧
      ∃ i : ℕ, i < 5 ∧ V22.inSpikeBlock cell i (M : ℝ) ∧
        V22.deficitG q mu (V22.excess p) beta M ≤ (cell.logBounds.getD i 0 : ℝ) + V22.excess p

/-- ROW-v21: exact max(Za,Zb,Zc) bounds every native spike atom. The only
intermediate analytic input is the identity-preserving cell/block family,
which is consumed immediately and must be discharged by the source theorem. -/
theorem row_spike_price_book (hB1 : V22.Checks.lemma_7_12) (hRows : V22.Checks.lemma_7_21)
    {p : ℕ} (hp : p < 55) {q mu beta : ℝ}
    (hqlo : V22.Checks.rowQa p ≤ q) (hqhi : q ≤ V22.Checks.rowQb p)
    (hmu : V22.startingMean p ≤ mu) (hbeta : 0 ≤ beta)
    (hCells : rowPriceCellDeficits p q mu beta) :
    spikeMaxPrice q mu (V22.excess p) beta (V22.Checks.rowEll0 p) (V22.spikeCutoff p) ≤
      max (V22.Checks.rowZa p) (max (V22.Checks.rowZb p) (V22.Checks.rowZc p)) := by
  obtain ⟨hqa, _, hqb, _, _, _, _, _, _, _⟩ := e6_row_bounds hp
  obtain ⟨hm0, _, _, hell, _, _, _, hdecay, _⟩ := hRows p hp
  have hmu0 : 0 < V22.startingMean p := by linarith only [hm0]
  have hmup : 0 < mu := hmu0.trans_le hmu
  obtain ⟨hcut0, hcut1⟩ := row_cutoff_bounds hp
  have hcut := mul_pos hcut0 hmup
  unfold spikeMaxPrice
  rw [dif_pos hcut]
  apply Finset.sup'_le
  intro M hMr
  have hMcut : (M : ℝ) < V22.spikeCutoff p * mu := Nat.lt_ceil.mp (Finset.mem_range.mp hMr)
  have htcut : (M : ℝ) / mu < V22.spikeCutoff p := (div_lt_iff₀ hmup).2 hMcut
  by_cases hSmall : M < 8
  · exact ((row_small_spike_price hB1 hRows hp hSmall hqlo hqhi hmu hbeta).trans
      (row_smallPrice_le_Za hSmall)).trans (le_max_left _ _)
  have hM8 : 8 ≤ M := by omega
  by_cases hVery : (M : ℝ) / mu < 11 / 50
  · exact (row_very_small_spike_price hRows hp hM8 hqlo hqhi hmu hbeta hVery).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  have ht21 : (21 / 100 : ℝ) ≤ (M : ℝ) / mu := by linarith only [hVery]
  obtain ⟨cell, hc, hUsed, hlo, ht, i, hi, hblock, hDef⟩ := hCells M hM8 ht21 htcut
  have hBlock := row_block_spike_price hqlo hqhi hqa (by linarith only [hqb] : V22.Checks.rowQb p ≤ 3 / 4)
    hmu0 hmu hM8 hlo ht hblock hell (hdecay cell hc hUsed) hDef
  exact (hBlock.trans (row_blockPrice_le_Zb hc hUsed hi)).trans
    ((le_max_left _ _).trans (le_max_right _ _))

/-- Increasing the real mean preserves the source strict row margin, since
both retained negative moment costs decrease and the price book is fixed. -/
theorem row_spike_margin (hB1 : V22.Checks.lemma_7_12) (hRows : V22.Checks.lemma_7_21)
    {p : ℕ} (hp : p < 55) {q mu beta : ℝ}
    (hqlo : V22.Checks.rowQa p ≤ q) (hqhi : q ≤ V22.Checks.rowQb p)
    (hmu : V22.startingMean p ≤ mu) (hbeta : 0 ≤ beta)
    (hCells : rowPriceCellDeficits p q mu beta) :
    0 < 1 + V22.excess p - ((V22.pieceV22 p).theta : ℝ) -
      9 * ((V22.pieceV22 p).D : ℝ) / (2 * mu) -
      (V22.Checks.rowRhi p) ^ 2 / ((1 - (V22.Checks.rowRhi p) ^ 2) * mu) -
      spikeMaxPrice q mu (V22.excess p) beta (V22.Checks.rowEll0 p) (V22.spikeCutoff p) := by
  obtain ⟨hqa, _, hqb, _, _, hD, _, _, _, _⟩ := e6_row_bounds hp
  obtain ⟨hm0, _, _, _, _, _, _, _, hmargin⟩ := hRows p hp
  have hmup0 : 0 < V22.startingMean p := by linarith only [hm0]
  have hmup : 0 < mu := hmup0.trans_le hmu
  have hPrice := row_spike_price_book hB1 hRows hp hqlo hqhi hmu hbeta hCells
  have hCap : (V22.Checks.rowRhi p) ^ 2 < 1 := by
    exact (spike_endpoint_r_cap hqa (by linarith only [hqb] : V22.Checks.rowQb p ≤ 3 / 4) hqlo hqhi).1
  have hd : 0 < 1 - (V22.Checks.rowRhi p) ^ 2 := by linarith only [hCap]
  have hDcost : 9 * ((V22.pieceV22 p).D : ℝ) / (2 * mu) ≤
      9 * ((V22.pieceV22 p).D : ℝ) / (2 * V22.startingMean p) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith only [hmu])
  have hRcost : (V22.Checks.rowRhi p) ^ 2 / ((1 - (V22.Checks.rowRhi p) ^ 2) * mu) ≤
      (V22.Checks.rowRhi p) ^ 2 / ((1 - (V22.Checks.rowRhi p) ^ 2) * V22.startingMean p) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos hd hmup0) (mul_le_mul_of_nonneg_left hmu hd.le)
  unfold V22.Checks.rowMargin at hmargin
  linarith only [hmargin, hDcost, hRcost, hPrice]

/-- Immediate actual-mixture consumer. The final source central/wing/outer
theorem supplies both retained native fiber families and adds no new
moment, tail, or scalar-pricing assumption to its final statement. -/
theorem row_noValley_of_cell_deficits (hB1 : V22.Checks.lemma_7_12) (hRows : V22.Checks.lemma_7_21)
    {p : ℕ} (hp : p < 55) {q mu beta : ℝ}
    (hqlo : V22.Checks.rowQa p ≤ q) (hqhi : q ≤ V22.Checks.rowQb p)
    (hmu : V22.startingMean p ≤ mu) (hbeta : 0 ≤ beta)
    (hCells : rowPriceCellDeficits p q mu beta)
    (hf : ∀ M : ℕ, V22.spikeCutoff p * mu ≤ (M : ℝ) → ∀ j : ℤ,
      V22.psi ((M : ℝ) / mu) + V22.targetLine (V22.excess p) beta ((M : ℝ) / mu) ≤ V22.fiberFunction q mu M j) :
    NoValleyAtMGF2 q mu ((V22.pieceV22 p).theta : ℝ) ((V22.pieceV22 p).D : ℝ)
      [(1 - q, Real.exp (-V22.Checks.rowEll0 p * mu))] := by
  obtain ⟨hqa, _, hqb, _, _, _, _, _, _, _⟩ := e6_row_bounds hp
  obtain ⟨hm0, hb0, _, _, _, _, _, _, _⟩ := hRows p hp
  obtain ⟨hcut0, hcut1⟩ := row_cutoff_bounds hp
  exact source_spike_averaging hqa (by linarith only [hqb] : V22.Checks.rowQb p ≤ 3 / 4) hqlo hqhi
    (by linarith only [hm0, hmu] : 0 < mu) hcut0 hcut1 hb0 hbeta hf
    (row_spike_margin hB1 hRows hp hqlo hqhi hmu hbeta hCells)

end

end Erdos993Lean.Analytic.V22.Analysis
