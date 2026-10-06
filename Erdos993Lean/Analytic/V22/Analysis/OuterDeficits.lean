import Erdos993Lean.Analytic.V22.Analysis.WindowTheorems
import Erdos993Lean.Analytic.V22.Analysis.SpikeRayBounds
import Erdos993Lean.Analytic.V22.Analysis.OuterCells

/-! Source: note Corollary 5.15, the actual all-integer deficit and the
repaired B3 minimum interface. The minimum in a window-marked certificate
is never projected to a Phi certificate. These are intermediate transport
lemmas; the final outer theorem must also discharge its native Phi bound
and its inherited row-price book. Parent owns Lean verification. -/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

theorem shared_fiberInfimum_reflection {q mu : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (M : ℕ) :
    V22.fiberInfimum (1 - q) mu M = V22.fiberInfimum q mu M := by
  obtain ⟨a, ha, hmina⟩ := shared_fiberInfimum_attained (mu := mu)
    (by linarith : 0 ≤ 1 - q) (by linarith : 1 - q ≤ 1) M
  obtain ⟨b, hb, hminb⟩ := shared_fiberInfimum_attained (mu := mu) hq0.le hq1.le M
  have hab := hmina ((M : ℤ) - b)
  have hba := hminb ((M : ℤ) - a)
  have hidx : (M : ℤ) - ((M : ℤ) - a) = a := by ring
  have hleft : V22.fiberFunction (1 - q) mu M ((M : ℤ) - b) =
      V22.fiberFunction q mu M b := by
    rw [shared_fiberFunction_eq, shared_fiberFunction_eq]
    exact fiber_reflection hq0 hq1 M b
  have hright : V22.fiberFunction q mu M ((M : ℤ) - a) =
      V22.fiberFunction (1 - q) mu M a := by
    rw [shared_fiberFunction_eq, shared_fiberFunction_eq]
    simpa only [hidx] using (fiber_reflection hq0 hq1 M ((M : ℤ) - a)).symm
  rw [hleft] at hab
  rw [hright] at hba
  rw [ha, hb]
  exact le_antisymm hab hba

theorem shared_deficitG_reflection {q mu b beta : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (M : ℕ) :
    V22.deficitG (1 - q) mu b beta M = V22.deficitG q mu b beta M := by
  unfold V22.deficitG
  rw [shared_fiberInfimum_reflection hq0 hq1]

theorem outer_deficitG_le_base_add {q mu b beta : ℝ} {M : ℕ}
    (hb : 0 ≤ b) (hbeta : 0 ≤ beta) (ht : (M : ℝ) / mu ≤ 1) :
    V22.deficitG q mu b beta M ≤ V22.deficitG q mu 0 0 M + b := by
  have hg : beta * ((M : ℝ) / mu - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hbeta (by linarith)
  unfold V22.deficitG V22.targetLine V22.positivePart
  norm_num only [zero_add, zero_mul, add_zero]
  apply max_le
  · linarith [le_max_left (V22.psi ((M : ℝ) / mu) - V22.fiberInfimum q mu M) 0]
  · linarith [le_max_right (V22.psi ((M : ℝ) / mu) - V22.fiberInfimum q mu M) 0]

theorem outer_deficitG_le_beta_zero {q mu b beta : ℝ} {M : ℕ}
    (hbeta : 0 ≤ beta) (ht : (M : ℝ) / mu ≤ 1) :
    V22.deficitG q mu b beta M ≤ V22.deficitG q mu b 0 M := by
  have hg : beta * ((M : ℝ) / mu - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hbeta (by linarith)
  unfold V22.deficitG V22.targetLine V22.positivePart
  apply max_le_max _ le_rfl
  norm_num only [zero_mul, add_zero]
  linarith

theorem outer_minimum_price_algebra {D Phi b L : ℝ} (hb : 0 ≤ b)
    (hPhi : D ≤ Phi + b) (hmin : min Phi D ≤ L) : D ≤ b + L := by
  have hself : D ≤ D + b := by linarith
  have hbase : D ≤ min (b + Phi) (b + D) := le_min (by linarith) (by linarith)
  have hid : min (b + Phi) (b + D) = b + min Phi D := by
    by_cases hPD : Phi ≤ D
    · rw [min_eq_left hPD, min_eq_left (by linarith : b + Phi ≤ b + D)]
    · have hDP : D ≤ Phi := by linarith
      rw [min_eq_right hDP, min_eq_right (by linarith : b + D ≤ b + Phi)]
  rw [hid] at hbase
  linarith

/-- Exact Corollary 5.15 B3 consumer, both markings and certified exports.
The ordinary actual deficit-to-Phi comparison is an intermediate input;
the final outer theorem must derive it from the source block/ray bound. -/
theorem outer_certified_cell_bound (hB3 : V22.Checks.lemma_7_14_certified)
    {c : V22.V22SpikeCell} (hc : c ∈ V22.spikeCells) {k : V22.V22Class}
    (hk : k ∈ V22.classes) (hid : k.classId = c.classId) {i : ℕ} (hi : i < 5)
    {q mu : ℝ} {M : ℕ} (hmu : 0 < mu) (hM : 8 ≤ M)
    (ht : V22.Checks.inCell c.lo c.hi ((M : ℝ) / mu))
    (hr : V22.Checks.inCell k.ra k.rb |2 * q - 1|)
    (hq : V22.Checks.inCell (1 / 4) (3 / 4) q)
    (hblock : V22.inSpikeBlock c i (M : ℝ)) (hmuD : (k.muD : ℝ) ≤ mu)
    (hPhi : V22.deficitG q mu 0 0 M ≤ V22.Checks.spikePhi c i ((M : ℝ) / mu) M) :
    V22.deficitG q mu k.b k.beta M ≤ (k.b : ℝ) + (c.logBounds.getD i 0 : ℝ) := by
  obtain ⟨_, _, hb, _, hbeta, _, _, htau, _⟩ := window_class_domains hk
  have hcut : (M : ℝ) / mu ≤ 1 := by
    have hcell : (c.hi : ℝ) ≤ (k.tau : ℝ) := (outer_cell_metadata hc hk hid).2.1
    exact ht.2.trans (hcell.trans htau.le)
  have hbase := outer_deficitG_le_base_add (q := q) (mu := mu) (M := M)
    (b := (k.b : ℝ)) (beta := (k.beta : ℝ)) hb hbeta hcut
  have hDPhi : V22.deficitG q mu k.b k.beta M ≤ V22.Checks.spikePhi c i ((M : ℝ) / mu) M + (k.b : ℝ) :=
    by linarith
  by_cases hmark : c.window = true
  · have hMp : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M from by omega)
    have he : (M : ℝ) / ((M : ℝ) / mu) = mu := by field_simp [hMp.ne', hmu.ne']
    have hcert := hB3.2.1 c hc hmark k hk hid i hi ((M : ℝ) / mu) q M ht hr hq hblock (by simpa only [he] using hmuD)
    rw [he] at hcert
    exact outer_minimum_price_algebra hb hDPhi hcert.2
  · have hfalse : c.window = false := Bool.eq_false_of_not_eq_true hmark
    have hcert := hB3.1 c hc hfalse i hi ((M : ℝ) / mu) (M : ℝ) ht hblock
    linarith [hcert.2]

end Erdos993Lean.Analytic.V22.Analysis
