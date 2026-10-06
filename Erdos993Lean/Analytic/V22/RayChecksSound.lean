import Erdos993Lean.Analytic.V22.Compute.RayChecks
import Erdos993Lean.Analytic.V22.RayEnvelopeSound
import Erdos993Lean.Analytic.V22.PhiRayMonotone
import Erdos993Lean.Analytic.V22.RootShapeSound
import Erdos993Lean.Analytic.V22.GridSound
import Erdos993Lean.Analytic.V22.Checks.EarlyStatements

/-!
# B3 ray coverage and actual-M transport

The finite or infinite block's remainder remains frozen while its actual
real `M` increases. RootShapeSound supplies the actual `G2` positivity,
not an independent root assumption. Successful piece guards supply every
coefficient-validity hypothesis. Exact partition coverage supplies every
actual `t`; the stronger six-digit export is then lifted to Table 4 using
a separately checked rational inequality. Window blocks with a pure-ray
certificate can be consumed through `min_le_left` without losing any of
the window statement's hypotheses.
-/

namespace Erdos993Lean.Analytic.V22.Compute.RayChecks

open GeneratedRayData

theorem rm_cast (c : V22SpikeCell) : (rm c : ℝ) = spikeRm c := by
  cases hfind : classes.find? (fun k => k.classId == c.classId) with
  | none => norm_num [rm, spikeRm, spikeClass, hfind]
  | some k => simp [rm, spikeRm, spikeClass, hfind]

theorem m1_cast (c : V22SpikeCell) (i : Nat) :
    (m1 c i : ℝ) = (blockMultipliers.getD i 0 : ℝ) * (c.ma : ℝ) := by
  simp [m1, blockMultipliers]

theorem piecePass_endpoint_sound {c : V22SpikeCell} {i : Nat} {p : RayPiece}
    (h : piecePass c i p = true) {t : ℝ}
    (ht : (p.tspan.1 : ℝ) ≤ t ∧ t ≤ (p.tspan.2 : ℝ))
    (ht0 : 0 ≤ t) (hm : 8 ≤ (m1 c i : ℝ)) :
    Checks.spikePhiCoefficientsValid c i t ∧
      Checks.spikePhi c i t (m1 c i : ℝ) ≤ (c.logBounds.getD i 0 : ℝ) := by
  have henv := spanEnv_mem ht
  by_cases hi : i = 4
  · have hp : RayExprs.infinitePass p.brackets (spanEnv p.tspan) (.var 0)
        (.rat (m1 c i)) (m1 c i) (rm c) (c.logBounds.getD i 0) = true := by
      simpa only [piecePass, if_pos hi] using h
    have hs := RayExprs.infinitePass_sound (realSpanEnv t) p.brackets (.var 0)
      (.rat (m1 c i)) (m1 c i) (rm c) (c.logBounds.getD i 0) henv hp
    simpa [Checks.spikePhi, Checks.spikePhiCoefficientsValid, hi, Expr.evalR,
      realSpanEnv, m1_cast, rm_cast] using hs
  · have hp : RayEnvelope.finitePass p.brackets
        ⟨p.methods, p.firstUniversal, p.secondUniversal⟩ (spanEnv p.tspan)
        (.var 0) (.rat (m1 c i)) (m1 c i) (2 * m1 c i) (rm c)
        (c.logBounds.getD i 0) = true := by
      simpa only [piecePass, if_neg hi] using h
    have ht' : 0 ≤ (Expr.var 0).evalR (realSpanEnv t) := by
      simpa [Expr.evalR, realSpanEnv] using ht0
    have hm' : 0 < (Expr.rat (m1 c i)).evalR (realSpanEnv t) := by
      simp only [Expr.evalR]
      linarith
    have hs := RayEnvelope.finitePass_sound (realSpanEnv t) p.brackets
      ⟨p.methods, p.firstUniversal, p.secondUniversal⟩ (.var 0) (.rat (m1 c i))
      (m1 c i) (2 * m1 c i) (rm c) (c.logBounds.getD i 0) henv ht' hm' hp
    simpa [Checks.spikePhi, Checks.spikePhiCoefficientsValid, hi, Expr.evalR,
      realSpanEnv, m1_cast, rm_cast] using hs

/-- The actual fiber parameter varies; both block endpoints remain frozen. -/
theorem spikePhi_le_endpoint {c : V22SpikeCell} {i : Nat} {t M : ℝ}
    (ht : 0 ≤ t) (hm1 : 8 ≤ (m1 c i : ℝ)) (hM : inSpikeBlock c i M) :
    Checks.spikePhi c i t M ≤ Checks.spikePhi c i t (m1 c i : ℝ) := by
  have hM1 : (m1 c i : ℝ) ≤ M := by
    simpa only [m1_cast] using hM.1
  have hg2 : 0 ≤ G2 (lambdaT t) := (G2_pos (lambdaT t)).le
  by_cases hi : i = 4
  · have hs := phiWithRemainder_antitone_parameter ht hm1 hM1 hg2
      (D := phiInfiniteBlockRemainder t (m1 c i : ℝ) (spikeRm c))
    simpa only [Checks.spikePhi, if_pos hi, phiInfiniteBlock, m1_cast] using hs
  · have hs := phiWithRemainder_antitone_parameter ht hm1 hM1 hg2
      (D := phiBlockRemainder t (m1 c i : ℝ) (2 * (m1 c i : ℝ)) (spikeRm c))
    simpa only [Checks.spikePhi, if_neg hi, phiBlock, m1_cast] using hs

/-- Generic soundness for any actual cell/index with the checked exact key. -/
theorem blockOK_log_sound {c : V22SpikeCell} {i : Nat} {b : RayBlock}
    (h : blockOK c i b = true) {t M : ℝ}
    (ht : Checks.inCell c.lo c.hi t) (hM : inSpikeBlock c i M) :
    Checks.spikePhiCoefficientsValid c i t ∧
      Checks.spikePhi c i t M ≤ (c.logBounds.getD i 0 : ℝ) := by
  simp only [blockOK, Bool.and_eq_true] at h
  have hd := h.1.1.2
  simp only [domainOK, decide_eq_true_eq] at hd
  have hlo : (0 : ℝ) ≤ (c.lo : ℝ) := by exact_mod_cast hd.2.1
  have hm1 : (8 : ℝ) ≤ (m1 c i : ℝ) := by exact_mod_cast hd.2.2.1
  have ht0 : 0 ≤ t := hlo.trans ht.1
  obtain ⟨s, hs, hts⟩ := partitionFrom_covers h.1.2 ht
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
  have hend := piecePass_endpoint_sound ((List.all_eq_true.mp h.2) p hp) hts ht0 hm1
  exact ⟨hend.1, (spikePhi_le_endpoint ht0 hm1 hM).trans hend.2⟩

theorem blockOK_sound {c : V22SpikeCell} {i : Nat} {b : RayBlock}
    (h : blockOK c i b = true) {t M : ℝ}
    (ht : Checks.inCell c.lo c.hi t) (hM : inSpikeBlock c i M) :
    Checks.spikePhiCoefficientsValid c i t ∧
      Checks.spikePhi c i t M ≤ (c.bounds.getD i 0 : ℝ) := by
  have hs := blockOK_log_sound h ht hM
  have hd := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1).2
  simp only [domainOK, decide_eq_true_eq] at hd
  have hup : (c.logBounds.getD i 0 : ℝ) ≤ (c.bounds.getD i 0 : ℝ) := by
    exact_mod_cast hd.2.2.2
  exact ⟨hs.1, hs.2.trans hup⟩

theorem checkedBlockOK_log_sound {blocks : List RayBlock} {c : V22SpikeCell} {i : Nat}
    (h : checkedBlockOK blocks c i = true) {t M : ℝ}
    (ht : Checks.inCell c.lo c.hi t) (hM : inSpikeBlock c i M) :
    Checks.spikePhiCoefficientsValid c i t ∧
      Checks.spikePhi c i t M ≤ (c.logBounds.getD i 0 : ℝ) := by
  cases hf : blockFor blocks c i with
  | none => simp [checkedBlockOK, hf] at h
  | some b =>
      have hp : blockOK c i b = true := by simpa [checkedBlockOK, hf] using h
      exact blockOK_log_sound hp ht hM

theorem checkedBlockOK_sound {blocks : List RayBlock} {c : V22SpikeCell} {i : Nat}
    (h : checkedBlockOK blocks c i = true) {t M : ℝ}
    (ht : Checks.inCell c.lo c.hi t) (hM : inSpikeBlock c i M) :
    Checks.spikePhiCoefficientsValid c i t ∧
      Checks.spikePhi c i t M ≤ (c.bounds.getD i 0 : ℝ) := by
  cases hf : blockFor blocks c i with
  | none => simp [checkedBlockOK, hf] at h
  | some b =>
      have hp : blockOK c i b = true := by simpa [checkedBlockOK, hf] using h
      exact blockOK_sound hp ht hM

theorem nonwindowAllOK_log_sound {blocks : List RayBlock}
    (h : nonwindowAllOK blocks = true) :
    ∀ c ∈ spikeCells, c.window = false → ∀ i : Nat, i < 5 → ∀ t M : ℝ,
      Checks.inCell c.lo c.hi t → inSpikeBlock c i M →
      Checks.spikePhiCoefficientsValid c i t ∧
        Checks.spikePhi c i t M ≤ (c.logBounds.getD i 0 : ℝ) := by
  intro c hc hw i hi t M ht hM
  have hp := (List.all_eq_true.mp h) c hc
  simp only [hw, Bool.false_eq_true, if_false] at hp
  exact checkedBlockOK_log_sound
    ((List.all_eq_true.mp hp) i (List.mem_range.mpr hi)) ht hM

/-- The complete nonwindow checker proves exact statement 7.14(a). -/
theorem nonwindowAllOK_sound {blocks : List RayBlock}
    (h : nonwindowAllOK blocks = true) : Checks.lemma_7_14_nonwindow := by
  intro c hc hw i hi t M ht hM
  have hp := (List.all_eq_true.mp h) c hc
  simp only [hw, Bool.false_eq_true, if_false] at hp
  exact checkedBlockOK_sound
    ((List.all_eq_true.mp hp) i (List.mem_range.mpr hi)) ht hM

theorem suppliedNonwindowOK_sound {select : V22SpikeCell → Nat → RayBlock}
    (h : suppliedNonwindowOK select = true) : Checks.lemma_7_14_nonwindow := by
  intro c hc hw i hi t M ht hM
  have hp := (List.all_eq_true.mp h) c hc
  simp only [hw, Bool.false_eq_true, if_false] at hp
  exact blockOK_sound ((List.all_eq_true.mp hp) i (List.mem_range.mpr hi)) ht hM

/-- Available pure-ray bounds on marked cells cover the required minimum.
This is uniform in the second term, so every class/fiber hypothesis remains
available to the window consumer. -/
theorem checkedBlockOK_min_log_sound {blocks : List RayBlock} {c : V22SpikeCell} {i : Nat}
    (h : checkedBlockOK blocks c i = true) {t M X : ℝ}
    (ht : Checks.inCell c.lo c.hi t) (hM : inSpikeBlock c i M) :
    Checks.spikePhiCoefficientsValid c i t ∧
      min (Checks.spikePhi c i t M) X ≤ (c.logBounds.getD i 0 : ℝ) := by
  have hs := checkedBlockOK_log_sound h ht hM
  exact ⟨hs.1, (min_le_left _ _).trans hs.2⟩

theorem checkedBlockOK_min_sound {blocks : List RayBlock} {c : V22SpikeCell} {i : Nat}
    (h : checkedBlockOK blocks c i = true) {t M X : ℝ}
    (ht : Checks.inCell c.lo c.hi t) (hM : inSpikeBlock c i M) :
    Checks.spikePhiCoefficientsValid c i t ∧
      min (Checks.spikePhi c i t M) X ≤ (c.bounds.getD i 0 : ℝ) := by
  have hs := checkedBlockOK_sound h ht hM
  exact ⟨hs.1, (min_le_left _ _).trans hs.2⟩

theorem generatedNonwindowOK_sound (h : generatedNonwindowOK = true) :
    Checks.lemma_7_14_nonwindow := nonwindowAllOK_sound h

end Erdos993Lean.Analytic.V22.Compute.RayChecks
