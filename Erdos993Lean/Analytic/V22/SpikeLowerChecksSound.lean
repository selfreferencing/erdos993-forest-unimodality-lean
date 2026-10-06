import Erdos993Lean.Analytic.V22.Compute.SpikeLowerChecks
import Erdos993Lean.Analytic.V22.CoefficientExprsSound
import Erdos993Lean.Analytic.V22.SpikeLowerMonotone

/-!
# B2 endpoint-check soundness and the whole-cell consumer

Checker success supplies the original finite endpoint facts. The analytic
monotonicity proofs supply the all-real-size clauses of Lemma 7.13 and
transport each endpoint across its entire original closed `t` cell.
No numerical pass, root bracket or rounded diagnostic margin is asserted.
-/

namespace Erdos993Lean.Analytic.V22.Compute.SpikeLowerChecks

open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute

noncomputable def realEnv : Nat → ℝ := fun _ => 0

theorem closedEnv_mem : ∀ i, (closedEnv i).Mem (realEnv i) := by
  intro i
  simpa [closedEnv, realEnv] using mem_ofRat (0 : Rat)

theorem positive_sound {e : Expr} (h : positive e = true) :
    0 < e.evalR realEnv := e.positiveOK_sound closedEnv_mem h

theorem nonnegative_sound {e : Expr} (h : nonnegative e = true) :
    0 ≤ e.evalR realEnv := e.nonnegativeOK_sound closedEnv_mem h

theorem upper_sound {e : Expr} {q : Rat} (h : upper e q = true) :
    e.evalR realEnv ≤ (q : ℝ) := e.upperOK_sound q closedEnv_mem h

@[simp] theorem evalR_slack (env : Nat → ℝ) (rm t N : Expr) :
    (slack rm t N).evalR env =
      Checks.spikeLowerSlack (rm.evalR env) (t.evalR env) (N.evalR env) := by
  norm_num [slack, Expr.evalR, Checks.spikeLowerSlack]

@[simp] theorem start_cast (c : Candidate) :
    (start c : ℝ) = max 10 ((c.mean : ℝ) * (c.ta : ℝ) + 2) := by
  simp [start]

@[simp] theorem evalR_endpoint (env : Nat → ℝ) (c : Candidate) :
    (endpoint c).evalR env = Checks.spikeLowerSlack c.rm c.tb (start c : ℝ) := by
  simp [endpoint, Expr.evalR]

theorem domainOK_sound {c : Candidate} (h : domainOK c = true) :
    0 ≤ (c.rm : ℝ) ∧ (c.rm : ℝ) ≤ 1/2 ∧ 0 ≤ (c.ta : ℝ) ∧
      (c.ta : ℝ) ≤ (c.tb : ℝ) ∧ (c.tb : ℝ) ≤ 1 ∧ 10 ≤ (start c : ℝ) := by
  simp only [domainOK, Bool.and_eq_true] at h
  have hr := nonnegative_sound h.1.1.1.1.1
  have hrhi := upper_sound h.1.1.1.1.2
  have hta := nonnegative_sound h.1.1.1.2
  have hspan := nonnegative_sound h.1.1.2
  have htb := upper_sound h.1.2
  have hn := nonnegative_sound h.2
  simp only [Expr.evalR] at hr hrhi hta hspan htb hn
  norm_num at hrhi htb hn
  exact ⟨hr, hrhi, hta, by linarith, htb, by simp [start_cast]⟩

theorem candidateOK_endpoint {c : Candidate} (h : candidateOK c = true) :
    0 < Checks.spikeLowerSlack c.rm c.tb (start c : ℝ) := by
  have hp := (Bool.and_eq_true_iff.mp h).2
  simpa only [evalR_endpoint] using positive_sound hp

theorem rmRat_cast (cell : V22SpikeCell) : (rmRat cell : ℝ) = spikeRm cell := by
  cases hfind : classes.find? (fun c => c.classId == cell.classId) with
  | none => norm_num [rmRat, spikeRm, spikeClass, hfind]
  | some c => simp [rmRat, spikeRm, spikeClass, hfind]

theorem meanRat_cast (cell : V22SpikeCell) : (meanRat cell : ℝ) = spikeMean cell := by
  cases hfind : classes.find? (fun c => c.classId == cell.classId) with
  | none => norm_num [meanRat, spikeMean, spikeClass, hfind]
  | some c => simp [meanRat, spikeMean, spikeClass, hfind]

theorem outerOK_sound {cell : V22SpikeCell} (h : outerOK cell = true)
    (houter : cell.classId ≠ 0) :
    0 < Checks.spikeLowerSlack (spikeRm cell) cell.hi
      (max 10 (spikeMean cell * (cell.lo : ℝ) + 2)) := by
  have hc : candidateOK (ofCell cell) = true := by
    simpa only [outerOK, if_neg houter] using h
  simpa only [ofCell, start_cast, rmRat_cast, meanRat_cast] using candidateOK_endpoint hc

theorem b2OK_sound (h : b2OK = true) : Checks.lemma_7_13 := by
  have hc := (Bool.and_eq_true_iff.mp h).1
  have ho := (Bool.and_eq_true_iff.mp h).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hend := candidateOK_endpoint hc
    norm_num [central, start] at hend
    exact hend
  · intro cell hcell houter
    exact outerOK_sound ((List.all_eq_true.mp ho) cell hcell) houter
  · intro rm hr N hN
    exact spikeLowerSlack_subtracted_monotone_t hr.1 hr.2 hN
  · intro rm hr t ht
    exact spikeLowerSlack_subtracted_antitone_N hr.1 hr.2 ht

theorem certificateOK_implies_b2OK {candidates : List Candidate}
    (h : certificateOK candidates = true) : b2OK = true := by
  simp only [certificateOK, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨rfl, h⟩
  have hall := List.all_eq_true.mp h
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hall central (by simp [requiredCandidates]), ?_⟩
  apply List.all_eq_true.mpr
  intro cell hcell
  by_cases houter : cell.classId = 0
  · simp [outerOK, houter]
  · have hmem : ofCell cell ∈ requiredCandidates := by
      simp only [requiredCandidates, List.mem_cons, List.mem_map, List.mem_filter,
        decide_eq_true_eq]
      exact Or.inr ⟨cell, ⟨hcell, houter⟩, rfl⟩
    simpa only [outerOK, if_neg houter] using hall (ofCell cell) hmem

theorem certificateOK_sound {candidates : List Candidate}
    (h : certificateOK candidates = true) : Checks.lemma_7_13 :=
  b2OK_sound (certificateOK_implies_b2OK h)

/-- The source's frozen endpoint controls its whole original closed cell.
The upper `t` bound is essential: the quadratic is decreasing only up to 1. -/
theorem spikeLowerSlack_endpoint_lower {rm ta tb N0 t N : ℝ}
    (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) (hta : 0 ≤ ta)
    (htt : ta ≤ t) (htb : t ≤ tb) (htbhi : tb ≤ 1)
    (hN0 : 10 ≤ N0) (hN : N0 ≤ N) :
    Checks.spikeLowerSlack rm tb N0 ≤ Checks.spikeLowerSlack rm t N := by
  have ht : 0 ≤ t := hta.trans htt
  have htb0 : 0 ≤ tb := ht.trans htb
  have hN10 : 10 ≤ N := hN0.trans hN
  have hgapt := spikeLowerSlack_subtracted_monotone_t hrm hrmhi hN10
    (show t ∈ Set.Ici 0 from ht) (show tb ∈ Set.Ici 0 from htb0) htb
  have hgapN := spikeLowerSlack_subtracted_antitone_N hrm hrmhi htb0
    (show N0 ∈ Set.Ici 10 from hN0) (show N ∈ Set.Ici 10 from hN10) hN
  have hprod := mul_nonneg (sub_nonneg.mpr htb)
    (show 0 ≤ 2-t-tb by linarith)
  nlinarith

theorem candidateOK_whole_cell {c : Candidate} (h : candidateOK c = true)
    {t N : ℝ} (ht : (c.ta : ℝ) ≤ t ∧ t ≤ (c.tb : ℝ))
    (hN : (start c : ℝ) ≤ N) : 0 < Checks.spikeLowerSlack c.rm t N := by
  obtain ⟨hrm, hrmhi, hta, _, htbhi, hN0⟩ := domainOK_sound (Bool.and_eq_true_iff.mp h).1
  exact lt_of_lt_of_le (candidateOK_endpoint h)
    (spikeLowerSlack_endpoint_lower hrm hrmhi hta ht.1 ht.2 htbhi hN0 hN)

theorem b2OK_outer_whole_cell (h : b2OK = true) {cell : V22SpikeCell}
    (hcell : cell ∈ spikeCells) (houter : cell.classId ≠ 0) {t N : ℝ}
    (ht : (cell.lo : ℝ) ≤ t ∧ t ≤ (cell.hi : ℝ))
    (hN : max 10 (spikeMean cell * (cell.lo : ℝ) + 2) ≤ N) :
    0 < Checks.spikeLowerSlack (spikeRm cell) t N := by
  have ho := (List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2) cell hcell
  have hc : candidateOK (ofCell cell) = true := by
    simpa only [outerOK, if_neg houter] using ho
  have ht' : ((ofCell cell).ta : ℝ) ≤ t ∧ t ≤ ((ofCell cell).tb : ℝ) := ht
  have hn' : (start (ofCell cell) : ℝ) ≤ N := by
    simpa only [start_cast, ofCell, meanRat_cast] using hN
  simpa only [ofCell, rmRat_cast] using candidateOK_whole_cell hc ht' hn'

theorem b2OK_central_whole_cell (h : b2OK = true) {t N : ℝ}
    (ht : 0 ≤ t ∧ t ≤ 3/5) (hN : 10 ≤ N) :
    0 < Checks.spikeLowerSlack (1/4) t N := by
  have hc := (Bool.and_eq_true_iff.mp h).1
  have ht' : (central.ta : ℝ) ≤ t ∧ t ≤ (central.tb : ℝ) := by
    simpa [central] using ht
  have hn' : (start central : ℝ) ≤ N := by
    norm_num [central, start]
    exact hN
  simpa [central] using candidateOK_whole_cell hc ht' hn'

end Erdos993Lean.Analytic.V22.Compute.SpikeLowerChecks
