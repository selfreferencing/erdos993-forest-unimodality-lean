import Erdos993Lean.Analytic.V22.Compute.WingChecks
import Erdos993Lean.Analytic.V22.WingExprsSound
import Erdos993Lean.Analytic.V22.GridSound

/-! A passing C1 candidate proves all four source conditions and the full
all-real-size conclusion, uniformly on all eleven exact original cells. -/

namespace Erdos993Lean.Analytic.V22.Compute.WingChecks

def sourceAt (c : V22WingClass) (cell : V22Cell) (t : ℝ) : Prop :=
  0 < Checks.wingC c cell t (Checks.wingN0 c cell) ∧
  Checks.wingBPrime c cell t / (2 * Checks.wingC c cell t (Checks.wingN0 c cell)) ≤
    (c.ra : ℝ) * Real.sqrt (Checks.wingN0 c cell) ∧
  0 < rhoStar (Checks.wingN0 c cell) c.rb ∧
  0 < betaE (Checks.wingN0 c cell) c.rb (Checks.wingNuMax c cell)

def minimumAt (c : V22WingClass) (cell : V22Cell) (t : ℝ) : Prop :=
  (0 ≤ WingQuadratic.startingSlope (WingQuadratic.wingA c) (WingQuadratic.wingB c cell t)
      (WingQuadratic.wingSlope c cell t) (Checks.wingN0 c cell) ∧
    0 ≤ WingQuadratic.quadratic (WingQuadratic.wingA c) (WingQuadratic.wingB c cell t)
      (WingQuadratic.wingSlope c cell t) (WingQuadratic.wingD c cell t) (Checks.wingN0 c cell)) ∨
  ∃ N1 : ℝ, 0 < N1 ∧ 0 ≤ WingQuadratic.tangentBound
    (WingQuadratic.wingA c) (WingQuadratic.wingB c cell t)
    (WingQuadratic.wingSlope c cell t) (WingQuadratic.wingD c cell t) N1

theorem sourceOK_sound {c : V22WingClass} {cell : V22Cell} {p : PieceCandidate}
    (h : sourceOK c cell p = true) {t : ℝ}
    (ht : (p.span.1 : ℝ) ≤ t ∧ t ≤ (p.span.2 : ℝ)) : sourceAt c cell t := by
  simp only [sourceOK, Bool.and_eq_true] at h
  have hm := spanEnv_mem ht
  have hc0 : 0 < Checks.wingC c cell t (Checks.wingN0 c cell) := by
    simpa [WingExprs.sourceConditions, Expr.evalR, realSpanEnv, WingExprs.N0_cast] using
      Expr.positiveOK_sound _ hm h.1.1.1
  have hnu : 0 ≤ (c.ra : ℝ) * Real.sqrt (Checks.wingN0 c cell) -
      Checks.wingBPrime c cell t / (2 * Checks.wingC c cell t (Checks.wingN0 c cell)) := by
    simpa [WingExprs.sourceConditions, Expr.evalR, realSpanEnv, WingExprs.N0_cast] using
      Expr.nonnegativeOK_sound _ hm h.1.1.2
  have hrs : 0 < rhoStar (Checks.wingN0 c cell) c.rb := by
    simpa [WingExprs.sourceConditions, Expr.evalR, realSpanEnv, WingExprs.N0_cast] using
      Expr.positiveOK_sound _ hm h.1.2
  have hbe : 0 < betaE (Checks.wingN0 c cell) c.rb (Checks.wingNuMax c cell) := by
    simpa [WingExprs.sourceConditions, Expr.evalR, realSpanEnv, WingExprs.N0_cast] using
      Expr.positiveOK_sound _ hm h.2
  exact ⟨hc0, by linarith, hrs, hbe⟩

theorem algebraOK_sound {c : V22WingClass} {cell : V22Cell} {p : PieceCandidate}
    (h : algebraOK c cell p = true) {t : ℝ}
    (ht : (p.span.1 : ℝ) ≤ t ∧ t ≤ (p.span.2 : ℝ)) :
    0 < WingQuadratic.wingA c ∧ 0 ≤ WingQuadratic.wingSlope c cell t ∧
      0 < Checks.wingN0 c cell := by
  simp only [algebraOK, Bool.and_eq_true] at h
  have hm := spanEnv_mem ht
  refine ⟨?_, ?_, ?_⟩
  · simpa [Expr.evalR, realSpanEnv] using Expr.positiveOK_sound _ hm h.1.1
  · simpa [Expr.evalR, realSpanEnv] using Expr.nonnegativeOK_sound _ hm h.1.2
  · simpa [Expr.evalR, WingExprs.N0_cast] using Expr.positiveOK_sound _ hm h.2

theorem minimumOK_sound {c : V22WingClass} {cell : V22Cell} {p : PieceCandidate}
    (h : minimumOK c cell p = true) {t : ℝ}
    (ht : (p.span.1 : ℝ) ≤ t ∧ t ≤ (p.span.2 : ℝ)) : minimumAt c cell t := by
  have hm := spanEnv_mem ht
  cases hchoice : p.tangent with
  | none =>
      simp only [minimumOK, hchoice, Bool.and_eq_true] at h
      apply Or.inl
      constructor
      · simpa [Expr.evalR, realSpanEnv] using Expr.nonnegativeOK_sound _ hm h.1
      · simpa [Expr.evalR, realSpanEnv] using Expr.nonnegativeOK_sound _ hm h.2
  | some N1 =>
      simp only [minimumOK, hchoice, Bool.and_eq_true] at h
      apply Or.inr
      refine ⟨(N1 : ℝ), ?_, ?_⟩
      · simpa [Expr.evalR] using Expr.positiveOK_sound _ hm h.1.2
      · simpa [Expr.evalR, realSpanEnv] using Expr.nonnegativeOK_sound _ hm h.2

theorem pieceOK_sound {c : V22WingClass} {cell : V22Cell} {p : PieceCandidate}
    (h : pieceOK c cell p = true) {t : ℝ}
    (ht : (p.span.1 : ℝ) ≤ t ∧ t ≤ (p.span.2 : ℝ)) :
    sourceAt c cell t ∧ ∀ N : ℝ, Checks.wingN0 c cell ≤ N → 0 ≤ Checks.wingW c cell t N := by
  simp only [pieceOK, Bool.and_eq_true] at h
  have hs := sourceOK_sound h.1.1 ht
  have ha := algebraOK_sound h.1.2 ht
  have hc := minimumOK_sound h.2 ht
  have hp := WingQuadratic.wing_conditions_and_allN c cell t hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
    ha.1 ha.2.1 ha.2.2 hc
  exact ⟨hs, hp.2.2.2.2⟩

theorem cellOK_sound {c : V22WingClass} {cell : V22Cell} {pieces : List PieceCandidate}
    (h : cellOK c cell pieces = true) {t : ℝ}
    (ht : (cell.lo : ℝ) ≤ t ∧ t ≤ (cell.hi : ℝ)) :
    sourceAt c cell t ∧ ∀ N : ℝ, Checks.wingN0 c cell ≤ N → 0 ≤ Checks.wingW c cell t N := by
  simp only [cellOK, Bool.and_eq_true] at h
  obtain ⟨s, hs, hts⟩ := partitionFrom_covers h.1 ht
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
  exact pieceOK_sound ((List.all_eq_true.mp h.2) p hp) hts

theorem checkedCell_sound {certificates : List CellCertificate} {c : V22WingClass} {cell : V22Cell}
    (h : checkedCell certificates c cell = true) {t : ℝ}
    (ht : (cell.lo : ℝ) ≤ t ∧ t ≤ (cell.hi : ℝ)) :
    sourceAt c cell t ∧ ∀ N : ℝ, Checks.wingN0 c cell ≤ N → 0 ≤ Checks.wingW c cell t N := by
  cases hf : certificateFor certificates cell with
  | none => simp [checkedCell, hf] at h
  | some cert =>
      have hp : cellOK c cell cert.pieces = true := by simpa [checkedCell, hf] using h
      exact cellOK_sound hp ht

/-- Every exact wing class, original cell, actual `t`, and real `N` is retained. -/
theorem allOK_sound {certificates : List CellCertificate}
    (h : allOK certificates = true) : Checks.lemma_7_15 := by
  intro c hc cell hcell hid t hta htb
  have hp := (List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2) c hc
  have hcp := (List.all_eq_true.mp hp) cell hcell
  have hchecked : checkedCell certificates c cell = true := by
    simpa only [classCellOK, if_pos hid] using hcp
  obtain ⟨hs, hn⟩ := checkedCell_sound hchecked ⟨hta, htb⟩
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, hn⟩

theorem originalCellCount_eq : originalCellCount = 11 := by decide

end Erdos993Lean.Analytic.V22.Compute.WingChecks
