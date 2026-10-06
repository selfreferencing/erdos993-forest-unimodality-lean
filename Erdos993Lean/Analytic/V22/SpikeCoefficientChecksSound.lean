import Erdos993Lean.Analytic.V22.Compute.SpikeCoefficientChecks
import Erdos993Lean.Analytic.V22.RayChecksSound

/-! The missing marked-block coefficient consumer. No fiber transport or
betaE monotonicity is inferred from these positive denominator checks. -/

namespace Erdos993Lean.Analytic.V22.Compute.SpikeCoefficientChecks

open GeneratedRayData

noncomputable section

theorem pieceOK_sound {c : V22SpikeCell} {i : Nat} {p : CoefficientPiece}
    (h : pieceOK c i p = true) {t : ℝ}
    (ht : (p.tSpan.1 : ℝ) ≤ t ∧ t ≤ (p.tSpan.2 : ℝ)) :
    Checks.spikePhiCoefficientsValid c i t := by
  have henv := spanEnv_mem ht
  by_cases hi : i = 4
  · have hg : RayExprs.infiniteGuard p.brackets (spanEnv p.tSpan) (.var 0)
        (m1 c i) (rm c) = true := by simpa only [pieceOK, if_pos hi] using h
    have hs := RayExprs.infiniteGuard_sound (realSpanEnv t) p.brackets (.var 0)
      (m1 c i) (rm c) henv hg
    simpa [Checks.spikePhiCoefficientsValid, hi, Expr.evalR, realSpanEnv,
      RayChecks.m1_cast, RayChecks.rm_cast] using hs
  · have hg : (RayExprs.rhoStarBlock (RayExprs.blockN (m1 c i))
        (RayExprs.phiBlockNuMax (2 * m1 c i) (rm c)) (.rat (rm c))).positiveOK
        (spanEnv p.tSpan) = true := by
      simpa only [pieceOK, if_neg hi] using h
    have hs := Expr.positiveOK_sound _ henv hg
    simpa [Checks.spikePhiCoefficientsValid, hi, phiBlockCoefficientsValid,
      Expr.evalR, RayChecks.m1_cast, RayChecks.rm_cast] using hs

theorem blockOK_sound {c : V22SpikeCell} {i : Nat} {b : CoefficientBlock}
    (h : blockOK c i b = true) {t : ℝ} (ht : Checks.inCell c.lo c.hi t) :
    Checks.spikePhiCoefficientsValid c i t := by
  simp only [blockOK, Bool.and_eq_true] at h
  obtain ⟨s, hs, ht'⟩ := partitionFrom_covers h.1.2 ht
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
  exact pieceOK_sound ((List.all_eq_true.mp h.2) p hp) ht'

theorem checkedBlockOK_sound {blocks : List CoefficientBlock} {c : V22SpikeCell} {i : Nat}
    (h : checkedBlockOK blocks c i = true) {t : ℝ} (ht : Checks.inCell c.lo c.hi t) :
    Checks.spikePhiCoefficientsValid c i t := by
  cases hf : blockFor blocks c i with
  | none => simp [checkedBlockOK, hf] at h
  | some b =>
      have hp : blockOK c i b = true := by simpa [checkedBlockOK, hf] using h
      exact blockOK_sound hp ht

theorem allOK_sound {blocks : List CoefficientBlock} (h : allOK blocks = true) :
    ∀ c ∈ spikeCells, ∀ i : Nat, i < 5 → ∀ t : ℝ, Checks.inCell c.lo c.hi t →
      Checks.spikePhiCoefficientsValid c i t := by
  intro c hc i hi t ht
  have hp := (List.all_eq_true.mp h) c hc
  exact checkedBlockOK_sound ((List.all_eq_true.mp hp) i (List.mem_range.mpr hi)) ht

end
end Erdos993Lean.Analytic.V22.Compute.SpikeCoefficientChecks
