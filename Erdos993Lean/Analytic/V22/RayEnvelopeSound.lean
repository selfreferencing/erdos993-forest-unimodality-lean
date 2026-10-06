import Erdos993Lean.Analytic.V22.Compute.RayEnvelope
import Erdos993Lean.Analytic.V22.RayExprsSound

/-! Upper transport for conservative quadratic transition envelopes. -/
namespace Erdos993Lean.Analytic.V22.Compute.RayEnvelope
open RayExprs
noncomputable section

theorem quadraticSup_le_envelope (a b nm : ℝ) :
    V22.quadraticSupBound a b nm ≤ a*nm + V22.positivePart (-b)*nm^2 := by
  unfold V22.quadraticSupBound
  split_ifs with hb
  · exact (min_le_right _ _).trans (le_add_of_nonneg_right
      (mul_nonneg (le_max_right _ _) (sq_nonneg _)))
  · have hp : V22.positivePart (-b) = -b := max_eq_left (by linarith)
    rw [hp]
    exact le_of_eq (by ring)

theorem selected_upper (envR : Nat → ℝ) (universal isPositive : Bool) (a b nm : Expr)
    {env : Nat → TailCert.Compute.Ival} (henv : ∀ i, (env i).Mem (envR i))
    (hg : selectedGuard universal isPositive env b = true) :
    V22.quadraticSupBound (a.evalR envR) (b.evalR envR) (nm.evalR envR) ≤
      (selected universal isPositive a b nm).evalR envR := by
  cases universal with
  | true =>
    simpa [selected,quadraticEnvelope,Expr.evalR,V22.positivePart] using
      quadraticSup_le_envelope (a.evalR envR) (b.evalR envR) (nm.evalR envR)
  | false =>
    have he := evalR_quadraticSup envR isPositive a b nm henv hg
    simpa only [selected, Bool.false_eq_true, if_false] using he.ge

theorem phiWithRemainder_monotone {t M D D' : ℝ}
    (ht : 0 ≤ t) (hM : 0 < M) (hD : D ≤ D') :
    V22.phiWithRemainder t M D ≤ V22.phiWithRemainder t M D' := by
  unfold V22.phiWithRemainder V22.positivePart
  apply add_le_add (le_refl _)
  apply mul_le_mul_of_nonneg_left _ (div_nonneg ht hM.le)
  apply max_le_max _ (le_refl _)
  linarith

theorem remainder_upper (envR : Nat → ℝ) (br : RootBrackets) (m : EnvelopeMethods)
    (t : Expr) (M1 M2 rm : Rat) {env : Nat → TailCert.Compute.Ival}
    (henv : ∀ i, (env i).Mem (envR i))
    (hg : guard br m env t M1 M2 rm = true) :
    V22.phiBlockRemainder (t.evalR envR) (M1 : ℝ) (M2 : ℝ) (rm : ℝ) ≤
      (remainder br m t M1 M2 rm).evalR envR := by
  simp only [guard, Bool.and_eq_true] at hg
  have hq := hg.1.1.1
  have hfirst := selected_upper envR m.firstUniversal m.base.quadratic.firstPositive
    (blockFirstA (RayExprs.phiBlockGhat br t M1 M2) (blockN M1) (RayExprs.phiBlockNuMax M2 rm) (.rat rm))
    (blockFirstB (RayExprs.phiBlockGhat br t M1 M2) (blockN M1) (RayExprs.phiBlockNuMax M2 rm) (.rat rm))
    (RayExprs.phiBlockNuMax M2 rm) henv hg.1.2
  have hsecond := selected_upper envR m.secondUniversal m.base.quadratic.secondPositive
    (blockSecondA (blockN M1) (RayExprs.phiBlockNuMax M2 rm) (.rat rm))
    (blockSecondB (blockN M1) (RayExprs.phiBlockNuMax M2 rm) (.rat rm))
    (RayExprs.phiBlockNuMax M2 rm) henv hg.2
  have hg1 := evalR_phiBlockG1Bound envR br m.base t M1 M2 rm henv hq
  have hnonneg : 0 ≤ V22.phiBlockG1Bound (t.evalR envR) M1 M2 rm := by
    unfold V22.phiBlockG1Bound V22.positivePart
    dsimp only
    split_ifs <;> exact le_max_right _ _
  have hp1 := max_le_max hfirst (le_refl (0 : ℝ))
  have hp2 := mul_le_mul_of_nonneg_left (max_le_max hsecond (le_refl (0 : ℝ))) hnonneg
  have hh := add_le_add hp1 hp2
  simpa [remainder,Expr.evalR,hg1,blockFirstA,blockFirstB,blockSecondA,blockSecondB,
    V22.phiBlockRemainder,V22.dUbarBlock,V22.positivePart] using hh

theorem finitePass_sound (envR : Nat → ℝ) (br : RootBrackets) (m : EnvelopeMethods)
    (t M : Expr) (M1 M2 rm bound : Rat) {env : Nat → TailCert.Compute.Ival}
    (henv : ∀ i, (env i).Mem (envR i)) (ht : 0 ≤ t.evalR envR) (hM : 0 < M.evalR envR)
    (hp : finitePass br m env t M M1 M2 rm bound = true) :
    V22.phiBlockCoefficientsValid M1 M2 rm ∧
      V22.phiBlock (t.evalR envR) (M.evalR envR) M1 M2 rm ≤ (bound : ℝ) := by
  simp only [finitePass,Bool.and_eq_true] at hp
  have hg := hp.1
  simp only [guard,Bool.and_eq_true] at hg
  have hrs := (RayExprs.rhoStarBlock (blockN M1) (RayExprs.phiBlockNuMax M2 rm) (.rat rm)).positiveOK_sound
    henv hg.1.1.2
  have hr := remainder_upper envR br m t M1 M2 rm henv hp.1
  have hb := (phiUpper br m t M M1 M2 rm).upperOK_sound bound henv hp.2
  have hu := phiWithRemainder_monotone ht hM hr
  rw [phiUpper,evalR_phiWithRemainder] at hb
  exact ⟨by simpa [Expr.evalR,V22.phiBlockCoefficientsValid] using hrs,
    hu.trans hb⟩

end
end Erdos993Lean.Analytic.V22.Compute.RayEnvelope
