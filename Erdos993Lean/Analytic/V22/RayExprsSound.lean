import Erdos993Lean.Analytic.V22.Compute.RayExprs
import Erdos993Lean.Analytic.V22.CoefficientExprsSound

/-!
# Exact meanings of the retained block ray recipes

The sign guards justify each selected source branch. Root brackets and
division safety are consumed by the generic interval evaluator. The final
theorems certify only the exact `phiBlock` / `phiInfiniteBlock` formula and
its retained coefficient conditions. They do not provide the separate
analytic transport from a fiber/window deficit to that formula.
-/

namespace Erdos993Lean.Analytic.V22.Compute.RayExprs

open Erdos993Lean.Analytic.TailCert
open Erdos993Lean.Analytic.TailCert.Compute

noncomputable section
attribute [local instance] Classical.propDecidable

variable (realEnv : Nat → ℝ)

@[simp] theorem evalR_rootAt (b : RootBracket) (l : Expr) :
    (rootAt b l).evalR realEnv = V22.rootMap (l.evalR realEnv) := rfl

@[simp] theorem evalR_G (b : RootBracket) (l : Expr) :
    (G b l).evalR realEnv = V22.G (l.evalR realEnv) := by
  simp [G, Expr.evalR, V22.G]

@[simp] theorem evalR_G1 (b : RootBracket) (l : Expr) :
    (G1 b l).evalR realEnv = V22.G1 (l.evalR realEnv) := by
  simp [G1, Expr.evalR, V22.G1]

@[simp] theorem evalR_G2 (b : RootBracket) (l : Expr) :
    (G2 b l).evalR realEnv = V22.G2 (l.evalR realEnv) := by
  simp [G2, Expr.evalR, V22.G2]

@[simp] theorem evalR_positivePart (x : Expr) :
    (positivePart x).evalR realEnv = V22.positivePart (x.evalR realEnv) := by
  simp [positivePart, Expr.evalR, V22.positivePart]

@[simp] theorem evalR_absolute (x : Expr) :
    (absolute x).evalR realEnv = |x.evalR realEnv| := by
  simp [absolute, Expr.evalR, abs_eq_max_neg]

@[simp] theorem evalR_lambdaT (t : Expr) :
    (lambdaT t).evalR realEnv = V22.lambdaT (t.evalR realEnv) := by
  norm_num [lambdaT, Expr.evalR, V22.lambdaT]

@[simp] theorem evalR_kbar (M : Expr) :
    (kbar M).evalR realEnv = V22.kbar (M.evalR realEnv) := by
  norm_num [kbar, Expr.evalR, V22.kbar]

@[simp] theorem evalR_hbar (M : Expr) :
    (hbar M).evalR realEnv = V22.hbar (M.evalR realEnv) := by
  simp [hbar, Expr.evalR, V22.hbar]

@[simp] theorem evalR_gaussianSlack (b : RootBracket) (t : Expr) :
    (gaussianSlack b t).evalR realEnv = V22.gaussianSlack (t.evalR realEnv) := by
  norm_num [gaussianSlack, Expr.evalR, V22.gaussianSlack]

@[simp] theorem evalR_rhoStarBlock (N nm rm : Expr) :
    (rhoStarBlock N nm rm).evalR realEnv =
      V22.rhoStarBlock (N.evalR realEnv) (nm.evalR realEnv) (rm.evalR realEnv) := by
  simp [rhoStarBlock, Expr.evalR, V22.rhoStarBlock]

@[simp] theorem evalR_kappaABlock (N nm rm : Expr) :
    (kappaABlock N nm rm).evalR realEnv =
      V22.kappaABlock (N.evalR realEnv) (nm.evalR realEnv) (rm.evalR realEnv) := by
  simp [kappaABlock, Expr.evalR, V22.kappaABlock]

theorem evalR_quadraticSup (isPositive : Bool) (a b nm : Expr)
    {env : Nat → Ival} (henv : ∀ i, (env i).Mem (realEnv i))
    (hguard : signGuard isPositive env b = true) :
    (quadraticSup isPositive a b nm).evalR realEnv =
      V22.quadraticSupBound (a.evalR realEnv) (b.evalR realEnv) (nm.evalR realEnv) := by
  cases isPositive with
  | false =>
    have hg : b.upperOK env 0 = true := by simpa [signGuard] using hguard
    have hb : b.evalR realEnv ≤ 0 := by simpa using b.upperOK_sound 0 henv hg
    simp [quadraticSup, Expr.evalR, V22.quadraticSupBound, not_lt_of_ge hb]
  | true =>
    have hg : b.positiveOK env = true := by simpa [signGuard] using hguard
    have hb : 0 < b.evalR realEnv := b.positiveOK_sound henv hg
    simp [quadraticSup, Expr.evalR, V22.quadraticSupBound, hb]

theorem evalR_dUbarBlock (m : QuadraticMethods) (Gh g1 N nm rm : Expr)
    {env : Nat → Ival} (henv : ∀ i, (env i).Mem (realEnv i))
    (hguard : boundedSignGuard m env Gh N nm rm = true) :
    (dUbarBlock m Gh g1 N nm rm).evalR realEnv =
      V22.dUbarBlock (Gh.evalR realEnv) (g1.evalR realEnv)
        (N.evalR realEnv) (nm.evalR realEnv) (rm.evalR realEnv) := by
  simp only [boundedSignGuard, Bool.and_eq_true] at hguard
  simp only [dUbarBlock, Expr.evalR, evalR_positivePart]
  rw [evalR_quadraticSup realEnv m.firstPositive _ _ _ henv hguard.1,
    evalR_quadraticSup realEnv m.secondPositive _ _ _ henv hguard.2]
  simp [blockFirstA, blockFirstB, blockSecondA, blockSecondB, Expr.evalR,
    V22.dUbarBlock, V22.positivePart]

@[simp] theorem evalR_phiWithRemainder (b : RootBracket) (t M D : Expr) :
    (phiWithRemainder b t M D).evalR realEnv =
      V22.phiWithRemainder (t.evalR realEnv) (M.evalR realEnv) (D.evalR realEnv) := by
  norm_num [phiWithRemainder, Expr.evalR, V22.phiWithRemainder]

@[simp] theorem evalR_blockN (M1 : Rat) :
    (blockN M1).evalR realEnv = (M1 : ℝ) + 2 := by
  simp [blockN, Expr.evalR]

@[simp] theorem evalR_phiBlockNuMax (M2 rm : Rat) :
    (phiBlockNuMax M2 rm).evalR realEnv = V22.phiBlockNuMax (M2 : ℝ) (rm : ℝ) := by
  simp [phiBlockNuMax, Expr.evalR, V22.phiBlockNuMax]

@[simp] theorem evalR_phiBlockQ2 (M1 M2 rm : Rat) :
    (phiBlockQ2 M1 M2 rm).evalR realEnv =
      V22.phiBlockQ2 (M1 : ℝ) (M2 : ℝ) (rm : ℝ) := by
  simp [phiBlockQ2, Expr.evalR, V22.phiBlockQ2]

@[simp] theorem evalR_shiftLowArg (t : Expr) (M2 : Rat) :
    (shiftLowArg t M2).evalR realEnv =
      V22.lambdaT (t.evalR realEnv) + (71 / 20) / ((M2 : ℝ) + 3) := by
  norm_num [shiftLowArg, Expr.evalR]

@[simp] theorem evalR_shiftHighArg (t : Expr) (M1 : Rat) :
    (shiftHighArg t M1).evalR realEnv = V22.lambdaT (t.evalR realEnv) + V22.hbar (M1 : ℝ) := by
  simp [shiftHighArg, Expr.evalR]

@[simp] theorem evalR_g1ShiftArg (t : Expr) (M1 M2 rm : Rat) :
    (g1ShiftArg t M1 M2 rm).evalR realEnv =
      V22.lambdaT (t.evalR realEnv) + (71 / 20) / ((M2 : ℝ) + 3) -
        1 / (((M1 : ℝ) + 2) ^ 2 * V22.phiBlockQ2 (M1 : ℝ) (M2 : ℝ) (rm : ℝ)) := by
  simp [g1ShiftArg, Expr.evalR]

@[simp] theorem evalR_phiBlockGhat (b : RootBrackets) (t : Expr) (M1 M2 : Rat) :
    (phiBlockGhat b t M1 M2).evalR realEnv =
      V22.phiBlockGhat (t.evalR realEnv) (M1 : ℝ) (M2 : ℝ) := by
  norm_num [phiBlockGhat, Expr.evalR, V22.phiBlockGhat]

theorem evalR_phiBlockG1Bound (b : RootBrackets) (m : FiniteMethods)
    (t : Expr) (M1 M2 rm : Rat) {env : Nat → Ival}
    (henv : ∀ i, (env i).Mem (realEnv i))
    (hguard : signGuard m.q2positive env (phiBlockQ2 M1 M2 rm) = true) :
    (phiBlockG1Bound b m t M1 M2 rm).evalR realEnv =
      V22.phiBlockG1Bound (t.evalR realEnv) (M1 : ℝ) (M2 : ℝ) (rm : ℝ) := by
  cases hq : m.q2positive with
  | false =>
    have hg : (phiBlockQ2 M1 M2 rm).upperOK env 0 = true := by
      simpa [signGuard, hq] using hguard
    have hle : V22.phiBlockQ2 (M1 : ℝ) (M2 : ℝ) (rm : ℝ) ≤ 0 := by
      simpa using (phiBlockQ2 M1 M2 rm).upperOK_sound 0 henv hg
    simp [phiBlockG1Bound, hq, Expr.evalR, V22.phiBlockG1Bound, not_lt_of_ge hle]
  | true =>
    have hg : (phiBlockQ2 M1 M2 rm).positiveOK env = true := by
      simpa [signGuard, hq] using hguard
    have hpos : 0 < V22.phiBlockQ2 (M1 : ℝ) (M2 : ℝ) (rm : ℝ) := by
      simpa using (phiBlockQ2 M1 M2 rm).positiveOK_sound henv hg
    simp [phiBlockG1Bound, hq, Expr.evalR, V22.phiBlockG1Bound, hpos]

theorem evalR_phiBlockRemainder (b : RootBrackets) (m : FiniteMethods)
    (t : Expr) (M1 M2 rm : Rat) {env : Nat → Ival}
    (henv : ∀ i, (env i).Mem (realEnv i))
    (hq : signGuard m.q2positive env (phiBlockQ2 M1 M2 rm) = true)
    (hquad : boundedSignGuard m.quadratic env (phiBlockGhat b t M1 M2)
      (blockN M1) (phiBlockNuMax M2 rm) (Expr.rat rm) = true) :
    (phiBlockRemainder b m t M1 M2 rm).evalR realEnv =
      V22.phiBlockRemainder (t.evalR realEnv) (M1 : ℝ) (M2 : ℝ) (rm : ℝ) := by
  unfold phiBlockRemainder
  rw [evalR_dUbarBlock realEnv m.quadratic _ _ _ _ _ henv hquad,
    evalR_phiBlockG1Bound realEnv b m t M1 M2 rm henv hq]
  simp [Expr.evalR, V22.phiBlockRemainder]

theorem evalR_phiBlock (b : RootBrackets) (m : FiniteMethods)
    (t M : Expr) (M1 M2 rm : Rat) {env : Nat → Ival}
    (henv : ∀ i, (env i).Mem (realEnv i))
    (hguard : finiteGuard b m env t M1 M2 rm = true) :
    (phiBlock b m t M M1 M2 rm).evalR realEnv =
      V22.phiBlock (t.evalR realEnv) (M.evalR realEnv) (M1 : ℝ) (M2 : ℝ) (rm : ℝ) := by
  simp only [finiteGuard, Bool.and_eq_true] at hguard
  rcases hguard with ⟨⟨hq, _⟩, hquad⟩
  unfold phiBlock
  rw [evalR_phiWithRemainder,
    evalR_phiBlockRemainder realEnv b m t M1 M2 rm henv hq hquad]
  rfl

/-- A concrete pass bounds the exact finite-block formula. Analytic
transport to the source fiber/window target is a separate consumer. -/
theorem finitePass_sound (b : RootBrackets) (m : FiniteMethods)
    (t M : Expr) (M1 M2 rm bound : Rat) {env : Nat → Ival}
    (henv : ∀ i, (env i).Mem (realEnv i))
    (hpass : finitePass b m env t M M1 M2 rm bound = true) :
    V22.phiBlockCoefficientsValid (M1 : ℝ) (M2 : ℝ) (rm : ℝ) ∧
      V22.phiBlock (t.evalR realEnv) (M.evalR realEnv)
        (M1 : ℝ) (M2 : ℝ) (rm : ℝ) ≤ (bound : ℝ) := by
  simp only [finitePass, Bool.and_eq_true] at hpass
  have hg := hpass.1
  simp only [finiteGuard, Bool.and_eq_true] at hg
  have hrs := (rhoStarBlock (blockN M1) (phiBlockNuMax M2 rm) (Expr.rat rm)).positiveOK_sound
    henv hg.1.2
  have hb := (phiBlock b m t M M1 M2 rm).upperOK_sound bound henv hpass.2
  rw [evalR_phiBlock realEnv b m t M M1 M2 rm henv hpass.1] at hb
  exact ⟨by simpa [Expr.evalR, V22.phiBlockCoefficientsValid] using hrs, hb⟩

@[simp] theorem evalR_Ghat (b : RootBrackets) (t : Expr) (M1 : Rat) :
    (Ghat b t M1).evalR realEnv = V22.Ghat (t.evalR realEnv) (M1 : ℝ) := by
  simp [Ghat, Expr.evalR, V22.Ghat]

@[simp] theorem evalR_infiniteFirstB (b : RootBrackets) (t : Expr) (M1 rm : Rat) :
    (infiniteFirstB b t M1 rm).evalR realEnv = (M1 : ℝ) + 2 - 1 -
      V22.kappaA ((M1 : ℝ) + 2) (rm : ℝ) * V22.Ghat (t.evalR realEnv) (M1 : ℝ) /
        V22.rhoStar ((M1 : ℝ) + 2) (rm : ℝ) := by
  simp [infiniteFirstB, Expr.evalR]

@[simp] theorem evalR_infiniteBetaE (M1 rm : Rat) :
    (infiniteBetaE M1 rm).evalR realEnv =
      V22.betaE ((M1 : ℝ) + 2) (rm : ℝ)
        (min 6 ((rm : ℝ) * Real.sqrt ((M1 : ℝ) + 2))) := by
  simp [infiniteBetaE, Expr.evalR]

@[simp] theorem evalR_phiInfiniteBlockRemainder (b : RootBrackets) (t : Expr) (M1 rm : Rat) :
    (phiInfiniteBlockRemainder b t M1 rm).evalR realEnv =
      V22.phiInfiniteBlockRemainder (t.evalR realEnv) (M1 : ℝ) (rm : ℝ) := by
  simp [phiInfiniteBlockRemainder, Expr.evalR, V22.phiInfiniteBlockRemainder, V22.dUbar]

@[simp] theorem evalR_phiInfiniteBlock (b : RootBrackets) (t M : Expr) (M1 rm : Rat) :
    (phiInfiniteBlock b t M M1 rm).evalR realEnv =
      V22.phiInfiniteBlock (t.evalR realEnv) (M.evalR realEnv) (M1 : ℝ) (rm : ℝ) := by
  simp [phiInfiniteBlock, V22.phiInfiniteBlock]

theorem infiniteGuard_sound (b : RootBrackets) (t : Expr) (M1 rm : Rat)
    {env : Nat → Ival} (henv : ∀ i, (env i).Mem (realEnv i))
    (hguard : infiniteGuard b env t M1 rm = true) :
    V22.phiInfiniteBlockCoefficientsValid (t.evalR realEnv) (M1 : ℝ) (rm : ℝ) := by
  simp only [infiniteGuard, Bool.and_eq_true] at hguard
  have hrs := (CoefficientExprs.rhoStar (blockN M1) (Expr.rat rm)).positiveOK_sound
    henv hguard.1.1
  have hfirst := (infiniteFirstB b t M1 rm).positiveOK_sound henv hguard.1.2
  have hbeta := (infiniteBetaE M1 rm).positiveOK_sound henv hguard.2
  exact ⟨by simpa [Expr.evalR] using hrs, by simpa using hfirst, by simpa using hbeta⟩

/-- A pass on the final block bounds its all-`ν` formula and retains all
three positive coefficients. No finite quadratic minimum is substituted. -/
theorem infinitePass_sound (b : RootBrackets) (t M : Expr) (M1 rm bound : Rat)
    {env : Nat → Ival} (henv : ∀ i, (env i).Mem (realEnv i))
    (hpass : infinitePass b env t M M1 rm bound = true) :
    V22.phiInfiniteBlockCoefficientsValid (t.evalR realEnv) (M1 : ℝ) (rm : ℝ) ∧
      V22.phiInfiniteBlock (t.evalR realEnv) (M.evalR realEnv) (M1 : ℝ) (rm : ℝ) ≤ (bound : ℝ) := by
  simp only [infinitePass, Bool.and_eq_true] at hpass
  have hb := (phiInfiniteBlock b t M M1 rm).upperOK_sound bound henv hpass.2
  rw [evalR_phiInfiniteBlock] at hb
  exact ⟨infiniteGuard_sound realEnv b t M1 rm henv hpass.1, hb⟩

end

end Erdos993Lean.Analytic.V22.Compute.RayExprs
