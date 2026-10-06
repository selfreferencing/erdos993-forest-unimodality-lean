import Erdos993Lean.Analytic.V22.Compute.B1
import Erdos993Lean.Analytic.V22.ExprSound
import Erdos993Lean.Analytic.V22.GridSound
import Erdos993Lean.Analytic.V22.Checks.EarlyStatements
import Erdos993Lean.Analytic.MGF.Atoms

/-!
# B1: the exact expression denotes the source kernel

The support convention agrees with binom. Outside [-1,M+1] the existing
two-sided kernel theorems prove exact zero. The finite checker is consumed
only through expression and partition soundness; no certificate is assumed.
-/

namespace Erdos993Lean.Analytic.V22.B1Sound

open Erdos993Lean.Analytic
open Erdos993Lean.Analytic.V22.Compute
open Erdos993Lean.Analytic.V22.Compute.B1

noncomputable section

@[simp] theorem binNat_eq_choose (n k : Nat) : binNat n k = n.choose k := by
  induction n generalizing k with
  | zero => cases k <;> simp [binNat]
  | succ n ih => cases k <;> simp [binNat, Nat.choose_succ_succ, ih, add_comm]

theorem binomialE_meaning (M : Nat) (j : Int) (env : Nat → ℝ) :
    (binomialE M j).evalR env = binom M (env 0) j := by
  by_cases h : 0 ≤ j ∧ j ≤ (M : Int)
  · simp [binomialE, binom, h, Expr.evalR, qE, oneMinusQE, Rat.cast_natCast]
  · simp [binomialE, binom, h, Expr.evalR]

theorem kernelE_meaning (M : Nat) (j : Int) (env : Nat → ℝ) :
    (kernelE M j).evalR env =
      kernel2 (env 0) (weightL (env 0)) (weightR (env 0)) M j := by
  simp only [kernelE, fLE, fRE, weightLE, weightRE, qE, oneMinusQE,
    Expr.evalR, binomialE_meaning, Rat.cast_zero, Rat.cast_one, Rat.cast_ofNat]
  unfold kernel2 fL fR weightL weightR
  simp only [div_eq_mul_inv]
  ring

theorem slackE_meaning (M : Nat) (j : Int) (env : Nat → ℝ) :
    (slackE M j).evalR env =
      kernel2 (env 0) (weightL (env 0)) (weightR (env 0)) M j +
        (smallK.getD M 0 : ℝ) - (smallMargins.getD M 0 : ℝ) := by
  simp only [slackE, Expr.evalR, kernelE_meaning]

theorem kernel_outside (M : Nat) (j : Int) (q : ℝ)
    (hj : j < -1 ∨ (M : Int) + 1 < j) :
    kernel2 q (weightL q) (weightR q) M j = 0 := by
  rcases hj with hj | hj
  · exact MGF.kernel2_of_lt hj
  · exact MGF.kernel2_of_gt hj

/-- A passing partition and expression list gives the claimed actual margin
on the whole source activity interval for this retained atom. -/
theorem atom_sound (M : Nat) (j : Int)
    (hcover : partitionFrom (1 / 4) (3 / 4) qPieces = true)
    (hpass : nonnegativeOn (slackE M j) qPieces = true) {q : ℝ}
    (hq : Checks.inCell (1 / 4) (3 / 4) q) :
    (smallMargins.getD M 0 : ℝ) ≤
      kernel2 q (weightL q) (weightR q) M j + (smallK.getD M 0 : ℝ) := by
  have hq' : ((1 / 4 : Rat) : ℝ) ≤ q ∧ q ≤ ((3 / 4 : Rat) : ℝ) := by
    simpa [Checks.inCell] using hq
  have hs := nonnegativeOn_sound hcover hpass hq'
  rw [slackE_meaning] at hs
  change 0 ≤ kernel2 q (weightL q) (weightR q) M j +
    (smallK.getD M 0 : ℝ) - (smallMargins.getD M 0 : ℝ) at hs
  exact sub_nonneg.mp hs

/-- The finite certificate is consumed without discarding fibers, offsets,
activity endpoints, source margins, or the outside-support zero assertion. -/
theorem check_sound (hcheck : check = true) : Checks.lemma_7_12 := by
  simp only [check, Bool.and_eq_true] at hcheck
  intro M hM j q hq
  constructor
  · intro hj
    let k : Nat := (j + 1).toNat
    have hkcast : (k : Int) = j + 1 := by
      exact Int.toNat_of_nonneg (by omega)
    have hk : k < M + 3 := by omega
    have hjoffset : offset k = j := by unfold offset; omega
    have hMmem : M ∈ List.range 8 := List.mem_range.mpr (by omega)
    have hkmem : k ∈ List.range (M + 3) := List.mem_range.mpr hk
    have hfiber : (List.range (M + 3)).all (fun k =>
        nonnegativeOn (slackE M (offset k)) qPieces) = true :=
      List.all_eq_true.mp hcheck.2 M hMmem
    have hatom := List.all_eq_true.mp hfiber k hkmem
    rw [hjoffset] at hatom
    exact atom_sound M j hcheck.1 hatom hq
  · intro hj
    exact kernel_outside M j q hj

end
end Erdos993Lean.Analytic.V22.B1Sound
