import Erdos993Lean.Analytic.V22.Analysis.Kernel
import Mathlib.Tactic

/-! Source: note Lemma 3.2. The reflection retains every integer fiber index,
including both support boundaries and the indices outside support. -/

namespace Erdos993Lean.Analytic.V22.Analysis

open Erdos993Lean.Analytic.NoValley

theorem binom_reflection (M : ℕ) (q : ℝ) (j : ℤ) :
    binom M (1 - q) ((M : ℤ) - j) = binom M q j := by
  rcases lt_or_ge j 0 with hj | hj
  · rw [binom_of_neg hj, binom_of_gt (by omega : (M : ℤ) < (M : ℤ) - j)]
  · by_cases hjM : (M : ℤ) < j
    · rw [binom_of_gt hjM, binom_of_neg (by omega : (M : ℤ) - j < 0)]
    · lift j to ℕ using hj
      have hle : j ≤ M := by omega
      have hidx : (M : ℤ) - (j : ℤ) = ((M - j : ℕ) : ℤ) := by omega
      rw [hidx, binom_natCast_of_le (1 - q) (by omega), binom_natCast_of_le q hle,
        Nat.choose_symm hle, Nat.sub_sub_self hle]
      have he : 1 - (1 - q) = q := by ring
      rw [he]
      ring

theorem signedR_reflection (q : ℝ) : signedR (1 - q) = -signedR q := by
  unfold signedR
  ring

theorem variance_reflection (q : ℝ) : variance (1 - q) = variance q := by
  unfold variance
  ring

/-- Source note Lemma 3.2: the actual offset changes sign. -/
theorem offset_reflection (q : ℝ) (M : ℕ) (j : ℤ) :
    offset (1 - q) M ((M : ℤ) - j) = -offset q M j := by
  unfold offset signedR
  push_cast
  ring

/-- Source note Lemma 3.2: exact reflection of the weighted kernel. -/
theorem weightedKernel_reflection {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (M : ℕ) (j : ℤ) :
    weightedKernel (1 - q) M ((M : ℤ) - j) = weightedKernel q M j := by
  rw [weightedKernel_eq (by linarith : 0 < 1 - q) (by linarith : 1 - q < 1),
    weightedKernel_eq hq0 hq1, offset_reflection, signedR_reflection]
  have hi : (M : ℤ) - j + 1 = ((M + 2 : ℕ) : ℤ) - (j + 1) := by omega
  rw [hi, binom_reflection]
  simp only [neg_sq]

/-- Source note Lemma 3.2: exact reflection of the complete fiber function. -/
theorem fiber_reflection {q mu : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (M : ℕ) (j : ℤ) :
    fiber (1 - q) mu M ((M : ℤ) - j) = fiber q mu M j := by
  unfold fiber sigma
  rw [variance_reflection, weightedKernel_reflection hq0 hq1, offset_reflection]
  simp only [neg_sq]

end Erdos993Lean.Analytic.V22.Analysis
