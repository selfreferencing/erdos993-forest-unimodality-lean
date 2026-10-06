import Erdos993Lean.Analytic.V22.Analysis.SharedRoot
import Mathlib.Tactic

/-!
# The minimum over every integer offset is attained

Source: Sections 5.1 and 5.6 of the repaired fiber note. The finite window
below is only a proof device: the public minimum and deficit still quantify
over all integer offsets. The binomial support is retained, together with the
quadratic tails on both sides. This supplies the `min_j`/`sInf` bridge required
by the finite-check interface, without an attainment assumption.
-/

namespace Erdos993Lean.Analytic.V22.Analysis

open Erdos993Lean.Analytic.NoValley
open Finset Set

theorem weightedKernel_eq_zero_outside (q : ℝ) (M : ℕ) (j : ℤ)
    (hj : j < -1 ∨ (M : ℤ) + 1 < j) : weightedKernel q M j = 0 := by
  unfold weightedKernel kernel2 fL fR
  rcases hj with hj | hj
  · rw [binom_of_neg (by omega : j < 0), binom_of_neg (by omega : j - 1 < 0),
      binom_of_neg (by omega : j + 1 < 0)]
    ring
  · rw [binom_of_gt (by omega : (M : ℤ) < j),
      binom_of_gt (by omega : (M : ℤ) < j - 1),
      binom_of_gt (by omega : (M : ℤ) < j + 1)]
    ring

theorem fiber_eq_tail (q mu : ℝ) (M : ℕ) (j : ℤ)
    (hj : j < -1 ∨ (M : ℤ) + 1 < j) :
    fiber q mu M j = offset q M j ^ 2 / sigma q mu ^ 2 := by
  unfold fiber
  rw [weightedKernel_eq_zero_outside q M j hj]
  ring

private theorem offset_center_bounds {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (M : ℕ) :
    -(1 / 2 : ℝ) ≤ q * M + signedR q / 2 ∧
      q * M + signedR q / 2 ≤ (M : ℝ) + 1 / 2 := by
  have hl : 0 ≤ q * (M : ℝ) := mul_nonneg hq0 (Nat.cast_nonneg M)
  have hu : q * (M : ℝ) ≤ (M : ℝ) := by
    simpa using mul_le_mul_of_nonneg_right hq1 (Nat.cast_nonneg M)
  unfold signedR
  constructor <;> linarith

theorem fiber_left_tail_lower {q mu : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (M : ℕ) {j : ℤ} (hj : j ≤ -2) : fiber q mu M (-2) ≤ fiber q mu M j := by
  have hcenter := (offset_center_bounds hq0 hq1 M).1
  have hjr : (j : ℝ) ≤ -2 := by exact_mod_cast hj
  have hbase : offset q M (-2) ≤ 0 := by
    unfold offset
    norm_num only [Int.cast_neg, Int.cast_ofNat]
    linarith
  have horder : offset q M j ≤ offset q M (-2) := by
    unfold offset
    norm_num only [Int.cast_neg, Int.cast_ofNat]
    linarith
  have hs : offset q M (-2) ^ 2 ≤ offset q M j ^ 2 := by
    nlinarith
  rw [fiber_eq_tail q mu M (-2) (Or.inl (by omega)),
    fiber_eq_tail q mu M j (Or.inl (by omega))]
  exact div_le_div_of_nonneg_right hs (sq_nonneg _)

theorem fiber_right_tail_lower {q mu : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (M : ℕ) {j : ℤ} (hj : (M : ℤ) + 2 ≤ j) :
    fiber q mu M ((M : ℤ) + 2) ≤ fiber q mu M j := by
  have hcenter := (offset_center_bounds hq0 hq1 M).2
  have hjr : (M : ℝ) + 2 ≤ (j : ℝ) := by exact_mod_cast hj
  have hbase : 0 ≤ offset q M ((M : ℤ) + 2) := by
    unfold offset
    push_cast
    linarith
  have horder : offset q M ((M : ℤ) + 2) ≤ offset q M j := by
    unfold offset
    push_cast
    linarith
  have hs := (sq_le_sq₀ hbase (hbase.trans horder)).2 horder
  rw [fiber_eq_tail q mu M ((M : ℤ) + 2) (Or.inr (by omega)),
    fiber_eq_tail q mu M j (Or.inr (by omega))]
  exact div_le_div_of_nonneg_right hs (sq_nonneg _)

/-- Every integer fiber is bounded below by one fiber in an explicit finite
window. The kernel and penalty are both kept, rather than truncating support. -/
theorem fiber_finite_window {q mu : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (M : ℕ) (j : ℤ) :
    ∃ k ∈ Finset.Icc (-2 : ℤ) ((M : ℤ) + 2), fiber q mu M k ≤ fiber q mu M j := by
  rcases lt_or_ge j (-2) with hj | hj
  · exact ⟨-2, by simp; omega, fiber_left_tail_lower hq0 hq1 M hj.le⟩
  · rcases le_or_gt j ((M : ℤ) + 2) with hjM | hjM
    · exact ⟨j, mem_Icc.mpr ⟨hj, hjM⟩, le_rfl⟩
    · exact ⟨(M : ℤ) + 2, by simp; omega,
        fiber_right_tail_lower hq0 hq1 M hjM.le⟩

/-- The source's `min_j` exists for every fiber, over the full integer domain. -/
theorem fiber_minimum_attained {q mu : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (M : ℕ) :
    ∃ j : ℤ, ∀ k : ℤ, fiber q mu M j ≤ fiber q mu M k := by
  have hne : (Finset.Icc (-2 : ℤ) ((M : ℤ) + 2)).Nonempty :=
    ⟨0, by simp; omega⟩
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image
    (Finset.Icc (-2 : ℤ) ((M : ℤ) + 2)) (fiber q mu M) hne
  refine ⟨j, fun k => ?_⟩
  obtain ⟨i, hi, hik⟩ := fiber_finite_window hq0 hq1 M k
  exact (hmin i hi).trans hik

/-- Exact identification of lane D's real infimum with an attained fiber. -/
theorem shared_fiberInfimum_attained {q mu : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (M : ℕ) :
    ∃ j : ℤ, V22.fiberInfimum q mu M = V22.fiberFunction q mu M j ∧
      ∀ k : ℤ, V22.fiberFunction q mu M j ≤ V22.fiberFunction q mu M k := by
  obtain ⟨j, hj⟩ := fiber_minimum_attained (mu := mu) hq0 hq1 M
  have hleast : IsLeast (Set.range (V22.fiberFunction q mu M))
      (V22.fiberFunction q mu M j) := by
    refine ⟨⟨j, rfl⟩, ?_⟩
    rintro x ⟨k, rfl⟩
    simpa only [shared_fiberFunction_eq] using hj k
  refine ⟨j, hleast.csInf_eq, fun k => ?_⟩
  simpa only [shared_fiberFunction_eq] using hj k

theorem shared_fiberInfimum_le {q mu : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (M : ℕ) (j : ℤ) : V22.fiberInfimum q mu M ≤ V22.fiberFunction q mu M j := by
  obtain ⟨k, hk, hmin⟩ := shared_fiberInfimum_attained (mu := mu) hq0 hq1 M
  rw [hk]
  exact hmin j

/-- The exact positive-part deficit pays every integer fiber. -/
theorem shared_deficitG_pays {q mu b beta : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (M : ℕ) (j : ℤ) :
    V22.psi ((M : ℝ) / mu) + V22.targetLine b beta ((M : ℝ) / mu) -
      V22.deficitG q mu b beta M ≤ V22.fiberFunction q mu M j := by
  have hinf := shared_fiberInfimum_le (mu := mu) hq0 hq1 M j
  unfold V22.deficitG V22.positivePart
  have h := le_max_left
    (V22.psi ((M : ℝ) / mu) + V22.targetLine b beta ((M : ℝ) / mu) -
      V22.fiberInfimum q mu M) (0 : ℝ)
  linarith

end Erdos993Lean.Analytic.V22.Analysis
