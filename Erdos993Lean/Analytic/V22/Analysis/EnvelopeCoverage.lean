import Erdos993Lean.Analytic.V22.Analysis.SharedActivity

/-!
# Exact nine-cell coverage for the v2.2 envelope theorem

Source: Lemma 7.3 and the proof of Theorem 4.15. The cover includes every
closed endpoint. Its starts are exactly `M0=19*t(s_a)`; neither the source
first start nor any cell endpoint is replaced by a rounded rational.
All start-domain facts are elementary theorems, not further finite premises.
The parent owns Lean verification.
-/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

/-- The exact shared list covers the complete root-coordinate interval. -/
theorem envelopeCells_cover {s : ℝ} (hs0 : -(66 / 125 : ℝ) ≤ s)
    (hs1 : s ≤ 67 / 100) :
    ∃ c ∈ Checks.envelopeCells, Checks.inCell (c.1 : ℝ) (c.2 : ℝ) s := by
  by_cases h1 : s ≤ -(373 / 1000 : ℝ)
  · refine ⟨(-66 / 125, -373 / 1000), by norm_num [Checks.envelopeCells], ?_⟩
    norm_num [Checks.inCell]
    exact ⟨hs0, h1⟩
  by_cases h2 : s ≤ -(13 / 125 : ℝ)
  · refine ⟨(-373 / 1000, -13 / 125), by norm_num [Checks.envelopeCells], ?_⟩
    norm_num [Checks.inCell]
    exact ⟨(lt_of_not_ge h1).le, h2⟩
  by_cases h3 : s ≤ 0
  · refine ⟨(-13 / 125, 0), by norm_num [Checks.envelopeCells], ?_⟩
    norm_num [Checks.inCell]
    exact ⟨(lt_of_not_ge h2).le, h3⟩
  by_cases h4 : s ≤ 31 / 200
  · refine ⟨(0, 31 / 200), by norm_num [Checks.envelopeCells], ?_⟩
    norm_num [Checks.inCell]
    exact ⟨(lt_of_not_ge h3).le, h4⟩
  by_cases h5 : s ≤ 47 / 200
  · refine ⟨(31 / 200, 47 / 200), by norm_num [Checks.envelopeCells], ?_⟩
    norm_num [Checks.inCell]
    exact ⟨(lt_of_not_ge h4).le, h5⟩
  by_cases h6 : s ≤ 317 / 1000
  · refine ⟨(47 / 200, 317 / 1000), by norm_num [Checks.envelopeCells], ?_⟩
    norm_num [Checks.inCell]
    exact ⟨(lt_of_not_ge h5).le, h6⟩
  by_cases h7 : s ≤ 53 / 125
  · refine ⟨(317 / 1000, 53 / 125), by norm_num [Checks.envelopeCells], ?_⟩
    norm_num [Checks.inCell]
    exact ⟨(lt_of_not_ge h6).le, h7⟩
  by_cases h8 : s ≤ 117 / 200
  · refine ⟨(53 / 125, 117 / 200), by norm_num [Checks.envelopeCells], ?_⟩
    norm_num [Checks.inCell]
    exact ⟨(lt_of_not_ge h7).le, h8⟩
  · refine ⟨(117 / 200, 67 / 100), by norm_num [Checks.envelopeCells], ?_⟩
    norm_num [Checks.inCell]
    exact ⟨(lt_of_not_ge h8).le, hs1⟩

/-- Every listed cell retains its genuine ordered endpoints and full domain. -/
theorem envelopeCell_bounds {c : ℚ × ℚ} (hc : c ∈ Checks.envelopeCells) :
    -(66 / 125 : ℝ) ≤ (c.1 : ℝ) ∧ (c.1 : ℝ) ≤ (c.2 : ℝ) ∧
      (c.2 : ℝ) ≤ 67 / 100 := by
  simp only [Checks.envelopeCells, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- An elementary lower bound at the first exact endpoint; no interval
certificate is needed merely to license `M0>=8`. -/
theorem envelope_first_coordinate_ge_half :
    (1 / 2 : ℝ) ≤ activityOneCoordinate (-(66 / 125 : ℝ)) := by
  have he : (59 / 125 : ℝ) ≤ Real.exp (-(66 / 125 : ℝ)) := by
    have h := Real.add_one_le_exp (-(66 / 125 : ℝ))
    linarith
  have hesq : (59 / 125 : ℝ) ^ 2 ≤ Real.exp (-(66 / 125 : ℝ)) ^ 2 :=
    (sq_le_sq₀ (by norm_num) (Real.exp_pos _).le).2 he
  have hscaled := mul_le_mul_of_nonneg_right hesq
    (by norm_num : 0 ≤ (59 / 125 : ℝ) ^ 2)
  apply (pow_le_pow_iff_left₀ (by norm_num : 0 ≤ (1 / 2 : ℝ))
    (activityOneCoordinate_pos (s := -(66 / 125 : ℝ)) (by norm_num)).le
    (by decide : (5 : ℕ) ≠ 0)).1
  rw [gaussian_coordinate_pow_five (by norm_num)]
  have htwo : 2 * (-(66 / 125 : ℝ)) = -(66 / 125 : ℝ) + -(66 / 125 : ℝ) := by ring
  have hone : 1 + (-(66 / 125 : ℝ)) = (59 / 125 : ℝ) := by norm_num
  rw [htwo, hone, Real.exp_add]
  norm_num at hscaled ⊢
  nlinarith

theorem envelopeCell_coordinate_ge_half {c : ℚ × ℚ} (hc : c ∈ Checks.envelopeCells) :
    (1 / 2 : ℝ) ≤ Erdos993Lean.Analytic.V22.tOfS c.1 := by
  have hbounds := envelopeCell_bounds hc
  have hmono := activityOneCoordinate_strictMonoOn.monotoneOn
    (show -(66 / 125 : ℝ) ∈ Ioi (-1) by norm_num)
    (show (c.1 : ℝ) ∈ Ioi (-1) by simp only [mem_Ioi]; linarith)
    hbounds.1
  rw [shared_tOfS_eq]
  exact envelope_first_coordinate_ge_half.trans hmono

/-- Exact cell starting size, with a strictly stronger elementary lower bound. -/
theorem envelopeCell_start_domain {c : ℚ × ℚ} (hc : c ∈ Checks.envelopeCells) :
    0 < 19 * Erdos993Lean.Analytic.V22.tOfS c.1 ∧
      (8 : ℝ) ≤ 19 * Erdos993Lean.Analytic.V22.tOfS c.1 := by
  have h := envelopeCell_coordinate_ge_half hc
  constructor <;> linarith

theorem envelopeCell_start_le_coordinate {c : ℚ × ℚ} (hc : c ∈ Checks.envelopeCells)
    {s : ℝ} (hs : Checks.inCell (c.1 : ℝ) (c.2 : ℝ) s) :
    19 * Erdos993Lean.Analytic.V22.tOfS c.1 ≤ 19 * Erdos993Lean.Analytic.V22.tOfS s := by
  have hbounds := envelopeCell_bounds hc
  have hcl : -1 < (c.1 : ℝ) := by linarith [hbounds.1]
  have hsl : -1 < s := by linarith [hs.1]
  exact mul_le_mul_of_nonneg_left
    (shared_tOfS_strictMonoOn.monotoneOn hcl hsl hs.1) (by norm_num)

/-- The exact envelope start is below the actual fiber size when `mu>=19`;
the coordinate equality is the lossless root representation of that fiber. -/
theorem envelopeCell_start_le_fiber {c : ℚ × ℚ} (hc : c ∈ Checks.envelopeCells)
    {s mu M : ℝ} (hs : Checks.inCell (c.1 : ℝ) (c.2 : ℝ) s)
    (hmu : 19 ≤ mu) (ht : Erdos993Lean.Analytic.V22.tOfS s = M / mu) :
    19 * Erdos993Lean.Analytic.V22.tOfS c.1 ≤ M := by
  have hbounds := envelopeCell_bounds hc
  have hsp : -1 < s := by linarith [hbounds.1, hs.1]
  have htp := (shared_tOfS_pos hsp).le
  have hmu0 : 0 < mu := by linarith
  calc
    19 * Erdos993Lean.Analytic.V22.tOfS c.1 ≤
        19 * Erdos993Lean.Analytic.V22.tOfS s := envelopeCell_start_le_coordinate hc hs
    _ ≤ mu * Erdos993Lean.Analytic.V22.tOfS s := mul_le_mul_of_nonneg_right hmu htp
    _ = M := by rw [ht]; field_simp [hmu0.ne']

end Erdos993Lean.Analytic.V22.Analysis
