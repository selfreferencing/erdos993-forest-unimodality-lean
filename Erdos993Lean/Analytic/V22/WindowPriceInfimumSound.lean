import Erdos993Lean.Analytic.V22.Checks.LateStatements

/-!
# The one-sided infimum step in the marked-spike window price

Source: repaired note Corollary 5.15, the window-price branch of its proof.
This module consumes an explicit lower bound on `fiberFunction` for every
integer offset. It does not prove the analytic window minorant or produce
`DeficitToWindowPriceTransport`. The lower-bound family preserves the actual
`q`, `mu`, integer fiber `M`, and all offsets `j : Int`.

The range is nonempty, and the supplied pointwise family proves it bounded
below. No attainment of a minimum is needed for this one-sided `sInf` bound.
The original-cell analytic comparison required by the consumer is recorded
separately in `CHECKS/V22/D2/WINDOW_PRICE_DEPENDENCIES.md`.
-/

namespace Erdos993Lean.Analytic.V22

noncomputable section

/-- The infimum in the actual deficit ranges over a nonempty integer family. -/
theorem fiberFunction_range_nonempty (q mu : ℝ) (M : ℕ) :
    (Set.range (fun j : ℤ => fiberFunction q mu M j)).Nonempty := by
  exact ⟨fiberFunction q mu M 0, ⟨0, rfl⟩⟩

/-- A pointwise lower family supplies the boundedness needed for the actual
real infimum, with no restriction of its integer-offset domain. -/
theorem fiberFunction_range_bddBelow_of_lower {q mu L : ℝ} {M : ℕ}
    (hpoint : ∀ j : ℤ, L ≤ fiberFunction q mu M j) :
    BddBelow (Set.range (fun j : ℤ => fiberFunction q mu M j)) := by
  refine ⟨L, ?_⟩
  intro y hy
  obtain ⟨j, rfl⟩ := hy
  exact hpoint j

/-- The actual `sInf` is above each retained pointwise lower bound. -/
theorem fiberInfimum_ge_of_pointwise {q mu L : ℝ} {M : ℕ}
    (hpoint : ∀ j : ℤ, L ≤ fiberFunction q mu M j) :
    L ≤ fiberInfimum q mu M := by
  apply le_csInf (fiberFunction_range_nonempty q mu M)
  intro y hy
  obtain ⟨j, rfl⟩ := hy
  exact hpoint j

/-- A nonnegative multiplier bounded by `Bmax` gives the conservative lower
price for either sign of `X`. -/
theorem neg_window_loss_le_mul {B Bmax X : ℝ}
    (hB : 0 ≤ B) (hBB : B ≤ Bmax) :
    -(Bmax * positivePart (-X)) ≤ B * X := by
  have hpos : 0 ≤ positivePart (-X) := le_max_right (-X) 0
  have hX : -positivePart (-X) ≤ X := by
    have h := le_max_left (-X) (0 : ℝ)
    change -X ≤ positivePart (-X) at h
    linarith
  have hfirst := mul_le_mul_of_nonneg_left hX hB
  have hsecond := mul_le_mul_of_nonneg_right hBB hpos
  nlinarith

/-- Nonemptiness, boundedness, and the exact conservative lower infimum
price are all supplied by the pointwise family. The family is a hypothesis,
not a conclusion of a finite numerical certificate. -/
theorem fiberInfimum_window_lower {q mu B Bmax X : ℝ} {M : ℕ}
    (hB : 0 ≤ B) (hBB : B ≤ Bmax)
    (hpoint : ∀ j : ℤ, B * X ≤ fiberFunction q mu M j) :
    (Set.range (fun j : ℤ => fiberFunction q mu M j)).Nonempty ∧
      BddBelow (Set.range (fun j : ℤ => fiberFunction q mu M j)) ∧
      -(Bmax * positivePart (-X)) ≤ fiberInfimum q mu M := by
  exact ⟨fiberFunction_range_nonempty q mu M,
    fiberFunction_range_bddBelow_of_lower hpoint,
    (neg_window_loss_le_mul hB hBB).trans (fiberInfimum_ge_of_pointwise hpoint)⟩

/-- Corollary 5.15's one-sided algebraic consumer at the supplied exact
coordinate `t=M/mu`. Positivity of `mu` is retained for the analytic caller;
the infimum step itself uses the explicit pointwise family and multiplier
bounds. This theorem does not prove that family. -/
theorem deficitG_le_window_price_of_pointwise {q mu b beta t B Bmax X : ℝ}
    {M : ℕ} (_hmu : 0 < mu) (hcoordinate : (M : ℝ) / mu = t)
    (hB : 0 ≤ B) (hBB : B ≤ Bmax)
    (hpoint : ∀ j : ℤ, B * X ≤ fiberFunction q mu M j) :
    deficitG q mu b beta M ≤
      positivePart (psi t + targetLine b beta t + Bmax * positivePart (-X)) := by
  have hInf := (fiberInfimum_window_lower hB hBB hpoint).2.2
  have hdiff : psi t + targetLine b beta t - fiberInfimum q mu M ≤
      psi t + targetLine b beta t + Bmax * positivePart (-X) := by
    linarith
  simpa only [deficitG, hcoordinate, positivePart] using
    max_le_max hdiff (le_refl (0 : ℝ))

/-- The same exact infimum consumer expressed using the retained class
target. It makes no class/cell or analytic-window claim. -/
theorem deficitG_le_class_window_price_of_pointwise {c : V22Class}
    {q mu t B Bmax X : ℝ} {M : ℕ}
    (hmu : 0 < mu) (hcoordinate : (M : ℝ) / mu = t)
    (hB : 0 ≤ B) (hBB : B ≤ Bmax)
    (hpoint : ∀ j : ℤ, B * X ≤ fiberFunction q mu M j) :
    deficitG q mu c.b c.beta M ≤
      positivePart (Checks.classTarget c t + Bmax * positivePart (-X)) := by
  simpa only [Checks.classTarget, targetLine, add_assoc] using
    (deficitG_le_window_price_of_pointwise (b := (c.b : ℝ))
      (beta := (c.beta : ℝ)) hmu hcoordinate hB hBB hpoint)

/-- Exact `mu=M/t` normalization for the marked-spike caller. The positive
integer fiber and positive `t` prove `mu>0`; no rounded mean is introduced. -/
theorem deficitG_div_le_class_window_price_of_pointwise {c : V22Class}
    {q t B Bmax X : ℝ} {M : ℕ} (hM : 0 < M) (ht : 0 < t)
    (hB : 0 ≤ B) (hBB : B ≤ Bmax)
    (hpoint : ∀ j : ℤ, B * X ≤ fiberFunction q ((M : ℝ) / t) M j) :
    deficitG q ((M : ℝ) / t) c.b c.beta M ≤
      positivePart (Checks.classTarget c t + Bmax * positivePart (-X)) := by
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have hmu : 0 < (M : ℝ) / t := div_pos hMr ht
  have hcoordinate : (M : ℝ) / ((M : ℝ) / t) = t := by
    field_simp [hMr.ne', ht.ne'] <;> ring
  exact deficitG_le_class_window_price_of_pointwise hmu hcoordinate hB hBB hpoint

end

end Erdos993Lean.Analytic.V22
