import Erdos993Lean.Analytic.V22.Analysis.ActivityOne

/-!
# Paper v2.2: template monotonicity on a fixed activity ray

Source: the monotonicity argument in Theorem 4.15 and the shrinking-interval
argument reused in Lemma 5.4. Every real `M>0` is retained; the endpoint interval
is `[3.55,3.85+10/M]`. Concavity bounds every intermediate `k`, so a negative
first derivative of `G` does not require either endpoint to be extremal.
The parent lane owns Lean verification.
-/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

theorem template_kbar_antitone {M0 M : ℝ} (hM0 : 0 < M0) (hM : M0 ≤ M) :
    (77 / 20 : ℝ) + 10 / M ≤ (77 / 20 : ℝ) + 10 / M0 := by
  have h := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 10 by norm_num) hM0 hM
  linarith

theorem template_kbar_ge_lower {M : ℝ} (hM : 0 < M) :
    (71 / 20 : ℝ) ≤ (77 / 20 : ℝ) + 10 / M := by
  have hdiv : 0 ≤ (10 : ℝ) / M := div_nonneg (by norm_num) hM.le
  linarith

/-- For each retained offset `k`, the template endpoint increases with `M`
when the Gaussian slack is nonnegative. -/
theorem activityOneEndpointValue_monotone {t M0 M k : ℝ} (hM0 : 0 < M0)
    (hM : M0 ≤ M) (hS : 0 ≤ activityOneS t) :
    activityOneEndpointValue t M0 k ≤ activityOneEndpointValue t M k := by
  have hnum : 0 ≤ k ^ 2 * activityOneG2 t :=
    mul_nonneg (sq_nonneg k) (rootGSecond_pos _).le
  have hden : 0 < M0 + 3 := by linarith
  have hquad := div_le_div_of_nonneg_left hnum hden
    (show M0 + 3 ≤ M + 3 by linarith)
  have hlinear := mul_le_mul_of_nonneg_right hM hS
  unfold activityOneEndpointValue
  linarith

/-- Exact Theorem 4.15 monotonicity: use every-k concavity on the larger
interval, then the increasing value at each retained offset. -/
theorem activityOneT_mono {t M0 M : ℝ} (hM0 : 0 < M0) (hM : M0 ≤ M)
    (hS : 0 ≤ activityOneS t) : activityOneT t M0 ≤ activityOneT t M := by
  have hMp : 0 < M := hM0.trans_le hM
  have hlo : activityOneT t M0 ≤ activityOneEndpointValue t M (71 / 20) := by
    exact (activityOneT_le_at_k hM0 le_rfl (template_kbar_ge_lower hM0)).trans
      (activityOneEndpointValue_monotone hM0 hM hS)
  have hhi : activityOneT t M0 ≤
      activityOneEndpointValue t M ((77 / 20 : ℝ) + 10 / M) := by
    exact (activityOneT_le_at_k hM0 (template_kbar_ge_lower hMp)
      (template_kbar_antitone hM0 hM)).trans
      (activityOneEndpointValue_monotone hM0 hM hS)
  exact le_min hlo hhi

theorem activityOneT_monotoneOn (t : ℝ) (hS : 0 ≤ activityOneS t) :
    MonotoneOn (activityOneT t) (Ioi 0) := by
  intro M0 hM0 M _ hM
  exact activityOneT_mono hM0 hM hS

/-- The convex quadratic counterpart needed for Lemma 5.4's endpoint maximum. -/
theorem convexQuadratic_endpoint_max (d c a b k : ℝ) (hc : 0 ≤ c)
    (hak : a ≤ k) (hkb : k ≤ b) :
    d * k + c * k ^ 2 ≤ max (d * a + c * a ^ 2) (d * b + c * b ^ 2) := by
  have h := concaveQuadratic_endpoint_min 0 d c a b k hc hak hkb
  have ha : 0 - d * a - c * a ^ 2 = -(d * a + c * a ^ 2) := by ring
  have hb : 0 - d * b - c * b ^ 2 = -(d * b + c * b ^ 2) := by ring
  have hk : 0 - d * k - c * k ^ 2 = -(d * k + c * k ^ 2) := by ring
  rw [ha, hb, hk, min_neg_neg] at h
  linarith

noncomputable def activityOneLossTerm (t M k : ℝ) : ℝ :=
  2 * k * activityOneG1 t + k ^ 2 * activityOneG2 t / (M + 3)

noncomputable def activityOneLossMax (t M : ℝ) : ℝ :=
  max (activityOneLossTerm t M (71 / 20))
    (activityOneLossTerm t M ((77 / 20 : ℝ) + 10 / M))

theorem activityOneLossTerm_le_max {t M k : ℝ} (hM : 0 < M)
    (hkl : (71 / 20 : ℝ) ≤ k) (hku : k ≤ (77 / 20 : ℝ) + 10 / M) :
    activityOneLossTerm t M k ≤ activityOneLossMax t M := by
  have hc : 0 ≤ activityOneG2 t / (M + 3) :=
    div_nonneg (rootGSecond_pos _).le (by linarith)
  have h := convexQuadratic_endpoint_max (2 * activityOneG1 t)
    (activityOneG2 t / (M + 3)) (71 / 20) ((77 / 20) + 10 / M) k hc hkl hku
  have heq : ∀ x : ℝ, activityOneLossTerm t M x =
      (2 * activityOneG1 t) * x + (activityOneG2 t / (M + 3)) * x ^ 2 := by
    intro x
    unfold activityOneLossTerm
    ring
  unfold activityOneLossMax
  rw [heq, heq, heq]
  exact h

theorem activityOneLossTerm_antitone {t M0 M k : ℝ} (hM0 : 0 < M0)
    (hM : M0 ≤ M) : activityOneLossTerm t M k ≤ activityOneLossTerm t M0 k := by
  have hnum : 0 ≤ k ^ 2 * activityOneG2 t :=
    mul_nonneg (sq_nonneg k) (rootGSecond_pos _).le
  have hquad := div_le_div_of_nonneg_left hnum (show 0 < M0 + 3 by linarith)
    (show M0 + 3 ≤ M + 3 by linarith)
  unfold activityOneLossTerm
  linarith

/-- The exact endpoint maximum in Lemma 5.4 decreases as its interval shrinks;
no sign condition on `G1` or on the slack is used. -/
theorem activityOneLossMax_antitone {t M0 M : ℝ} (hM0 : 0 < M0) (hM : M0 ≤ M) :
    activityOneLossMax t M ≤ activityOneLossMax t M0 := by
  have hMp : 0 < M := hM0.trans_le hM
  have hlo : activityOneLossTerm t M (71 / 20) ≤ activityOneLossMax t M0 :=
    (activityOneLossTerm_antitone hM0 hM).trans
      (activityOneLossTerm_le_max hM0 le_rfl (template_kbar_ge_lower hM0))
  have hhi : activityOneLossTerm t M ((77 / 20 : ℝ) + 10 / M) ≤ activityOneLossMax t M0 :=
    (activityOneLossTerm_antitone hM0 hM).trans
      (activityOneLossTerm_le_max hM0 (template_kbar_ge_lower hMp)
        (template_kbar_antitone hM0 hM))
  exact max_le hlo hhi

/-- A generic fixed-ray Phi expression; the source remainder supplies `D`. -/
noncomputable def activityOnePhiWithRemainder (t M D : ℝ) : ℝ :=
  t * max (-activityOneS t) 0 + t / M *
    max (6 * activityOneG0 t - 2 + D + activityOneLossMax t M) 0

/-- Lemma 5.4's final algebra once the exact remainder has been proved
nonincreasing. The hypothesis concerns only that supplied remainder. -/
theorem activityOnePhiWithRemainder_antitone {t M0 M D0 D : ℝ}
    (ht : 0 ≤ t) (hM0 : 0 < M0) (hM : M0 ≤ M) (hD : D ≤ D0) :
    activityOnePhiWithRemainder t M D ≤ activityOnePhiWithRemainder t M0 D0 := by
  have hMp : 0 < M := hM0.trans_le hM
  have hfactor := div_le_div_of_nonneg_left ht hM0 hM
  have hmax : max (6 * activityOneG0 t - 2 + D + activityOneLossMax t M) 0 ≤
      max (6 * activityOneG0 t - 2 + D0 + activityOneLossMax t M0) 0 := max_le_max (show
      6 * activityOneG0 t - 2 + D + activityOneLossMax t M ≤
        6 * activityOneG0 t - 2 + D0 + activityOneLossMax t M0 from
      by
        have hLoss := activityOneLossMax_antitone (t := t) hM0 hM
        linarith) le_rfl
  have hprod := mul_le_mul hfactor hmax (le_max_right _ _)
    (div_nonneg ht hM0.le)
  unfold activityOnePhiWithRemainder
  linarith

end Erdos993Lean.Analytic.V22.Analysis
