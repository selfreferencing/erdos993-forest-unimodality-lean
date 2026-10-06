import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

/-!
# Paper v2.2: quadratic suprema and remainder algebra

Source: Lemma 4.11's first sentence and the algebra in Proposition 4.6 and
Lemma 4.7. The exact supremum is attained at `a/(2*b)`; the bounded form keeps
both signs of `b`. The helpers below are identities/inequalities over supplied
real quantities. They construct no forest state and add no analytical premise
to a source-bound theorem. The parent owns Lean verification.
-/

namespace Erdos993Lean.Analytic.V22.Analysis

open Set

def quadraticValues (a b : ℝ) : Set ℝ :=
  (fun nu : ℝ => a * nu - b * nu ^ 2) '' Ici 0

def boundedQuadraticValues (a b nuM : ℝ) : Set ℝ :=
  (fun nu : ℝ => a * nu - b * nu ^ 2) '' Icc 0 nuM

/-- Completing the square, with the exact source denominator. -/
theorem quadratic_complete_square (a b nu : ℝ) (hb : b ≠ 0) :
    a * nu - b * nu ^ 2 = a ^ 2 / (4 * b) - b * (nu - a / (2 * b)) ^ 2 := by
  field_simp [hb]
  ring

theorem quadratic_le_vertex {a b nu : ℝ} (hb : 0 < b) :
    a * nu - b * nu ^ 2 ≤ a ^ 2 / (4 * b) := by
  rw [quadratic_complete_square a b nu hb.ne']
  exact sub_le_self _ (mul_nonneg hb.le (sq_nonneg _))

theorem quadratic_vertex_value {a b : ℝ} (hb : 0 < b) :
    a * (a / (2 * b)) - b * (a / (2 * b)) ^ 2 = a ^ 2 / (4 * b) := by
  rw [quadratic_complete_square a b (a / (2 * b)) hb.ne']
  simp

/-- Source Lemma 4.11: exact maximum, including an explicit attaining offset. -/
theorem quadratic_isGreatest {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    IsGreatest (quadraticValues a b) (a ^ 2 / (4 * b)) := by
  constructor
  · refine ⟨a / (2 * b), ?_, quadratic_vertex_value hb⟩
    exact div_nonneg ha (by positivity)
  · rintro value ⟨nu, _, rfl⟩
    exact quadratic_le_vertex hb

theorem quadratic_sup_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    sSup (quadraticValues a b) = a ^ 2 / (4 * b) :=
  (quadratic_isGreatest ha hb).csSup_eq

/-- The bounded positive-coefficient case retains both independent bounds. -/
theorem quadratic_le_bounded_pos {a b nu nuM : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hnu : 0 ≤ nu) (hcap : nu ≤ nuM) :
    a * nu - b * nu ^ 2 ≤ min (a ^ 2 / (4 * b)) (a * nuM) := by
  apply le_min (quadratic_le_vertex hb)
  exact (sub_le_self _ (mul_nonneg hb.le (sq_nonneg nu))).trans
    (mul_le_mul_of_nonneg_left hcap ha)

/-- The bounded nonpositive-coefficient case is attained at the right endpoint. -/
theorem quadratic_le_bounded_nonpos {a b nu nuM : ℝ} (ha : 0 ≤ a) (hb : b ≤ 0)
    (hnu : 0 ≤ nu) (hcap : nu ≤ nuM) :
    a * nu - b * nu ^ 2 ≤ a * nuM - b * nuM ^ 2 := by
  have hsq : nu ^ 2 ≤ nuM ^ 2 := (sq_le_sq₀ hnu (hnu.trans hcap)).2 hcap
  have hlin := mul_le_mul_of_nonneg_left hcap ha
  have hquad := mul_le_mul_of_nonneg_left hsq (neg_nonneg.mpr hb)
  nlinarith

theorem quadratic_bounded_sup_le_pos {a b nuM : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hcap : 0 ≤ nuM) :
    sSup (boundedQuadraticValues a b nuM) ≤ min (a ^ 2 / (4 * b)) (a * nuM) := by
  apply csSup_le (show (boundedQuadraticValues a b nuM).Nonempty from
    ⟨0, 0, ⟨le_rfl, hcap⟩, by ring⟩)
  rintro value ⟨nu, hnu, rfl⟩
  exact quadratic_le_bounded_pos ha hb hnu.1 hnu.2

theorem quadratic_bounded_sup_eq_nonpos {a b nuM : ℝ} (ha : 0 ≤ a) (hb : b ≤ 0)
    (hcap : 0 ≤ nuM) :
    sSup (boundedQuadraticValues a b nuM) = a * nuM - b * nuM ^ 2 := by
  apply IsGreatest.csSup_eq
  constructor
  · exact ⟨nuM, ⟨hcap, le_rfl⟩, rfl⟩
  · rintro value ⟨nu, hnu, rfl⟩
    exact quadratic_le_bounded_nonpos ha hb hnu.1 hnu.2

/-- The branch expression used by the bounded block remainder formulas. -/
noncomputable def quadraticBound (a b nuM : ℝ) : ℝ :=
  if 0 < b then min (a ^ 2 / (4 * b)) (a * nuM) else a * nuM - b * nuM ^ 2

theorem quadraticBound_nonneg {a b nuM : ℝ} (ha : 0 ≤ a) (hcap : 0 ≤ nuM) :
    0 ≤ quadraticBound a b nuM := by
  unfold quadraticBound
  split_ifs with hb
  · exact le_min (div_nonneg (sq_nonneg a) (by positivity)) (mul_nonneg ha hcap)
  · exact sub_nonneg.mpr ((mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hb)
      (sq_nonneg nuM)).trans (mul_nonneg ha hcap))

theorem quadratic_positivePart_le_vertex {a b nu : ℝ} (hb : 0 < b) :
    max (a * nu - b * nu ^ 2) 0 ≤ a ^ 2 / (4 * b) :=
  max_le (quadratic_le_vertex hb) (div_nonneg (sq_nonneg a) (by positivity))

theorem quadratic_positivePart_le_bounded {a b nu nuM : ℝ} (ha : 0 ≤ a)
    (hnu : 0 ≤ nu) (hcap : nu ≤ nuM) :
    max (a * nu - b * nu ^ 2) 0 ≤ quadraticBound a b nuM := by
  apply max_le _ (quadraticBound_nonneg ha (hnu.trans hcap))
  unfold quadraticBound
  split_ifs with hb
  · exact quadratic_le_bounded_pos ha hb hnu hcap
  · exact quadratic_le_bounded_nonpos ha (le_of_not_gt hb) hnu hcap

/-- Proposition 4.6: dividing a possible loss by `1+s>=1` cannot worsen its
positive-part bound. The numerator is allowed either sign. -/
theorem lowerRemainder_div_bound (A B s : ℝ) (hs : 0 ≤ s) :
    -max (A - B) 0 ≤ (B - A) / (1 + s) := by
  apply (le_div_iff₀ (show 0 < 1 + s by linarith)).2
  have hmax : 0 ≤ max (A - B) 0 := le_max_right _ _
  have hnum : A - B ≤ max (A - B) 0 := le_max_left _ _
  nlinarith [mul_nonneg hmax hs]

/-- Lemma 4.7: retain the separate bonus payment in each loss bracket. -/
theorem upperRemainder_two_bonus (T A B C g : ℝ) (hg : 0 ≤ g) :
    T - max (A - B) 0 - g * max (C - B) 0 ≤ T - A + B - g * (C - B) := by
  have hA : A - B ≤ max (A - B) 0 := le_max_left _ _
  have hC : C - B ≤ max (C - B) 0 := le_max_left _ _
  have hCg := mul_le_mul_of_nonneg_left hC hg
  linarith

/-- Generic lower-remainder expansion used before Lemma 4.11's supremum.
`C=N+1`, `d=N-1`, and `A,B` are the two linearised coefficients. -/
theorem lowerRemainder_quadratic_envelope
    {C d A B sigma0 nu nuM e sigma bonus ebar : ℝ}
    (hC : 0 < C) (hd : 0 ≤ d) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hsigma0 : 0 ≤ sigma0) (hnu : 0 ≤ nu) (hcap : nu ≤ nuM)
    (he : 0 ≤ e) (hCe : C * e ≤ A * nu + B * nu ^ 2)
    (hsigma : sigma ≤ sigma0 + e) (hbonus : d * nu ^ 2 ≤ bonus)
    (hebar : e ≤ ebar) (hebar1 : ebar ≤ 1) :
    max (2 * C * e * sigma - bonus * (1 - e)) 0 ≤
      max (2 * sigma0 * A * nu -
        (d * (1 - ebar) - 2 * sigma0 * B - 2 * (A + B * nuM) ^ 2 / C) * nu ^ 2) 0 := by
  have hnuM : 0 ≤ nuM := hnu.trans hcap
  have hCen : 0 ≤ C * e := mul_nonneg hC.le he
  have hK : 0 ≤ A + B * nuM := add_nonneg hA (mul_nonneg hB hnuM)
  have hcapPoly : A * nu + B * nu ^ 2 ≤ (A + B * nuM) * nu := by
    nlinarith [mul_nonneg (mul_nonneg hB hnu) (sub_nonneg.mpr hcap)]
  have hCecap := hCe.trans hcapPoly
  have hCesq : (C * e) ^ 2 ≤ ((A + B * nuM) * nu) ^ 2 :=
    (sq_le_sq₀ hCen (mul_nonneg hK hnu)).2 hCecap
  have hesq : C * e ^ 2 ≤ (A + B * nuM) ^ 2 * nu ^ 2 / C := by
    apply (le_div_iff₀ hC).2
    nlinarith [hCesq]
  have hesigma := mul_le_mul_of_nonneg_left hsigma hCen
  have hlinear := mul_le_mul_of_nonneg_left hCe hsigma0
  have hone : 0 ≤ 1 - e := by linarith
  have hbonus1 := mul_le_mul_of_nonneg_right hbonus hone
  have hbonus2 := mul_le_mul_of_nonneg_left (show 1 - ebar ≤ 1 - e by linarith)
    (mul_nonneg hd (sq_nonneg nu))
  have hbonusPay := hbonus2.trans hbonus1
  apply max_le_max _ le_rfl
  simp only [div_eq_mul_inv] at hesq ⊢
  nlinarith [hesigma, hlinear, hesq, hbonusPay]

/-- Close the lower quadratic envelope at its exact all-offset maximum. -/
theorem lowerRemainder_closed_quadratic {D sigma0 A beta nu : ℝ}
    (hbeta : 0 < beta)
    (hD : D ≤ max (2 * sigma0 * A * nu - beta * nu ^ 2) 0) :
    D ≤ (sigma0 * A) ^ 2 / beta := by
  have hq := quadratic_positivePart_le_vertex (a := 2 * sigma0 * A) (nu := nu) hbeta
  have heq : (2 * sigma0 * A) ^ 2 / (4 * beta) = (sigma0 * A) ^ 2 / beta := by
    field_simp [hbeta.ne']
    ring
  rw [heq] at hq
  exact hD.trans hq

/-- Bound the two upper loss brackets separately before adding their slope
factor. The bounded variant below keeps either sign of each coefficient. -/
theorem upperRemainder_closed_quadratics
    {loss1 loss2 a1 b1 a2 b2 g nu : ℝ} (hg : 0 ≤ g)
    (hb1 : 0 < b1) (hb2 : 0 < b2)
    (h1 : loss1 ≤ a1 * nu - b1 * nu ^ 2)
    (h2 : loss2 ≤ a2 * nu - b2 * nu ^ 2) :
    max loss1 0 + g * max loss2 0 ≤ a1 ^ 2 / (4 * b1) + g * (a2 ^ 2 / (4 * b2)) := by
  have hq1 := (max_le_max h1 le_rfl).trans (quadratic_positivePart_le_vertex hb1)
  have hq2 := (max_le_max h2 le_rfl).trans (quadratic_positivePart_le_vertex hb2)
  exact add_le_add hq1 (mul_le_mul_of_nonneg_left hq2 hg)

theorem upperRemainder_bounded_quadratics
    {loss1 loss2 a1 b1 a2 b2 g nu nuM : ℝ} (hg : 0 ≤ g)
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (hnu : 0 ≤ nu) (hcap : nu ≤ nuM)
    (h1 : loss1 ≤ a1 * nu - b1 * nu ^ 2)
    (h2 : loss2 ≤ a2 * nu - b2 * nu ^ 2) :
    max loss1 0 + g * max loss2 0 ≤ quadraticBound a1 b1 nuM +
      g * quadraticBound a2 b2 nuM := by
  have hq1 := (max_le_max h1 le_rfl).trans (quadratic_positivePart_le_bounded ha1 hnu hcap)
  have hq2 := (max_le_max h2 le_rfl).trans (quadratic_positivePart_le_bounded ha2 hnu hcap)
  exact add_le_add hq1 (mul_le_mul_of_nonneg_left hq2 hg)

end Erdos993Lean.Analytic.V22.Analysis
