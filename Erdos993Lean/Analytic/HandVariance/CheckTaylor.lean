import Erdos993Lean.Analytic.HandVariance.Taylor
import Erdos993Lean.Analytic.HandVariance.Compute.Checks

/-!
# The exact rational Taylor routines and their real bounds

Source: TWIN v1.8 Appendix N.4, proof of `tgt:thm` (two endpoint
quadratics), and the polygon paragraph after `tgt:lem:poly` (midpoint
upper enclosure). The retained endpoints, derivatives and curvature
bounds are the actual inputs of `Compute.twoEnded` and `polygonLower`.
-/

namespace Erdos993Lean.Analytic.HandVariance

open Real Set Compute

/-- Source: `tgt:thm`; the rational checker polynomial is exactly the real
Taylor polynomial, including its curvature normalization. -/
theorem quadratic_cast (v d m c x : ℚ) :
    (Compute.quadratic v d m c x : ℝ) =
      taylorQuadratic (v : ℝ) (d : ℝ) (m : ℝ) (c : ℝ) (x : ℝ) := by
  unfold Compute.quadratic taylorQuadratic
  push_cast
  ring

/-- Source: `tgt:thm`; the common-curvature difference has exactly the
affine interpolation identity determined by its endpoint differences. -/
theorem taylorQuadratic_difference_endpoints (v0 d0 v1 d1 m c0 c1 a b x : ℝ) :
    (b - a) * (taylorQuadratic v0 d0 m c0 x - taylorQuadratic v1 d1 m c1 x) =
      (b - x) * (taylorQuadratic v0 d0 m c0 a - taylorQuadratic v1 d1 m c1 a) +
      (x - a) * (taylorQuadratic v0 d0 m c0 b - taylorQuadratic v1 d1 m c1 b) := by
  unfold taylorQuadratic
  ring

/-- Source: `tgt:thm`; the exact rational endpoint/crossing routine is a
lower bound on the real Taylor envelope. Equal quadratics, equal endpoint
differences and crossings at an endpoint are included in its weak-sign branch. -/
theorem twoEnded_le (s : Span) (v0 d0 v1 d1 m : ℚ)
    (hm : (m : ℝ) ≤ 0) {x : ℝ} (hx : x ∈ Icc (s.lo : ℝ) (s.hi : ℝ)) :
    (Compute.twoEnded s v0 d0 v1 d1 m : ℝ) ≤
      max (taylorQuadratic (v0 : ℝ) (d0 : ℝ) (m : ℝ) (s.lo : ℝ) x)
        (taylorQuadratic (v1 : ℝ) (d1 : ℝ) (m : ℝ) (s.hi : ℝ) x) := by
  let q0 : ℚ → ℚ := Compute.quadratic v0 d0 m s.lo
  let q1 : ℚ → ℚ := Compute.quadratic v1 d1 m s.hi
  let a : ℝ := s.lo
  let b : ℝ := s.hi
  let Q0 : ℝ → ℝ := taylorQuadratic (v0 : ℝ) (d0 : ℝ) (m : ℝ) a
  let Q1 : ℝ → ℝ := taylorQuadratic (v1 : ℝ) (d1 : ℝ) (m : ℝ) b
  let e0 : ℚ := q0 s.lo - q1 s.lo
  let e1 : ℚ := q0 s.hi - q1 s.hi
  let edge : ℚ := min (max (q0 s.lo) (q1 s.lo)) (max (q0 s.hi) (q1 s.hi))
  let edgeR : ℝ := min (max (Q0 a) (Q1 a)) (max (Q0 b) (Q1 b))
  let crossing : ℚ := s.lo + (s.hi - s.lo) * e0 / (e0 - e1)
  let cond : Prop := (e0 != e1 && decide ((e0 < 0 ∧ 0 < e1) ∨ (e1 < 0 ∧ 0 < e0))) = true
  have hq0 (z : ℚ) : (q0 z : ℝ) = Q0 (z : ℝ) := quadratic_cast v0 d0 m s.lo z
  have hq1 (z : ℚ) : (q1 z : ℝ) = Q1 (z : ℝ) := quadratic_cast v1 d1 m s.hi z
  have he0 : (e0 : ℝ) = Q0 a - Q1 a := by
    dsimp [e0]
    rw [Rat.cast_sub, hq0, hq1]
  have he1 : (e1 : ℝ) = Q0 b - Q1 b := by
    dsimp [e1]
    rw [Rat.cast_sub, hq0, hq1]
  have hedge : (edge : ℝ) = edgeR := by
    dsimp [edge, edgeR]
    rw [Rat.cast_min, Rat.cast_max, Rat.cast_max, hq0, hq1, hq0, hq1]
  have hcrossing : (crossing : ℝ) = a + (b - a) * (e0 : ℝ) / ((e0 : ℝ) - (e1 : ℝ)) := by
    dsimp [crossing, a, b]
    push_cast
    rfl
  have hformula : Compute.twoEnded s v0 d0 v1 d1 m =
      if cond then min edge (max (q0 crossing) (q1 crossing)) else edge := by rfl
  have hab : a ≤ b := hx.1.trans hx.2
  change (Compute.twoEnded s v0 d0 v1 d1 m : ℝ) ≤ max (Q0 x) (Q1 x)
  by_cases hc : cond
  · have hguard : e0 ≠ e1 ∧ ((e0 < 0 ∧ 0 < e1) ∨ (e1 < 0 ∧ 0 < e0)) := by
      simpa only [cond, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] using hc
    have hden : (e0 : ℝ) - (e1 : ℝ) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr hguard.1
    rw [hformula, if_pos hc, Rat.cast_min, Rat.cast_max, hedge, hq0, hq1]
    apply max_taylorQuadratic_lower_of_checks hm
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact (min_le_left _ _).trans (min_le_right _ _)
    · intro y hy heq
      change Q0 y = Q1 y at heq
      change min edgeR (max (Q0 (crossing : ℝ)) (Q1 (crossing : ℝ))) ≤ Q0 y
      have hid := taylorQuadratic_difference_endpoints
        (v0 : ℝ) (d0 : ℝ) (v1 : ℝ) (d1 : ℝ) (m : ℝ) a b a b y
      change (b - a) * (Q0 y - Q1 y) =
        (b - y) * (Q0 a - Q1 a) + (y - a) * (Q0 b - Q1 b) at hid
      rw [heq, sub_self, mul_zero, ← he0, ← he1] at hid
      have hlin : (y - a) * ((e0 : ℝ) - (e1 : ℝ)) = (b - a) * (e0 : ℝ) := by
        nlinarith
      have hdiv : y - a = (b - a) * (e0 : ℝ) / ((e0 : ℝ) - (e1 : ℝ)) :=
        (eq_div_iff hden).mpr hlin
      have hycross : y = (crossing : ℝ) := by rw [hcrossing]; linarith
      rw [← hycross, heq, max_self]
      exact min_le_right edgeR (Q1 y)
    · exact hx
  · have hnoFlip : ¬((e0 < 0 ∧ 0 < e1) ∨ (e1 < 0 ∧ 0 < e0)) := by
      intro hf
      apply hc
      simp only [cond, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq]
      refine ⟨?_, hf⟩
      intro heq
      rcases hf with hf | hf <;> linarith [hf.1, hf.2]
    have hsignQ : (0 ≤ e0 ∧ 0 ≤ e1) ∨ (e0 ≤ 0 ∧ e1 ≤ 0) := by
      by_cases h0 : 0 ≤ e0
      · by_cases h1 : 0 ≤ e1
        · exact Or.inl ⟨h0, h1⟩
        · refine Or.inr ⟨?_, (lt_of_not_ge h1).le⟩
          by_contra h
          exact hnoFlip (Or.inr ⟨lt_of_not_ge h1, lt_of_not_ge h⟩)
      · refine Or.inr ⟨(lt_of_not_ge h0).le, ?_⟩
        by_contra h
        exact hnoFlip (Or.inl ⟨lt_of_not_ge h0, lt_of_not_ge h⟩)
    have hsign : (0 ≤ (e0 : ℝ) ∧ 0 ≤ (e1 : ℝ)) ∨
        ((e0 : ℝ) ≤ 0 ∧ (e1 : ℝ) ≤ 0) := by exact_mod_cast hsignQ
    rw [hformula, if_neg hc, hedge]
    apply max_taylorQuadratic_lower_of_checks hm
    · exact min_le_left _ _
    · exact min_le_right _ _
    · intro y hy heq
      change Q0 y = Q1 y at heq
      rcases hsign with hp | hn
      · have h0 : Q1 a ≤ Q0 a := by linarith [he0, hp.1]
        have h1 : Q1 b ≤ Q0 b := by linarith [he1, hp.2]
        change edgeR ≤ Q0 y
        dsimp [edgeR]
        rw [max_eq_left h0, max_eq_left h1]
        exact (concaveOn_taylorQuadratic (convex_Icc a b)
          (v0 : ℝ) (d0 : ℝ) (m : ℝ) a hm).min_le_of_mem_Icc
          (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hy
      · have h0 : Q0 a ≤ Q1 a := by linarith [he0, hn.1]
        have h1 : Q0 b ≤ Q1 b := by linarith [he1, hn.2]
        change edgeR ≤ Q0 y
        rw [heq]
        dsimp [edgeR]
        rw [max_eq_right h0, max_eq_right h1]
        exact (concaveOn_taylorQuadratic (convex_Icc a b)
          (v1 : ℝ) (d1 : ℝ) (m : ℝ) b hm).min_le_of_mem_Icc
          (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hy
    · exact hx

/-- Source: the midpoint recipes of `tgt:thm` and after `tgt:lem:poly`;
the maximum of the signed slope enclosures bounds its absolute value. -/
theorem abs_le_max_of_enclosure {v lo hi : ℝ} (hl : lo ≤ v) (hh : v ≤ hi) :
    |v| ≤ max (-lo) hi := by
  apply abs_le.mpr
  constructor <;> linarith [le_max_left (-lo) hi, le_max_right (-lo) hi]

/-- Source: the midpoint upper recipe after `tgt:lem:poly`, in exactly
the `max(-dLo,dHi)` slope form of `Compute.polygonLower`. -/
theorem midpoint_taylor_upper_enclosure
    {f f' f'' : ℝ → ℝ} {a b c x M value dLo dHi radius : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hff : ∀ t ∈ interior (Icc a b), HasDerivAt f' (f'' t) t)
    (hcurv : ∀ t ∈ interior (Icc a b), f'' t ≤ M) (hM : 0 ≤ M)
    (hc : c ∈ Icc a b) (hx : x ∈ Icc a b) (hdist : |x - c| ≤ radius)
    (hvalue : f c ≤ value) (hdLo : dLo ≤ f' c) (hdHi : f' c ≤ dHi) :
    f x ≤ value + max (-dLo) dHi * radius + M * radius ^ 2 / 2 := by
  have ht := taylor_upper hf hff hcurv hc hx
  have hslope := abs_le_max_of_enclosure hdLo hdHi
  have hbound : 0 ≤ max (-dLo) dHi := (abs_nonneg (f' c)).trans hslope
  have hradius : 0 ≤ radius := (abs_nonneg (x - c)).trans hdist
  have hprod := mul_le_mul hslope hdist (abs_nonneg (x - c)) hbound
  have hlin : f' c * (x - c) ≤ max (-dLo) dHi * radius := by
    have h := le_abs_self (f' c * (x - c))
    rw [abs_mul] at h
    exact h.trans hprod
  have hsq : (x - c) ^ 2 ≤ radius ^ 2 := by
    nlinarith [sq_abs (x - c), mul_nonneg (sub_nonneg.mpr hdist)
      (show 0 ≤ radius + |x - c| by positivity)]
  have hquad := mul_le_mul_of_nonneg_left hsq hM
  unfold taylorQuadratic at ht
  nlinarith

/-- Source: all midpoint recipes; the actual rational span supplies the
center membership and the radius inequality used by the Taylor theorems. -/
theorem span_midpoint_radius (s : Span) {x : ℝ}
    (hx : x ∈ Icc (s.lo : ℝ) (s.hi : ℝ)) :
    (((s.lo + s.hi) / 2 : ℚ) : ℝ) ∈ Icc (s.lo : ℝ) (s.hi : ℝ) ∧
      |x - (((s.lo + s.hi) / 2 : ℚ) : ℝ)| ≤ (((s.hi - s.lo) / 2 : ℚ) : ℝ) := by
  push_cast
  constructor
  · constructor <;> linarith [hx.1, hx.2]
  · apply abs_le.mpr
    constructor <;> linarith [hx.1, hx.2]

end Erdos993Lean.Analytic.HandVariance

#print axioms Erdos993Lean.Analytic.HandVariance.twoEnded_le
#print axioms Erdos993Lean.Analytic.HandVariance.midpoint_taylor_upper_enclosure
