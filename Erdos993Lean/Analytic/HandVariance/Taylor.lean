import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Hand variance: quadratic Taylor enclosures

Source: `ProofRuns/2026-09-28_analytic_large_n/LEAN/for_tong/TWIN_v1.8/apx_hand.tex`,
Appendix N.4, proof of `tgt:thm`, the endpoint Taylor bounds and CA midpoint bound;
and the child-polygon checks immediately following `tgt:lem:poly`.

Only first and second derivative certificates are used. The underlying function,
the spatial coordinate, and the endpoint derivative enclosure directions are retained.
This module does not supply the numerical derivative enclosures.
-/

namespace Erdos993Lean.Analytic.HandVariance

open Set

/-- The Taylor quadratic used in TWIN v1.8 Appendix N.4, proof of `tgt:thm`
and the child-polygon checks following `tgt:lem:poly`. -/
noncomputable def taylorQuadratic (value slope curvature center x : ℝ) : ℝ :=
  value + slope * (x - center) + curvature / 2 * (x - center) ^ 2

/-- Derivative of the Taylor quadratic in TWIN v1.8 Appendix N.4, proof of
`tgt:thm`. This is polynomial differentiation, with no regularity hypotheses. -/
theorem hasDerivAt_taylorQuadratic (v d m c x : ℝ) :
    HasDerivAt (taylorQuadratic v d m c) (d + m * (x - c)) x := by
  unfold taylorQuadratic
  convert ((hasDerivAt_const x v).add
    (((hasDerivAt_id x).sub_const c).const_mul d)).add
    ((((hasDerivAt_id x).sub_const c).pow 2).const_mul (m / 2)) using 1
  simp only [id_eq]
  ring

/-- Second derivative of the Taylor quadratic in TWIN v1.8 Appendix N.4,
proof of `tgt:thm`. -/
theorem hasDerivAt_taylorQuadratic_derivative (d m c x : ℝ) :
    HasDerivAt (fun t => d + m * (t - c)) m x := by
  simpa only [mul_one] using (((hasDerivAt_id x).sub_const c).const_mul m).const_add d

/-- A quadratic with nonpositive curvature is concave, as used in TWIN v1.8
Appendix N.4, proof of `tgt:thm`, to check endpoint/crossing minima. -/
theorem concaveOn_taylorQuadratic {D : Set ℝ} (hD : Convex ℝ D)
    (v d m c : ℝ) (hm : m ≤ 0) : ConcaveOn ℝ D (taylorQuadratic v d m c) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos hD
    (f' := fun t => d + m * (t - c)) (f'' := fun _ => m)
  · intro x hx
    exact (hasDerivAt_taylorQuadratic v d m c x).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_taylorQuadratic v d m c x).hasDerivWithinAt
  · intro x hx
    exact (hasDerivAt_taylorQuadratic_derivative d m c x).hasDerivWithinAt
  · intro x hx
    exact hm

/-- A quadratic with nonnegative curvature is convex, as used in TWIN v1.8
Appendix N.4, child-polygon checks following `tgt:lem:poly`, to check endpoint maxima. -/
theorem convexOn_taylorQuadratic {D : Set ℝ} (hD : Convex ℝ D)
    (v d m c : ℝ) (hm : 0 ≤ m) : ConvexOn ℝ D (taylorQuadratic v d m c) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg hD
    (f' := fun t => d + m * (t - c)) (f'' := fun _ => m)
  · intro x hx
    exact (hasDerivAt_taylorQuadratic v d m c x).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_taylorQuadratic v d m c x).hasDerivWithinAt
  · intro x hx
    exact (hasDerivAt_taylorQuadratic_derivative d m c x).hasDerivWithinAt
  · intro x hx
    exact hm

private theorem convex_support {D : Set ℝ} {g : ℝ → ℝ} {c x d : ℝ}
    (hg : ConvexOn ℝ D g) (hc : c ∈ D) (hx : x ∈ D)
    (hgc : HasDerivAt g d c) : g c + d * (x - c) ≤ g x := by
  rcases lt_trichotomy c x with hcx | hcx | hxc
  · have h := hg.le_slope_of_hasDerivAt hc hx hcx hgc
    rw [slope_def_field] at h
    have h' := (le_div_iff₀ (sub_pos.mpr hcx)).mp h
    linarith
  · subst x
    simp
  · have h := hg.slope_le_of_hasDerivAt hx hc hxc hgc
    rw [slope_def_field] at h
    have h' := (div_le_iff₀ (sub_pos.mpr hxc)).mp h
    nlinarith

/-- Quadratic Taylor lower bound from an arbitrary point, used in TWIN v1.8
Appendix N.4, proof of `tgt:thm` (AC endpoint bounds and CA midpoint bound).
The certificates require no continuous third derivative or `C∞` hypothesis. -/
theorem taylor_lower
    {f f' f'' : ℝ → ℝ} {a b c x m : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hff : ∀ t ∈ interior (Icc a b), HasDerivAt f' (f'' t) t)
    (hm : ∀ t ∈ interior (Icc a b), m ≤ f'' t)
    (hc : c ∈ Icc a b) (hx : x ∈ Icc a b) :
    taylorQuadratic (f c) (f' c) m c x ≤ f x := by
  let g : ℝ → ℝ := fun t => f t - m / 2 * t ^ 2
  let g' : ℝ → ℝ := fun t => f' t - m * t
  have hg : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t := by
    intro t ht
    dsimp [g, g']
    convert (hf t ht).sub (((hasDerivAt_id t).pow 2).const_mul (m / 2)) using 1
    simp only [id_eq]
    ring
  have hgg : ∀ t ∈ interior (Icc a b), HasDerivAt g' (f'' t - m) t := by
    intro t ht
    dsimp [g']
    simpa only [mul_one] using (hff t ht).sub ((hasDerivAt_id t).const_mul m)
  have hconv : ConvexOn ℝ (Icc a b) g := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc a b)
      (f' := g') (f'' := fun t => f'' t - m)
    · intro t ht
      exact (hg t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hg t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      exact (hgg t ht).hasDerivWithinAt
    · intro t ht
      exact sub_nonneg.mpr (hm t ht)
  have h := convex_support hconv hc hx (hg c hc)
  dsimp [g, g', taylorQuadratic] at h ⊢
  nlinarith

/-- Quadratic Taylor upper bound, used in TWIN v1.8 Appendix N.4,
child-polygon checks following `tgt:lem:poly`. -/
theorem taylor_upper
    {f f' f'' : ℝ → ℝ} {a b c x M : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hff : ∀ t ∈ interior (Icc a b), HasDerivAt f' (f'' t) t)
    (hM : ∀ t ∈ interior (Icc a b), f'' t ≤ M)
    (hc : c ∈ Icc a b) (hx : x ∈ Icc a b) :
    f x ≤ taylorQuadratic (f c) (f' c) M c x := by
  have h := taylor_lower
    (f := fun t => -f t) (f' := fun t => -f' t) (f'' := fun t => -f'' t)
    (m := -M) (fun t ht => (hf t ht).neg) (fun t ht => (hff t ht).neg)
    (fun t ht => neg_le_neg (hM t ht)) hc hx
  dsimp [taylorQuadratic] at h ⊢
  linarith

/-- The endpoint Taylor enclosures in TWIN v1.8 Appendix N.4, proof of
`tgt:thm`, AC check. The slope bound is a lower bound at the left endpoint and
an upper bound at the right endpoint, exactly as in the source. -/
theorem endpoint_taylor_lower
    {f f' f'' : ℝ → ℝ} {a b x m v0 v1 d0 d1 : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hff : ∀ t ∈ interior (Icc a b), HasDerivAt f' (f'' t) t)
    (hm : ∀ t ∈ interior (Icc a b), m ≤ f'' t)
    (hx : x ∈ Icc a b)
    (hv0 : v0 ≤ f a) (hv1 : v1 ≤ f b)
    (hd0 : d0 ≤ f' a) (hd1 : f' b ≤ d1) :
    max (taylorQuadratic v0 d0 m a x) (taylorQuadratic v1 d1 m b x) ≤ f x := by
  have hab : a ≤ b := hx.1.trans hx.2
  have h0 := taylor_lower hf hff hm (left_mem_Icc.mpr hab) hx
  have h1 := taylor_lower hf hff hm (right_mem_Icc.mpr hab) hx
  have hs0 := mul_le_mul_of_nonneg_right hd0 (sub_nonneg.mpr hx.1)
  have hs1 := mul_le_mul_of_nonpos_right hd1 (sub_nonpos.mpr hx.2)
  dsimp [taylorQuadratic] at h0 h1 ⊢
  apply max_le <;> linarith

/-- The CA midpoint bound in TWIN v1.8 Appendix N.4, proof of `tgt:thm`.
The curvature lower bound is nonpositive and `d` bounds the distance to the center. -/
theorem midpoint_taylor_lower
    {f f' f'' : ℝ → ℝ} {a b c x m d : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hff : ∀ t ∈ interior (Icc a b), HasDerivAt f' (f'' t) t)
    (hcurv : ∀ t ∈ interior (Icc a b), m ≤ f'' t)
    (hm : m ≤ 0) (hc : c ∈ Icc a b) (hx : x ∈ Icc a b)
    (hdist : |x - c| ≤ d) :
    f c - |f' c| * d + m / 2 * d ^ 2 ≤ f x := by
  have ht := taylor_lower hf hff hcurv hc hx
  have hlinear := neg_abs_le (f' c * (x - c))
  rw [abs_mul] at hlinear
  have hprod := mul_le_mul_of_nonneg_left hdist (abs_nonneg (f' c))
  have hleft : 0 ≤ d - (x - c) := by linarith [le_abs_self (x - c)]
  have hright : 0 ≤ d + (x - c) := by linarith [neg_abs_le (x - c)]
  have hsq : (x - c) ^ 2 ≤ d ^ 2 := by nlinarith [mul_nonneg hleft hright]
  have hmhalf : m / 2 ≤ 0 := by linarith
  have hquadratic := mul_le_mul_of_nonpos_left hsq hmhalf
  dsimp [taylorQuadratic] at ht
  nlinarith

/-- The enclosure form of the CA midpoint bound in TWIN v1.8 Appendix N.4,
proof of `tgt:thm`: a lower center value and an upper absolute derivative enclosure. -/
theorem midpoint_taylor_lower_enclosure
    {f f' f'' : ℝ → ℝ} {a b c x m d value derivAbs : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hff : ∀ t ∈ interior (Icc a b), HasDerivAt f' (f'' t) t)
    (hcurv : ∀ t ∈ interior (Icc a b), m ≤ f'' t)
    (hm : m ≤ 0) (hc : c ∈ Icc a b) (hx : x ∈ Icc a b)
    (hdist : |x - c| ≤ d) (hvalue : value ≤ f c) (hderiv : |f' c| ≤ derivAbs) :
    value - derivAbs * d + m / 2 * d ^ 2 ≤ f x := by
  have hd : 0 ≤ d := (abs_nonneg (x - c)).trans hdist
  have hprod := mul_le_mul_of_nonneg_right hderiv hd
  have ht := midpoint_taylor_lower hf hff hcurv hm hc hx hdist
  linarith

private theorem left_anchor {f g : ℝ → ℝ} {a b x : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hx : x ∈ Icc a b) (hdom : g x ≤ f x) :
    ∃ p ∈ Icc a x, (p = a ∨ f p = g p) ∧ g p ≤ f p := by
  by_cases ha : g a ≤ f a
  · exact ⟨a, ⟨le_rfl, hx.1⟩, Or.inl rfl, ha⟩
  · have hsub : Icc a x ⊆ Icc a b := Icc_subset_Icc_right hx.2
    have hcont := (hf.sub hg).mono hsub
    have hzero : (0 : ℝ) ∈ Icc (f a - g a) (f x - g x) := by
      constructor <;> linarith [lt_of_not_ge ha]
    rcases intermediate_value_Icc hx.1 hcont hzero with ⟨p, hp, hval⟩
    have heq : f p = g p := by change f p - g p = 0 at hval; linarith
    exact ⟨p, hp, Or.inr heq, heq.ge⟩

private theorem right_anchor {f g : ℝ → ℝ} {a b x : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hx : x ∈ Icc a b) (hdom : g x ≤ f x) :
    ∃ q ∈ Icc x b, (q = b ∨ f q = g q) ∧ g q ≤ f q := by
  by_cases hb : g b ≤ f b
  · exact ⟨b, ⟨hx.2, le_rfl⟩, Or.inl rfl, hb⟩
  · have hsub : Icc x b ⊆ Icc a b := Icc_subset_Icc_left hx.1
    have hcont := (hf.sub hg).mono hsub
    have hzero : (0 : ℝ) ∈ Icc (f b - g b) (f x - g x) := by
      constructor <;> linarith [lt_of_not_ge hb]
    rcases intermediate_value_Icc' hx.2 hcont hzero with ⟨q, hq, hval⟩
    have heq : f q = g q := by change f q - g q = 0 at hval; linarith
    exact ⟨q, hq, Or.inr heq, heq.ge⟩

private theorem candidate_le_of_dominates {f g : ℝ → ℝ} {a b x : ℝ}
    (hf : ConcaveOn ℝ (Icc a b) f)
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hx : x ∈ Icc a b) (hdom : g x ≤ f x) :
    ∃ y ∈ Icc a b, (y = a ∨ y = b ∨ f y = g y) ∧
      max (f y) (g y) ≤ max (f x) (g x) := by
  obtain ⟨p, hp, hpcand, hpdom⟩ := left_anchor hfc hgc hx hdom
  obtain ⟨q, hq, hqcand, hqdom⟩ := right_anchor hfc hgc hx hdom
  have hpall : p ∈ Icc a b := ⟨hp.1, hp.2.trans hx.2⟩
  have hqall : q ∈ Icc a b := ⟨hx.1.trans hq.1, hq.2⟩
  have hmin := hf.min_le_of_mem_Icc hpall hqall (show x ∈ Icc p q from ⟨hp.2, hq.1⟩)
  rcases le_total (f p) (f q) with hpq | hqp
  · refine ⟨p, hpall, ?_, ?_⟩
    · rcases hpcand with hpa | hpeq
      · exact Or.inl hpa
      · exact Or.inr (Or.inr hpeq)
    · simpa only [min_eq_left hpq, max_eq_left hpdom, max_eq_left hdom] using hmin
  · refine ⟨q, hqall, ?_, ?_⟩
    · rcases hqcand with hqb | hqeq
      · exact Or.inr (Or.inl hqb)
      · exact Or.inr (Or.inr hqeq)
    · simpa only [min_eq_right hqp, max_eq_left hqdom, max_eq_left hdom] using hmin

/-- Endpoint/crossing minimum principle used in TWIN v1.8 Appendix N.4,
proof of `tgt:thm`. It holds for any two continuous concave functions, and
therefore for the source's two quadratics with the same nonpositive curvature. -/
theorem exists_endpoint_or_crossing_le
    {f g : ℝ → ℝ} {a b x : ℝ}
    (hf : ConcaveOn ℝ (Icc a b) f) (hg : ConcaveOn ℝ (Icc a b) g)
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hx : x ∈ Icc a b) :
    ∃ y ∈ Icc a b, (y = a ∨ y = b ∨ f y = g y) ∧
      max (f y) (g y) ≤ max (f x) (g x) := by
  rcases le_total (g x) (f x) with hdom | hdom
  · exact candidate_le_of_dominates hf hfc hgc hx hdom
  · obtain ⟨y, hy, hcand, hle⟩ := candidate_le_of_dominates hg hgc hfc hx hdom
    refine ⟨y, hy, ?_, ?_⟩
    · rcases hcand with ha | hb | hcross
      · exact Or.inl ha
      · exact Or.inr (Or.inl hb)
      · exact Or.inr (Or.inr hcross.symm)
    · simpa only [max_comm] using hle

/-- The minimum of the two-quadratic envelope in TWIN v1.8 Appendix N.4,
proof of `tgt:thm`, is attained at an endpoint or crossing. This general
concave-function form also covers equal or parallel quadratics. -/
theorem exists_min_at_endpoint_or_crossing
    {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ConcaveOn ℝ (Icc a b) f) (hg : ConcaveOn ℝ (Icc a b) g)
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b)) :
    ∃ y ∈ Icc a b, (y = a ∨ y = b ∨ f y = g y) ∧
      IsMinOn (fun t => max (f t) (g t)) (Icc a b) y := by
  have hmaxcont : ContinuousOn (fun t => max (f t) (g t)) (Icc a b) := by
    exact hfc.sup hgc
  obtain ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr hab) hmaxcont
  obtain ⟨y, hy, hcand, hle⟩ := exists_endpoint_or_crossing_le hf hg hfc hgc hx
  refine ⟨y, hy, hcand, ?_⟩
  intro z hz
  exact hle.trans (hmin hz)

/-- Endpoint and crossing checks suffice to lower-bound the envelope in
TWIN v1.8 Appendix N.4, proof of `tgt:thm`. -/
theorem max_concave_lower_of_checks
    {f g : ℝ → ℝ} {a b lower : ℝ}
    (hf : ConcaveOn ℝ (Icc a b) f) (hg : ConcaveOn ℝ (Icc a b) g)
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (ha : lower ≤ max (f a) (g a)) (hb : lower ≤ max (f b) (g b))
    (hcross : ∀ y ∈ Icc a b, f y = g y → lower ≤ f y) :
    ∀ x ∈ Icc a b, lower ≤ max (f x) (g x) := by
  intro x hx
  obtain ⟨y, hy, hcand, hle⟩ := exists_endpoint_or_crossing_le hf hg hfc hgc hx
  apply le_trans (b := max (f y) (g y)) ?_ hle
  rcases hcand with hya | hyb | heq
  · simpa only [hya] using ha
  · simpa only [hyb] using hb
  · exact (hcross y hy heq).trans (le_max_left _ _)

/-- The difference of the source's two Taylor quadratics is affine, as stated
in TWIN v1.8 Appendix N.4, proof of `tgt:thm`. -/
theorem taylorQuadratic_sub (v0 v1 d0 d1 m c0 c1 x : ℝ) :
    taylorQuadratic v0 d0 m c0 x - taylorQuadratic v1 d1 m c1 x =
      (v0 - d0 * c0 + m / 2 * c0 ^ 2 - v1 + d1 * c1 - m / 2 * c1 ^ 2) +
      (d0 - d1 - m * c0 + m * c1) * x := by
  unfold taylorQuadratic
  ring

/-- The unique crossing when the affine difference has nonzero slope, for
the finite endpoint/crossing checks in TWIN v1.8 Appendix N.4, proof of `tgt:thm`. -/
theorem taylorQuadratic_eq_iff
    (v0 v1 d0 d1 m c0 c1 x : ℝ)
    (hslope : d0 - d1 - m * c0 + m * c1 ≠ 0) :
    taylorQuadratic v0 d0 m c0 x = taylorQuadratic v1 d1 m c1 x ↔
      x = (v1 - d1 * c1 + m / 2 * c1 ^ 2 - v0 + d0 * c0 - m / 2 * c0 ^ 2) /
        (d0 - d1 - m * c0 + m * c1) := by
  rw [eq_div_iff hslope]
  have hid := taylorQuadratic_sub v0 v1 d0 d1 m c0 c1 x
  constructor <;> intro h <;> nlinarith [hid]

/-- Exact specialization of the endpoint/crossing lower-bound rule to the
Taylor quadratics in TWIN v1.8 Appendix N.4, proof of `tgt:thm`. -/
theorem max_taylorQuadratic_lower_of_checks
    {a b lower v0 v1 d0 d1 m c0 c1 : ℝ} (hm : m ≤ 0)
    (ha : lower ≤ max (taylorQuadratic v0 d0 m c0 a) (taylorQuadratic v1 d1 m c1 a))
    (hb : lower ≤ max (taylorQuadratic v0 d0 m c0 b) (taylorQuadratic v1 d1 m c1 b))
    (hcross : ∀ y ∈ Icc a b,
      taylorQuadratic v0 d0 m c0 y = taylorQuadratic v1 d1 m c1 y →
      lower ≤ taylorQuadratic v0 d0 m c0 y) :
    ∀ x ∈ Icc a b,
      lower ≤ max (taylorQuadratic v0 d0 m c0 x) (taylorQuadratic v1 d1 m c1 x) := by
  exact max_concave_lower_of_checks
    (concaveOn_taylorQuadratic (convex_Icc a b) v0 d0 m c0 hm)
    (concaveOn_taylorQuadratic (convex_Icc a b) v1 d1 m c1 hm)
    (fun x hx => (hasDerivAt_taylorQuadratic v0 d0 m c0 x).continuousAt.continuousWithinAt)
    (fun x hx => (hasDerivAt_taylorQuadratic v1 d1 m c1 x).continuousAt.continuousWithinAt)
    ha hb hcross

/-- The three-check form when the affine difference has a unique crossing,
TWIN v1.8 Appendix N.4, proof of `tgt:thm`. A crossing outside the interval
requires no check. -/
theorem max_taylorQuadratic_lower_of_unique_crossing_checks
    {a b lower v0 v1 d0 d1 m c0 c1 : ℝ} (hm : m ≤ 0)
    (hslope : d0 - d1 - m * c0 + m * c1 ≠ 0)
    (ha : lower ≤ max (taylorQuadratic v0 d0 m c0 a) (taylorQuadratic v1 d1 m c1 a))
    (hb : lower ≤ max (taylorQuadratic v0 d0 m c0 b) (taylorQuadratic v1 d1 m c1 b))
    (hcross :
      (v1 - d1 * c1 + m / 2 * c1 ^ 2 - v0 + d0 * c0 - m / 2 * c0 ^ 2) /
          (d0 - d1 - m * c0 + m * c1) ∈ Icc a b →
      lower ≤ taylorQuadratic v0 d0 m c0
        ((v1 - d1 * c1 + m / 2 * c1 ^ 2 - v0 + d0 * c0 - m / 2 * c0 ^ 2) /
          (d0 - d1 - m * c0 + m * c1))) :
    ∀ x ∈ Icc a b,
      lower ≤ max (taylorQuadratic v0 d0 m c0 x) (taylorQuadratic v1 d1 m c1 x) := by
  apply max_taylorQuadratic_lower_of_checks hm ha hb
  intro y hy heq
  have hycross := (taylorQuadratic_eq_iff v0 v1 d0 d1 m c0 c1 y hslope).mp heq
  rw [hycross] at hy ⊢
  exact hcross hy

/-- A Taylor upper quadratic with nonnegative curvature reaches its maximum
at an endpoint, as used in TWIN v1.8 Appendix N.4, child-polygon checks
following `tgt:lem:poly`. -/
theorem taylorQuadratic_le_max_endpoints
    {a b x : ℝ} (v d M c : ℝ) (hM : 0 ≤ M) (hx : x ∈ Icc a b) :
    taylorQuadratic v d M c x ≤
      max (taylorQuadratic v d M c a) (taylorQuadratic v d M c b) := by
  have hab := hx.1.trans hx.2
  exact (convexOn_taylorQuadratic (convex_Icc a b) v d M c hM).le_max_of_mem_Icc
    (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hx

/-- Child-polygon upper enclosure from its center and a nonnegative curvature
upper bound, TWIN v1.8 Appendix N.4, after `tgt:lem:poly`. -/
theorem taylor_upper_le_max_endpoints
    {f f' f'' : ℝ → ℝ} {a b c x M : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hff : ∀ t ∈ interior (Icc a b), HasDerivAt f' (f'' t) t)
    (hcurv : ∀ t ∈ interior (Icc a b), f'' t ≤ M)
    (hM : 0 ≤ M) (hc : c ∈ Icc a b) (hx : x ∈ Icc a b) :
    f x ≤ max (taylorQuadratic (f c) (f' c) M c a)
      (taylorQuadratic (f c) (f' c) M c b) := by
  exact (taylor_upper hf hff hcurv hc hx).trans
    (taylorQuadratic_le_max_endpoints (f c) (f' c) M c hM hx)

/-- The center-enclosure form of the child-polygon bound in TWIN v1.8
Appendix N.4, following `tgt:lem:poly`. For the upper bound, the left endpoint
uses the lower center-slope enclosure and the right endpoint uses its upper enclosure. -/
theorem taylor_upper_endpoint_enclosure
    {f f' f'' : ℝ → ℝ} {a b c x M value dLo dHi : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hff : ∀ t ∈ interior (Icc a b), HasDerivAt f' (f'' t) t)
    (hcurv : ∀ t ∈ interior (Icc a b), f'' t ≤ M)
    (hM : 0 ≤ M) (hc : c ∈ Icc a b) (hx : x ∈ Icc a b)
    (hvalue : f c ≤ value) (hdLo : dLo ≤ f' c) (hdHi : f' c ≤ dHi) :
    f x ≤ max (taylorQuadratic value dLo M c a) (taylorQuadratic value dHi M c b) := by
  have ht := taylor_upper_le_max_endpoints hf hff hcurv hM hc hx
  have hl := mul_le_mul_of_nonpos_right hdLo (sub_nonpos.mpr hc.1)
  have hr := mul_le_mul_of_nonneg_right hdHi (sub_nonneg.mpr hc.2)
  apply ht.trans
  apply max_le_max <;> dsimp [taylorQuadratic] <;> linarith

end Erdos993Lean.Analytic.HandVariance

#print axioms Erdos993Lean.Analytic.HandVariance.endpoint_taylor_lower
#print axioms Erdos993Lean.Analytic.HandVariance.midpoint_taylor_lower
#print axioms Erdos993Lean.Analytic.HandVariance.midpoint_taylor_lower_enclosure
#print axioms Erdos993Lean.Analytic.HandVariance.exists_min_at_endpoint_or_crossing
#print axioms Erdos993Lean.Analytic.HandVariance.max_taylorQuadratic_lower_of_checks
#print axioms Erdos993Lean.Analytic.HandVariance.taylor_upper_le_max_endpoints
#print axioms Erdos993Lean.Analytic.HandVariance.taylor_upper_endpoint_enclosure
