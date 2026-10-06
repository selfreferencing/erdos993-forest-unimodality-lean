import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

/-!
# Hand variance: signed mean-value transport

Source: `ProofRuns/2026-09-28_analytic_large_n/LEAN/for_tong/TWIN_v1.8/apx_hand.tex`,
Appendix N.4, Lemma `tgt:lem:mvt` (the transport inequality, lines 719–728).

This module proves the pointwise transport argument. The function and fixed spatial
coordinate are retained throughout; no derivative enclosure or forest bound is asserted
here. The signed maximum charges only a derivative direction which can lower the function.
-/

namespace Erdos993Lean.Analytic.HandVariance

open Set

/-- The real-coordinate form of TWIN v1.8 Appendix N.4, Lemma `tgt:lem:mvt`.
Use `μ = log λ`; `a`, `b`, and `c` are the two log endpoints and the log center.
The hypotheses are weaker than continuous differentiability: continuity on the
closed interval and differentiability on its interior suffice. -/
theorem transport
    {f : ℝ → ℝ} {a b c x lower dMinus dPlus deltaMinus deltaPlus : ℝ}
    (hc : c ∈ Icc a b) (hx : x ∈ Icc a b)
    (hdeltaMinus : c - a ≤ deltaMinus) (hdeltaPlus : b - c ≤ deltaPlus)
    (hcont : ContinuousOn f (Icc a b))
    (hdiff : DifferentiableOn ℝ f (interior (Icc a b)))
    (hderivMinus : ∀ t ∈ interior (Icc a b), dMinus ≤ deriv f t)
    (hderivPlus : ∀ t ∈ interior (Icc a b), deriv f t ≤ dPlus)
    (hcenter : lower ≤ f c) :
    lower - max (deltaPlus * max 0 (-dMinus)) (deltaMinus * max 0 dPlus) ≤ f x := by
  rcases le_total c x with hcx | hxc
  · have hmvt := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
      hcont hdiff hderivMinus c hc x hx hcx
    have hwidth : x - c ≤ deltaPlus := by linarith [hx.2]
    have hd : -(max 0 (-dMinus)) ≤ dMinus := by
      linarith [le_max_right (0 : ℝ) (-dMinus)]
    have hprod := mul_le_mul_of_nonneg_right hd (sub_nonneg.mpr hcx)
    have hwidthProd := mul_le_mul_of_nonneg_left hwidth (le_max_left (0 : ℝ) (-dMinus))
    have hmax := le_max_left (deltaPlus * max 0 (-dMinus)) (deltaMinus * max 0 dPlus)
    nlinarith
  · have hmvt := (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le
      hcont hdiff hderivPlus x hx c hc hxc
    have hwidth : c - x ≤ deltaMinus := by linarith [hx.1]
    have hprod := mul_le_mul_of_nonneg_right
      (le_max_right (0 : ℝ) dPlus) (sub_nonneg.mpr hxc)
    have hwidthProd := mul_le_mul_of_nonneg_left hwidth (le_max_left (0 : ℝ) dPlus)
    have hmax := le_max_right (deltaPlus * max 0 (-dMinus)) (deltaMinus * max 0 dPlus)
    nlinarith

/-- TWIN v1.8 Appendix N.4, Lemma `tgt:lem:mvt`, at one fixed spatial point.
The derivative is taken in `μ = log λ`, represented by `F ∘ exp`. Activities are
positive, as in the variance segments of that appendix. -/
theorem transport_log_activity
    {F : ℝ → ℝ} {lo hi center lam lower dMinus dPlus deltaMinus deltaPlus : ℝ}
    (hlo : 0 < lo) (hc : center ∈ Icc lo hi) (hlam : lam ∈ Icc lo hi)
    (hdeltaMinus : Real.log (center / lo) ≤ deltaMinus)
    (hdeltaPlus : Real.log (hi / center) ≤ deltaPlus)
    (hcont : ContinuousOn (fun μ => F (Real.exp μ)) (Icc (Real.log lo) (Real.log hi)))
    (hdiff : DifferentiableOn ℝ (fun μ => F (Real.exp μ))
      (interior (Icc (Real.log lo) (Real.log hi))))
    (hderivMinus : ∀ μ ∈ interior (Icc (Real.log lo) (Real.log hi)),
      dMinus ≤ deriv (fun t => F (Real.exp t)) μ)
    (hderivPlus : ∀ μ ∈ interior (Icc (Real.log lo) (Real.log hi)),
      deriv (fun t => F (Real.exp t)) μ ≤ dPlus)
    (hcenter : lower ≤ F center) :
    lower - max (deltaPlus * max 0 (-dMinus)) (deltaMinus * max 0 dPlus) ≤ F lam := by
  have hcpos : 0 < center := lt_of_lt_of_le hlo hc.1
  have hlampos : 0 < lam := lt_of_lt_of_le hlo hlam.1
  have hhipos : 0 < hi := lt_of_lt_of_le hcpos hc.2
  have hclog : Real.log center ∈ Icc (Real.log lo) (Real.log hi) :=
    ⟨Real.log_le_log hlo hc.1, Real.log_le_log hcpos hc.2⟩
  have hlamlog : Real.log lam ∈ Icc (Real.log lo) (Real.log hi) :=
    ⟨Real.log_le_log hlo hlam.1, Real.log_le_log hlampos hlam.2⟩
  have hminus : Real.log center - Real.log lo ≤ deltaMinus := by
    simpa only [Real.log_div hcpos.ne' hlo.ne'] using hdeltaMinus
  have hplus : Real.log hi - Real.log center ≤ deltaPlus := by
    simpa only [Real.log_div hhipos.ne' hcpos.ne'] using hdeltaPlus
  have hcenter' : lower ≤ (fun μ => F (Real.exp μ)) (Real.log center) := by
    simpa only [Real.exp_log hcpos] using hcenter
  have h := transport hclog hlamlog hminus hplus hcont hdiff hderivMinus hderivPlus hcenter'
  simpa only [Real.exp_log hlampos] using h

/-- TWIN v1.8 Appendix N.4, Lemma `tgt:lem:mvt`, on the full spatial/activity
box. This is the stated source inequality, pointwise in `Y` and `λ`; its
derivative hypotheses retain the same function at the same `Y`. -/
theorem transport_log_box
    {F : ℝ → ℝ → ℝ} {Y0 Y1 lo hi center lower dMinus dPlus deltaMinus deltaPlus : ℝ}
    (hlo : 0 < lo) (hc : center ∈ Icc lo hi)
    (hdeltaMinus : Real.log (center / lo) ≤ deltaMinus)
    (hdeltaPlus : Real.log (hi / center) ≤ deltaPlus)
    (hcont : ∀ Y ∈ Icc Y0 Y1,
      ContinuousOn (fun μ => F Y (Real.exp μ)) (Icc (Real.log lo) (Real.log hi)))
    (hdiff : ∀ Y ∈ Icc Y0 Y1,
      DifferentiableOn ℝ (fun μ => F Y (Real.exp μ))
        (interior (Icc (Real.log lo) (Real.log hi))))
    (hderivMinus : ∀ Y ∈ Icc Y0 Y1, ∀ μ ∈ interior (Icc (Real.log lo) (Real.log hi)),
      dMinus ≤ deriv (fun t => F Y (Real.exp t)) μ)
    (hderivPlus : ∀ Y ∈ Icc Y0 Y1, ∀ μ ∈ interior (Icc (Real.log lo) (Real.log hi)),
      deriv (fun t => F Y (Real.exp t)) μ ≤ dPlus)
    (hcenter : ∀ Y ∈ Icc Y0 Y1, lower ≤ F Y center) :
    ∀ Y ∈ Icc Y0 Y1, ∀ lam ∈ Icc lo hi,
      lower - max (deltaPlus * max 0 (-dMinus)) (deltaMinus * max 0 dPlus) ≤ F Y lam := by
  intro Y hY lam hlam
  exact transport_log_activity hlo hc hlam hdeltaMinus hdeltaPlus
    (hcont Y hY) (hdiff Y hY) (hderivMinus Y hY) (hderivPlus Y hY) (hcenter Y hY)

end Erdos993Lean.Analytic.HandVariance

#print axioms Erdos993Lean.Analytic.HandVariance.transport
#print axioms Erdos993Lean.Analytic.HandVariance.transport_log_activity
#print axioms Erdos993Lean.Analytic.HandVariance.transport_log_box
