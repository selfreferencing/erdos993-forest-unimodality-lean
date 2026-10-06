import Erdos993Lean.Analytic.HandVariance.CheckTaylor
import Erdos993Lean.Analytic.HandVariance.Transport

/-!
# Taylor and activity-transport consumers of rational bounds

Source: TWIN v1.8 Appendix N.4, proof of `tgt:thm` and Lemma
`tgt:lem:mvt`. These lemmas retain the same real function, spatial point,
and signed derivative on both stages of the finite check.
-/
namespace Erdos993Lean.Analytic.HandVariance.Compute
open Real Set

/-- Source: `tgt:thm`, the endpoint Taylor bound followed by signed transport.
The hypotheses are real enclosures supplied by the expression checker. -/
theorem endpointTransport_lower
    (spatial activity : Span) (center v0 d0 v1 d1 curv dlo dhi dm dp : Rat)
    (F FY FYY FM : ℝ → ℝ → ℝ)
    (hlo : 0 < (activity.lo : ℝ))
    (hc : (center : ℝ) ∈ Icc (activity.lo : ℝ) (activity.hi : ℝ))
    (hf : ∀ y ∈ Icc (spatial.lo : ℝ) (spatial.hi : ℝ),
      HasDerivAt (fun t => F (center : ℝ) t) (FY center y) y)
    (hff : ∀ y ∈ interior (Icc (spatial.lo : ℝ) (spatial.hi : ℝ)),
      HasDerivAt (fun t => FY (center : ℝ) t) (FYY center y) y)
    (hcurv : ∀ y ∈ interior (Icc (spatial.lo : ℝ) (spatial.hi : ℝ)),
      (curv : ℝ) ≤ FYY center y)
    (hv0 : (v0 : ℝ) ≤ F center spatial.lo)
    (hd0 : (d0 : ℝ) ≤ FY center spatial.lo)
    (hv1 : (v1 : ℝ) ≤ F center spatial.hi)
    (hd1 : FY center spatial.hi ≤ (d1 : ℝ))
    (hmu : ∀ y ∈ Icc (spatial.lo : ℝ) (spatial.hi : ℝ),
      ∀ mu ∈ Icc (log (activity.lo : ℝ)) (log (activity.hi : ℝ)),
      HasDerivAt (fun t => F (exp t) y) (FM (exp mu) y) mu)
    (hderiv : ∀ y ∈ Icc (spatial.lo : ℝ) (spatial.hi : ℝ),
      ∀ mu ∈ Icc (log (activity.lo : ℝ)) (log (activity.hi : ℝ)),
      (dlo : ℝ) ≤ FM (exp mu) y ∧ FM (exp mu) y ≤ (dhi : ℝ))
    (hdm : log ((center : ℝ)/(activity.lo : ℝ)) ≤ (dm : ℝ))
    (hdp : log ((activity.hi : ℝ)/(center : ℝ)) ≤ (dp : ℝ))
    {lam y : ℝ} (hlam : lam ∈ Icc (activity.lo : ℝ) (activity.hi : ℝ))
    (hy : y ∈ Icc (spatial.lo : ℝ) (spatial.hi : ℝ)) :
    ((twoEnded spatial v0 d0 v1 d1 (min 0 curv) -
      transportLoss dlo dhi dm dp : Rat) : ℝ) ≤ F lam y := by
  have hm : ((min 0 curv : Rat) : ℝ) ≤ 0 := by
    exact_mod_cast min_le_left (0 : Rat) curv
  have hmcurv : ∀ t ∈ interior (Icc (spatial.lo : ℝ) (spatial.hi : ℝ)),
      ((min 0 curv : Rat) : ℝ) ≤ FYY center t := by
    intro t ht
    have hmin : ((min 0 curv : Rat) : ℝ) ≤ (curv : ℝ) := by
      exact_mod_cast min_le_right (0 : Rat) curv
    exact hmin.trans (hcurv t ht)
  have hcenter : (twoEnded spatial v0 d0 v1 d1 (min 0 curv) : ℝ) ≤ F center y := by
    exact (twoEnded_le spatial v0 d0 v1 d1 (min 0 curv) hm hy).trans
      (endpoint_taylor_lower hf hff hmcurv hy hv0 hv1 hd0 hd1)
  have h := transport_log_activity (F := fun l => F l y) hlo hc hlam hdm hdp
    (fun mu hmu' => (hmu y hy mu hmu').continuousAt.continuousWithinAt)
    (fun mu hmu' => (hmu y hy mu (interior_subset hmu')).differentiableAt.differentiableWithinAt)
    (fun mu hmu' => by rw [(hmu y hy mu (interior_subset hmu')).deriv]; exact (hderiv y hy mu (interior_subset hmu')).1)
    (fun mu hmu' => by rw [(hmu y hy mu (interior_subset hmu')).deriv]; exact (hderiv y hy mu (interior_subset hmu')).2)
    hcenter
  simpa only [Rat.cast_sub, transportLoss, Rat.cast_max, Rat.cast_mul,
    Rat.cast_zero, Rat.cast_neg] using h

/-- Source: `tgt:thm`, midpoint CA Taylor bound followed by signed transport. -/
theorem midpointTransport_lower
    (spatial activity : Span) (center value slopeLo slopeHi curv dlo dhi dm dp : Rat)
    (F FY FYY FM : ℝ → ℝ → ℝ)
    (hlo : 0 < (activity.lo : ℝ))
    (hc : (center : ℝ) ∈ Icc (activity.lo : ℝ) (activity.hi : ℝ))
    (hf : ∀ y ∈ Icc (spatial.lo : ℝ) (spatial.hi : ℝ),
      HasDerivAt (fun t => F (center : ℝ) t) (FY center y) y)
    (hff : ∀ y ∈ interior (Icc (spatial.lo : ℝ) (spatial.hi : ℝ)),
      HasDerivAt (fun t => FY (center : ℝ) t) (FYY center y) y)
    (hcurv : ∀ y ∈ interior (Icc (spatial.lo : ℝ) (spatial.hi : ℝ)),
      (curv : ℝ) ≤ FYY center y)
    (hvalue : (value : ℝ) ≤ F center (((spatial.lo+spatial.hi)/2 : Rat) : ℝ))
    (hslope : (slopeLo : ℝ) ≤ FY center (((spatial.lo+spatial.hi)/2 : Rat) : ℝ) ∧
      FY center (((spatial.lo+spatial.hi)/2 : Rat) : ℝ) ≤ (slopeHi : ℝ))
    (hmu : ∀ y ∈ Icc (spatial.lo : ℝ) (spatial.hi : ℝ),
      ∀ mu ∈ Icc (log (activity.lo : ℝ)) (log (activity.hi : ℝ)),
      HasDerivAt (fun t => F (exp t) y) (FM (exp mu) y) mu)
    (hderiv : ∀ y ∈ Icc (spatial.lo : ℝ) (spatial.hi : ℝ),
      ∀ mu ∈ Icc (log (activity.lo : ℝ)) (log (activity.hi : ℝ)),
      (dlo : ℝ) ≤ FM (exp mu) y ∧ FM (exp mu) y ≤ (dhi : ℝ))
    (hdm : log ((center : ℝ)/(activity.lo : ℝ)) ≤ (dm : ℝ))
    (hdp : log ((activity.hi : ℝ)/(center : ℝ)) ≤ (dp : ℝ))
    {lam y : ℝ} (hlam : lam ∈ Icc (activity.lo : ℝ) (activity.hi : ℝ))
    (hy : y ∈ Icc (spatial.lo : ℝ) (spatial.hi : ℝ)) :
    (((value - max (-slopeLo) slopeHi * ((spatial.hi-spatial.lo)/2) +
      min 0 curv * ((spatial.hi-spatial.lo)/2)^2/2) -
      transportLoss dlo dhi dm dp : Rat) : ℝ) ≤ F lam y := by
  let c : ℝ := ((spatial.lo : ℝ)+(spatial.hi : ℝ))/2
  let radius : ℝ := ((spatial.hi : ℝ)-(spatial.lo : ℝ))/2
  have hccast : (((spatial.lo+spatial.hi)/2 : Rat) : ℝ) = c := by
    simp [c]
  have hradius : (((spatial.hi-spatial.lo)/2 : Rat) : ℝ) = radius := by
    simp [radius]
  have hcsp : c ∈ Icc (spatial.lo : ℝ) (spatial.hi : ℝ) := by
    dsimp [c]; constructor <;> linarith [hy.1, hy.2]
  have hdist : |y-c| ≤ radius := by
    rw [abs_le]; dsimp [c,radius]; constructor <;> linarith [hy.1,hy.2]
  have hsabs : |FY center c| ≤ max (-(slopeLo : ℝ)) (slopeHi : ℝ) := by
    rw [abs_le]
    rw [hccast] at hslope
    constructor <;> linarith [hslope.1, hslope.2,
      le_max_left (-(slopeLo : ℝ)) (slopeHi : ℝ),
      le_max_right (-(slopeLo : ℝ)) (slopeHi : ℝ)]
  have hm : ((min 0 curv : Rat) : ℝ) ≤ 0 := by
    exact_mod_cast min_le_left (0 : Rat) curv
  have hmcurv : ∀ t ∈ interior (Icc (spatial.lo : ℝ) (spatial.hi : ℝ)),
      ((min 0 curv : Rat) : ℝ) ≤ FYY center t := by
    intro t ht
    have hmin : ((min 0 curv : Rat) : ℝ) ≤ (curv : ℝ) := by
      exact_mod_cast min_le_right (0 : Rat) curv
    exact hmin.trans (hcurv t ht)
  rw [hccast] at hvalue
  have ht := midpoint_taylor_lower_enclosure hf hff hmcurv hm hcsp hy hdist hvalue hsabs
  have h := transport_log_activity (F := fun l => F l y) hlo hc hlam hdm hdp
    (fun mu hmu' => (hmu y hy mu hmu').continuousAt.continuousWithinAt)
    (fun mu hmu' => (hmu y hy mu (interior_subset hmu')).differentiableAt.differentiableWithinAt)
    (fun mu hmu' => by rw [(hmu y hy mu (interior_subset hmu')).deriv]; exact (hderiv y hy mu (interior_subset hmu')).1)
    (fun mu hmu' => by rw [(hmu y hy mu (interior_subset hmu')).deriv]; exact (hderiv y hy mu (interior_subset hmu')).2)
    ht
  push_cast
  simpa [transportLoss, radius, div_mul_eq_mul_div, mul_div_assoc] using h

end Erdos993Lean.Analytic.HandVariance.Compute
