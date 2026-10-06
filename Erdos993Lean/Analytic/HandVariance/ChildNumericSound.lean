import Erdos993Lean.Analytic.HandVariance.FormulaMeaning
import Erdos993Lean.Analytic.HandVariance.EvalSound
import Erdos993Lean.Analytic.HandVariance.CheckTaylor
import Erdos993Lean.Analytic.HandVariance.Transport

/-!
# Soundness of child polygon, tail-chain and selected-leaf checks

Source: TWIN v1.8 Appendix N.4, the child polygon paragraph following
`tgt:lem:poly`, `tgt:lem:child` (b), and `mc:lem:base`. Every result retains
its actual activity and child coordinate. Finite check coverage and the
forest induction remain separate consumers.
-/
namespace Erdos993Lean.Analytic.HandVariance.Compute
open Real Reserve Set Erdos993Lean.Analytic.TailCert
open Erdos993Lean.Analytic.TailCert.Compute

/-- Source: the child polygon Taylor recipe; its checked lower slack
bounds the actual line slack on the same retained spatial interval. -/
theorem polygonLower_sound (p : PolygonCheck) {beta : Rat}
    (hcheck : polygonLower p = some beta) (hlam : 0 < (p.activity : ℝ))
    {T : ℝ} (hT : T ∈ Icc (p.spatial.lo : ℝ) (p.spatial.hi : ℝ)) :
    (beta : ℝ) ≤ (p.intercept : ℝ) + (p.slope : ℝ) * childR p.activity T -
      coefJ p.activity T := by
  simp only [polygonLower, Bind.bind, Option.bind_eq_some_iff, pure,
    Option.some.injEq] at hcheck
  obtain ⟨value, hvalue, slope, hslope, second, hsecond, hbeta⟩ := hcheck
  subst beta
  let center : Rat := (p.spatial.lo+p.spatial.hi)/2
  let radius : Rat := (p.spatial.hi-p.spatial.lo)/2
  let F : ℝ → ℝ := fun t => coefJ p.activity t-p.slope*childR p.activity t
  let Fp : ℝ → ℝ := fun t => coefJPrime p.activity t-p.slope*childRPrime p.activity t
  let Fpp : ℝ → ℝ := fun t => coefJSecond p.activity t-p.slope*childRSecond p.activity t
  have hvm := eval_raw_polygon_context_mem (parameters 1) ⟨center,center⟩
    ⟨p.activity,p.activity⟩ 0 0 0 p.slope p.intercept false fpolygon hvalue
    (lam := (p.activity : ℝ)) (Y := (center : ℝ)) le_rfl le_rfl le_rfl le_rfl
  have hsm := eval_raw_polygon_context_mem (parameters 1) ⟨center,center⟩
    ⟨p.activity,p.activity⟩ 0 0 0 p.slope p.intercept false fpolygonp hslope
    (lam := (p.activity : ℝ)) (Y := (center : ℝ)) le_rfl le_rfl le_rfl le_rfl
  change value.Mem (fpolygon.evalR (lineEnv (parameters 1) p.activity center p.slope p.intercept)) at hvm
  change slope.Mem (fpolygonp.evalR (lineEnv (parameters 1) p.activity center p.slope p.intercept)) at hsm
  rw [eval_fpolygon] at hvm
  rw [eval_fpolygonp _ _ _ _ _ hlam] at hsm
  obtain ⟨hc, hdist⟩ := span_midpoint_radius p.spatial hT
  have hupper := midpoint_taylor_upper_enclosure
    (f := F) (f' := Fp) (f'' := Fpp)
    (M := (max 0 (hiRat second) : Rat))
    (value := (hiRat value : Rat)) (dLo := (loRat slope : Rat))
    (dHi := (hiRat slope : Rat))
    (radius := (radius : ℝ))
    (fun t _ => (hasDerivAt_coefJ_Y hlam).sub
      ((hasDerivAt_childR_Y hlam).const_mul (p.slope : ℝ)))
    (fun t _ => (hasDerivAt_coefJPrime_Y hlam).sub
      ((hasDerivAt_childRPrime_Y hlam).const_mul (p.slope : ℝ)))
    (by
      intro t ht
      have hm := eval_raw_polygon_context_mem (parameters 1) p.spatial
        ⟨p.activity,p.activity⟩ 0 0 0 p.slope p.intercept false fpolygonpp hsecond
        (lam := (p.activity : ℝ)) (Y := t) le_rfl le_rfl
        (interior_subset ht).1 (interior_subset ht).2
      change second.Mem (fpolygonpp.evalR (lineEnv (parameters 1) p.activity t p.slope p.intercept)) at hm
      rw [eval_fpolygonpp _ _ _ _ _ hlam] at hm
      exact (mem_hiRat hm).trans (by exact_mod_cast le_max_right (0 : Rat) (hiRat second)))
    (by exact_mod_cast le_max_left (0 : Rat) (hiRat second)) hc hT hdist
    (mem_hiRat hvm) (mem_loRat hsm) (mem_hiRat hsm)
  change coefJ p.activity T-p.slope*childR p.activity T ≤ _ at hupper
  push_cast
  dsimp [radius] at hupper
  push_cast at hupper
  linarith

/-- Source: the finite child-tail chain recipe, including its final ray.
The optional right endpoint is retained explicitly in the conclusion. -/
theorem chainLower_endpoint_sound (c : ChainCheck) {beta : Rat}
    (hcheck : chainLower c = some beta) :
    (0 : ℝ) < c.activity ∧ (0 : ℝ) < c.left ∧
    (beta : ℝ) ≤ -(1/(c.left : ℝ) +
      1/(1+(match c.right with | none => 0 | some t => msg c.activity t)/2) -
      2+2*msg c.activity c.left) := by
  dsimp only [chainLower] at hcheck
  split_ifs at hcheck with hs
  have hguards : ((point c.activity c.left).safe &&
      (match c.right with | none => true | some t => (point c.activity t).safe && decide (c.left < t)) &&
      decide (0 < c.left) && decide (0 ≤ (match c.right with
        | none => zeroI | some t => (point c.activity t).p).lo)) = true := by
    simpa only [Bool.not_eq_true_eq_eq_false, Bool.eq_true_eq_not_eq_false] using hs
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hguards
  have hsafe : (point c.activity c.left).safe = true := by tauto
  have hleft : (0 : Rat) < c.left := by tauto
  have hpb : 0 ≤ (match c.right with
      | none => zeroI | some t => (point c.activity t).p).lo := by tauto
  have hlamp := point_activity_pos hsafe
  simp only [Bind.bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hcheck
  obtain ⟨term, hterm, hbeta⟩ := hcheck
  subst beta
  refine ⟨hlamp, by exact_mod_cast hleft, ?_⟩
  have hm := evalClosed_mem _ hterm
  dsimp only [Expr.evalR] at hm
  norm_num only [Rat.cast_natCast] at hm
  have hpa := (point_mem hsafe).2.1
  have hlo : (loRat (match c.right with
      | none => zeroI | some t => (point c.activity t).p) : ℝ) ≤
      (match c.right with | none => 0 | some t => msg c.activity t) := by
    cases hr : c.right with
    | none => simp [loRat_cast, zeroI, pt, toR_zero]
    | some t =>
        have hright : (point c.activity t).safe = true := by
          simp only [hr, Bool.and_eq_true, decide_eq_true_eq] at hguards
          tauto
        exact mem_loRat (point_mem hright).2.1
  have hlononneg : (0 : ℝ) ≤ (loRat (match c.right with
      | none => zeroI | some t => (point c.activity t).p) : ℝ) := by
    rw [loRat_cast]
    exact toR_nonneg.mpr hpb
  have hdenpos : (0 : ℝ) < (1 : ℝ)+(loRat (match c.right with
      | none => zeroI | some t => (point c.activity t).p) : ℝ)/2 := by linarith
  have hdenle : (1 : ℝ)+(loRat (match c.right with
      | none => zeroI | some t => (point c.activity t).p) : ℝ)/2 ≤
      (1 : ℝ)+(match c.right with | none => (0 : ℝ) | some t => msg c.activity t)/2 := by linarith
  have hrecip := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ (1 : ℝ) by norm_num)
    hdenpos hdenle
  rw [Rat.cast_neg]
  apply neg_le_neg
  have hpupper := mem_hiRat hpa
  calc
    _ ≤ (1 : ℝ)/(c.left : ℝ) +
        (1 : ℝ)/((1 : ℝ)+(loRat (match c.right with
          | none => zeroI | some t => (point c.activity t).p) : ℝ)/2) -
        2+2*(hiRat (point c.activity c.left).p : ℝ) := by linarith
    _ ≤ (hiRat term : ℝ) := mem_hiRat hm

/-- Source: `tgt:lem:child` (b), the checked finite or terminal segment
bounds the actual logarithmic derivative factor at each of its points. -/
theorem chainLower_sound (c : ChainCheck) {beta : Rat}
    (hcheck : chainLower c = some beta) {T : ℝ} (hleft : (c.left : ℝ) ≤ T)
    (hright : ∀ t, c.right = some t → T ≤ (t : ℝ)) :
    (beta : ℝ) ≤ -childSlope c.activity T := by
  obtain ⟨hlam, ha, hbound⟩ := chainLower_endpoint_sound c hcheck
  cases hr : c.right with
  | none =>
      simp only [hr, zero_div, add_zero, div_one] at hbound
      have hs := childSlope_le_terminal hlam ha hleft
      linarith
  | some t =>
      simp only [hr] at hbound
      have hs := childSlope_le_segment hlam ha hleft (hright t hr)
      linarith

/-- Source: `mc:lem:base`; midpoint evaluation followed by the signed
activity transport bounds the actual selected-leaf slack over its interval. -/
theorem baseLower_sound (b : BaseCheck) {beta : Rat}
    (hcheck : baseLower b = some beta) (hlo : (0 : ℝ) < b.activity.lo)
    {lam : ℝ} (hlam : lam ∈ Icc (b.activity.lo : ℝ) (b.activity.hi : ℝ)) :
    (beta : ℝ) ≤ baseSlack (parameters b.segment).asBand lam := by
  simp only [baseLower, Bind.bind, Option.bind_eq_some_iff, pure,
    Option.some.injEq] at hcheck
  obtain ⟨value, hvalue, values, hvalues, dm, hdm, dp, hdp, hbeta⟩ := hcheck
  subst beta
  let center : Rat := (b.activity.lo+b.activity.hi)/2
  let deriv : Ival := values.foldl hull (ofRat 0)
  have hcenter : (center : ℝ) ∈ Icc (b.activity.lo : ℝ) (b.activity.hi : ℝ) :=
    (span_midpoint_radius b.activity hlam).1
  have hcpos := hlo.trans_le hcenter.1
  have hvm := eval_rawContext_mem (parameters b.segment) ⟨0,0⟩ ⟨center,center⟩
    0 0 0 false fbase hvalue (lam := (center : ℝ)) (Y := (0 : ℝ))
    le_rfl le_rfl (by norm_num) (by norm_num)
  rw [eval_fbase] at hvm
  have hds : ∀ mu ∈ Icc (log (b.activity.lo : ℝ)) (log (b.activity.hi : ℝ)),
      deriv.Mem (baseSlackDot (parameters b.segment).asBand (exp mu)) := by
    intro mu hmu
    have hm := exp_mem_log_Icc hlo (hlam.1.trans hlam.2) hmu
    obtain ⟨piece, hp, hpiece⟩ := halves_cover b.activity b.useHalves hm
    obtain ⟨d, hd, hde⟩ := mapM_some_mem _ hvalues hp
    have hen := eval_rawContext_mem (parameters b.segment) ⟨0,0⟩ piece
      0 0 0 false fbased hde (lam := exp mu) (Y := (0 : ℝ))
      hpiece.1 hpiece.2 (by norm_num) (by norm_num)
    rw [eval_fbased _ _ _ _ _ _ (exp_pos mu)] at hen
    exact foldl_hull_mem_of_mem hd hen
  have hdmlog : log ((center : ℝ)/(b.activity.lo : ℝ)) ≤ (dm : ℝ) := by
    simpa [center] using logUpper_sound hdm
      (by simpa [center] using div_pos hcpos hlo)
  have hdplog : log ((b.activity.hi : ℝ)/(center : ℝ)) ≤ (dp : ℝ) := by
    simpa [center] using logUpper_sound hdp
      (by simpa [center] using div_pos (hcpos.trans_le hcenter.2) hcpos)
  have ht := transport_log_activity (F := baseSlack (parameters b.segment).asBand)
    hlo hcenter hlam hdmlog hdplog
    (fun mu _ => (hasDerivAt_baseSlack_mu _ mu).continuousAt.continuousWithinAt)
    (fun mu _ => (hasDerivAt_baseSlack_mu _ mu).differentiableAt.differentiableWithinAt)
    (fun mu hmu => by
      rw [(hasDerivAt_baseSlack_mu _ mu).deriv]
      exact mem_loRat (hds mu (interior_subset hmu)))
    (fun mu hmu => by
      rw [(hasDerivAt_baseSlack_mu _ mu).deriv]
      exact mem_hiRat (hds mu (interior_subset hmu)))
    (mem_loRat hvm)
  simpa only [Rat.cast_sub, transportLoss, Rat.cast_max, Rat.cast_mul,
    Rat.cast_zero, Rat.cast_neg] using ht

end Erdos993Lean.Analytic.HandVariance.Compute

#print axioms Erdos993Lean.Analytic.HandVariance.Compute.polygonLower_sound
#print axioms Erdos993Lean.Analytic.HandVariance.Compute.chainLower_sound
#print axioms Erdos993Lean.Analytic.HandVariance.Compute.baseLower_sound
