import Erdos993Lean.Analytic.HandVariance.ContextSound

/-!
# Sound evaluation of the retained hand variance recipes

Source: the exact transport scripts underlying Appendix N.4, including the
two spatial halves, interval hulls, positive logarithm arguments, and retained
polygon lines. A successful evaluation contains an actual formula value;
sign proofs, Taylor consumers, and covering are separate obligations.
-/

namespace Erdos993Lean.Analytic.HandVariance.Compute

open Real Reserve Erdos993Lean.Analytic.TailCert
open Erdos993Lean.Analytic.TailCert.Compute

/-- Source: fixed-point endpoint interpretation in the exact verifiers. -/
theorem loRat_cast (a : Ival) : (loRat a : ℝ) = toR a.lo := endpoint_rat_cast a.lo

/-- Source: fixed-point endpoint interpretation in the exact verifiers. -/
theorem hiRat_cast (a : Ival) : (hiRat a : ℝ) = toR a.hi := endpoint_rat_cast a.hi

/-- Source: the lower fixed-point endpoint read by the exact checkers. -/
theorem mem_loRat {a : Ival} {x : ℝ} (hx : a.Mem x) : (loRat a : ℝ) ≤ x := by
  rw [loRat_cast]
  exact hx.1

/-- Source: the upper fixed-point endpoint read by the exact checkers. -/
theorem mem_hiRat {a : Ival} {x : ℝ} (hx : a.Mem x) : x ≤ (hiRat a : ℝ) := by
  rw [hiRat_cast]
  exact hx.2

/-- Source: the activity change of variables in `tgt:lem:mvt`; positive,
ordered activity endpoints retain their actual interval under exponentiation. -/
theorem exp_mem_log_Icc {lo hi mu : ℝ} (hlo : 0 < lo) (hord : lo ≤ hi)
    (hmu : mu ∈ Set.Icc (log lo) (log hi)) : exp mu ∈ Set.Icc lo hi := by
  constructor
  · simpa only [exp_log hlo] using Real.exp_le_exp.mpr hmu.1
  · simpa only [exp_log (hlo.trans_le hord)] using Real.exp_le_exp.mpr hmu.2

/-- Source: the closed flank formulas in `flankBounds`; no free variable
is assigned an inferred value, and every explicit division/log guard survives. -/
theorem evalClosed_mem (e : Expr) {v : Ival} (he : evalClosed e = some v) :
    v.Mem (e.evalR (fun _ => 0)) := by
  unfold evalClosed at he
  split_ifs at he with hs
  cases Option.some.inj he
  apply e.evalI_mem _ hs
  intro i
  simpa only [zeroI, toR_zero] using mem_pt 0

/-- Source: logarithmic activity-transport distances in the exact scripts. -/
theorem logUpper_sound {q bound : Rat} (he : logUpper q = some bound)
    (hq : (0 : ℝ) < q) : log (q : ℝ) ≤ (bound : ℝ) := by
  dsimp only [logUpper] at he
  split_ifs at he with hlo
  cases Option.some.inj he
  rw [hiRat_cast]
  exact (mem_logI (mem_ofRat q) hlo).2

/-- Source: the successful logarithm's retained positive lower endpoint. -/
theorem logUpper_some_pos {q bound : Rat} (he : logUpper q = some bound) :
    (0 : ℝ) < q := by
  dsimp only [logUpper] at he
  split_ifs at he with hlo
  exact (toR_pos.mpr hlo).trans_le (mem_ofRat q).1

/-- Source: the mid verifier's two spatial halves; every point in the
retained whole interval belongs to at least one of the computed halves. -/
theorem halves_cover (s : Span) (useHalves : Bool) {x : ℝ}
    (hx : (s.lo : ℝ) ≤ x ∧ x ≤ (s.hi : ℝ)) :
    ∃ piece ∈ halves s useHalves, (piece.lo : ℝ) ≤ x ∧ x ≤ (piece.hi : ℝ) := by
  cases useHalves with
  | false => exact ⟨s, by simp [halves], hx⟩
  | true =>
      let c : Rat := (s.lo+s.hi)/2
      by_cases hc : x ≤ (c : ℝ)
      · exact ⟨⟨s.lo,c⟩, by simp [halves, c], hx.1, hc⟩
      · exact ⟨⟨c,s.hi⟩, by simp [halves, c], (le_of_not_ge hc), hx.2⟩

/-- Source: the finite `mapM` of half-interval evaluations. A successful
list evaluation retains a successful result for each actual list element. -/
theorem mapM_some_mem {α β : Type} (f : α → Option β) {xs : List α} {ys : List β}
    (he : xs.mapM f = some ys) {x : α} (hx : x ∈ xs) :
    ∃ y ∈ ys, f x = some y := by
  induction xs generalizing ys with
  | nil => simp at hx
  | cons a rest ih =>
      cases ha : f a with
      | none => simp [List.mapM_cons, ha] at he
      | some b =>
          cases hr : rest.mapM f with
          | none => simp [List.mapM_cons, ha, hr] at he
          | some tail =>
              simp only [List.mapM_cons, ha, hr] at he
              cases Option.some.inj he
              rcases List.mem_cons.mp hx with hxa | hxr
              · subst x
                exact ⟨b, by simp, ha⟩
              · obtain ⟨y, hy, hfy⟩ := ih hr hxr
                exact ⟨y, List.mem_cons_of_mem b hy, hfy⟩

/-- Source: the exact interval hull over half-interval evaluations. -/
theorem foldl_hull_mem_of_seed (rest : List Ival) {seed : Ival} {x : ℝ}
    (hseed : seed.Mem x) : (rest.foldl hull seed).Mem x := by
  induction rest generalizing seed with
  | nil => exact hseed
  | cons a rest ih => exact ih (hull_mem_left hseed)

/-- Source: the exact interval hull over half-interval evaluations. -/
theorem foldl_hull_mem_of_mem {rest : List Ival} {seed v : Ival} {x : ℝ}
    (hv : v ∈ rest) (hval : v.Mem x) : (rest.foldl hull seed).Mem x := by
  induction rest generalizing seed with
  | nil => simp at hv
  | cons a rest ih =>
      rcases List.mem_cons.mp hv with h | h
      · subst v
        exact foldl_hull_mem_of_seed rest (hull_mem_right hval)
      · exact ih h

/-- Source: the exact verifiers' `evalHull`; successful half evaluations
and their hull contain the actual formula throughout the retained rectangle. -/
theorem evalHull_mem (par : Parameters) (ys ls : Span)
    (r J Jcap : Rat) (midMethod : Bool) (e : Expr) {v : Ival} {lam Y : ℝ}
    (he : evalHull par ys ls r J Jcap midMethod e = some v)
    (hl : (ls.lo : ℝ) ≤ lam) (hh : lam ≤ (ls.hi : ℝ))
    (hYl : (ys.lo : ℝ) ≤ Y) (hYh : Y ≤ (ys.hi : ℝ)) :
    v.Mem (e.evalR (realEnv par lam Y r J Jcap)) := by
  let f := fun s => eval (context par s ls r J Jcap midMethod) e
  obtain ⟨piece, hpiece, hYpiece⟩ := halves_cover ys midMethod ⟨hYl,hYh⟩
  cases hvals : (halves ys midMethod).mapM f with
  | none => simp [evalHull, f, hvals] at he
  | some vals =>
      obtain ⟨w, hw, hwe⟩ := mapM_some_mem f hvals hpiece
      have hwm := eval_context_mem par piece ls r J Jcap midMethod e hwe hl hh hYpiece.1 hYpiece.2
      cases vals with
      | nil => simp at hw
      | cons first rest =>
          have hv : rest.foldl hull first = v := by
            simpa [evalHull, f, hvals] using he
          rw [← hv]
          rcases List.mem_cons.mp hw with hw | hw
          · subst w
            exact foldl_hull_mem_of_seed rest hwm
          · exact foldl_hull_mem_of_mem hw hwm

/-- Source: the exact expression and retained-context safety gates. -/
theorem eval_success_safe {ctx : Context} {e : Expr} {v : Ival}
    (he : eval ctx e = some v) : ctx.safe = true ∧ e.safe ctx.env = true := by
  unfold eval at he
  split_ifs at he with hs
  simpa only [Bool.and_eq_true] using hs

/-- Source: the positive divisor/safety gates of exact formula evaluation. -/
theorem eval_context_safe (par : Parameters) (ys ls : Span)
    (r J Jcap : Rat) (midMethod : Bool) (e : Expr) {v : Ival}
    (he : eval (context par ys ls r J Jcap midMethod) e = some v) :
    (context par ys ls r J Jcap midMethod).safe = true ∧
      e.safe (context par ys ls r J Jcap midMethod).env = true := by
  exact eval_success_safe he

/-- Source: successful context evaluations retain actual positive activity. -/
theorem eval_context_activity_pos (par : Parameters) (ys ls : Span)
    (r J Jcap : Rat) (midMethod : Bool) (e : Expr) {v : Ival} {lam : ℝ}
    (he : eval (context par ys ls r J Jcap midMethod) e = some v)
    (hl : (ls.lo : ℝ) ≤ lam) : 0 < lam := by
  have hs := (eval_context_safe par ys ls r J Jcap midMethod e he).1
  have hr : (rawContext par ys ls r J Jcap midMethod).safe = true := by
    cases midMethod with
    | true => exact hs
    | false =>
        change ((rawContext par ys ls r J Jcap false).safe && _ && _ && _ && _) = true at hs
        simp only [Bool.and_eq_true] at hs
        tauto
  obtain ⟨_, hpb⟩ := rawContext_point_safe par ys ls r J Jcap midMethod hr
  exact (point_activity_pos hpb).trans_le hl

/-- Source: base and child-polygon recipes retain a direct rectangular
context, including the unrestricted theta enclosure selected by `false`. -/
theorem eval_rawContext_mem (par : Parameters) (ys ls : Span)
    (r J Jcap : Rat) (cornerTheta : Bool) (e : Expr) {v : Ival} {lam Y : ℝ}
    (he : eval (rawContext par ys ls r J Jcap cornerTheta) e = some v)
    (hl : (ls.lo : ℝ) ≤ lam) (hh : lam ≤ (ls.hi : ℝ))
    (hYl : (ys.lo : ℝ) ≤ Y) (hYh : Y ≤ (ys.hi : ℝ)) :
    v.Mem (e.evalR (realEnv par lam Y r J Jcap)) := by
  unfold eval at he
  split_ifs at he with hs
  simp only [Bool.and_eq_true] at hs
  cases Option.some.inj he
  exact e.evalI_mem (rawContext_mem par ys ls r J Jcap cornerTheta
    hs.1 hl hh hYl hYh) hs.2

/-- Source: successful direct rectangle evaluations retain positive activity. -/
theorem eval_rawContext_activity_pos (par : Parameters) (ys ls : Span)
    (r J Jcap : Rat) (cornerTheta : Bool) (e : Expr) {v : Ival} {lam : ℝ}
    (he : eval (rawContext par ys ls r J Jcap cornerTheta) e = some v)
    (hl : (ls.lo : ℝ) ≤ lam) : 0 < lam := by
  obtain ⟨_, hpb⟩ := rawContext_point_safe par ys ls r J Jcap cornerTheta
    (eval_success_safe he).1
  exact (point_activity_pos hpb).trans_le hl

/-- Source: the child-polygon rectangle and midpoint after retaining its
actual line; this is the direct context used by `polygonLower`. -/
theorem eval_raw_polygon_context_mem (par : Parameters) (ys ls : Span)
    (r J Jcap slope intercept : Rat) (cornerTheta : Bool) (e : Expr)
    {v : Ival} {lam Y : ℝ}
    (he : eval
      { env := fun i => if i == 19 then ofRat slope else if i == 20 then ofRat intercept
          else (rawContext par ys ls r J Jcap cornerTheta).env i
        safe := (rawContext par ys ls r J Jcap cornerTheta).safe } e = some v)
    (hl : (ls.lo : ℝ) ≤ lam) (hh : lam ≤ (ls.hi : ℝ))
    (hYl : (ys.lo : ℝ) ≤ Y) (hYh : Y ≤ (ys.hi : ℝ)) :
    v.Mem (e.evalR (fun i => if i == 19 then (slope : ℝ) else if i == 20 then
      (intercept : ℝ) else realEnv par lam Y r J Jcap i)) := by
  unfold eval at he
  split_ifs at he with hs
  simp only [Bool.and_eq_true] at hs
  cases Option.some.inj he
  exact e.evalI_mem (override_line_mem
    (rawContext_mem par ys ls r J Jcap cornerTheta hs.1 hl hh hYl hYh) slope intercept) hs.2

/-- Source: the child-polygon evaluation after retaining its actual line.
The original parent/child environment and the rational line survive together. -/
theorem eval_polygon_context_mem (par : Parameters) (ys ls : Span)
    (r J Jcap slope intercept : Rat) (midMethod : Bool) (e : Expr)
    {v : Ival} {lam Y : ℝ}
    (he : eval
      { env := fun i => if i == 19 then ofRat slope else if i == 20 then ofRat intercept
          else (context par ys ls r J Jcap midMethod).env i
        safe := (context par ys ls r J Jcap midMethod).safe } e = some v)
    (hl : (ls.lo : ℝ) ≤ lam) (hh : lam ≤ (ls.hi : ℝ))
    (hYl : (ys.lo : ℝ) ≤ Y) (hYh : Y ≤ (ys.hi : ℝ)) :
    v.Mem (e.evalR (fun i => if i == 19 then (slope : ℝ) else if i == 20 then
      (intercept : ℝ) else realEnv par lam Y r J Jcap i)) := by
  unfold eval at he
  split_ifs at he with hs
  simp only [Bool.and_eq_true] at hs
  cases Option.some.inj he
  exact e.evalI_mem (override_line_mem
    (context_mem par ys ls r J Jcap midMethod hs.1 hl hh hYl hYh) slope intercept) hs.2

end Erdos993Lean.Analytic.HandVariance.Compute

#print axioms Erdos993Lean.Analytic.HandVariance.Compute.context_mem
#print axioms Erdos993Lean.Analytic.HandVariance.Compute.eval_context_mem
#print axioms Erdos993Lean.Analytic.HandVariance.hasDerivAt_vertexAPrime_Y
#print axioms Erdos993Lean.Analytic.HandVariance.Compute.evalHull_mem
#print axioms Erdos993Lean.Analytic.HandVariance.Compute.logUpper_sound
