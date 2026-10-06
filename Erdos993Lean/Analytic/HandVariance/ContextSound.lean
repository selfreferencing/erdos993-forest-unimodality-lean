import Erdos993Lean.Analytic.HandVariance.Compute.Context
import Erdos993Lean.Analytic.HandVariance.Compute.Checks
import Erdos993Lean.Analytic.HandVariance.ExprSound
import Erdos993Lean.Analytic.HandVariance.Primitives
import Erdos993Lean.Analytic.HandVariance.Derivatives
import Erdos993Lean.Analytic.TailCert.Mono

/-!
# Sound primitive intervals for the hand variance contexts

Source: TWIN v1.8 Appendix N.4, Lemma `tgt:lem:tr`, and the `pp_of`
endpoint/quarter enclosure in the exact transport scripts. This file proves
primitive containment, retaining the actual activity and parent log-mass.
The mean-value intersections are a separate obligation: they must consume
the actual first and second derivatives of `lBar` on the same rectangle.
-/

namespace Erdos993Lean.Analytic.HandVariance.Compute

open Real Reserve Erdos993Lean.Analytic.TailCert
open Erdos993Lean.Analytic.TailCert.Compute

/-- Source: `mc:def:curve`; parameters used in the actual parent functions.
Only `D`, `aCoef`, and `gDen` occur in these functions. -/
def Parameters.asBand (par : Parameters) : Band := ⟨0, 0, par.D, par.a, par.g⟩

/-- Source: Section `hand:var:set`; the activity variance `q(1-q)`. -/
noncomputable def activityVariance (lam : ℝ) : ℝ := lam / (1+lam)^2

/-- Source: `tgt:lem:dmu`; the activity variance has this rational form. -/
theorem activityVariance_eq {lam : ℝ} (hlam : 0 < lam) :
    activityVariance lam = actQ lam * (1-actQ lam) := by
  unfold activityVariance actQ
  field_simp [show 1+lam ≠ 0 by linarith]
  ring

/-- Source: the natural activity interval in the non-mid transport scripts;
this enclosure remains sound when the activity interval crosses 1. -/
theorem activityVariance_natural_corners {a lam b : ℝ}
    (ha : 0 < a) (hl : a ≤ lam) (hh : lam ≤ b) :
    a/(1+b)^2 ≤ activityVariance lam ∧ activityVariance lam ≤ b/(1+a)^2 := by
  have hlam : 0 < lam := ha.trans_le hl
  have hb : 0 < b := hlam.trans_le hh
  have hda : 0 < (1+a)^2 := sq_pos_of_pos (by linarith)
  have hdl : 0 < (1+lam)^2 := sq_pos_of_pos (by linarith)
  have hdb : 0 < (1+b)^2 := sq_pos_of_pos (by linarith)
  have hsql : (1+a)^2 ≤ (1+lam)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ lam-a by linarith) (show 0 ≤ 2+a+lam by linarith)]
  have hsqh : (1+lam)^2 ≤ (1+b)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ b-lam by linarith) (show 0 ≤ 2+lam+b by linarith)]
  unfold activityVariance
  constructor
  · exact (div_le_div_of_nonneg_left ha.le hdl hsqh).trans
      (div_le_div_of_nonneg_right hl hdl.le)
  · exact (div_le_div_of_nonneg_right hh hdl.le).trans
      (div_le_div_of_nonneg_left hb.le hda hsql)

/-- Source: the activity-endpoint monotonicity check in the mid transport
script. The exact factorization preserves which side of 1 is retained. -/
theorem activityVariance_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    activityVariance b - activityVariance a =
      (b-a)*(1-a*b)/((1+a)^2*(1+b)^2) := by
  unfold activityVariance
  field_simp [show 1+a ≠ 0 by linarith, show 1+b ≠ 0 by linarith]
  ring

/-- Source: the activity-endpoint monotonicity check in the mid transport
script, increasing on `(0,1]`. -/
theorem activityVariance_le_of_le_one {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) :
    activityVariance a ≤ activityVariance b := by
  have hb0 := ha.trans_le hab
  have hp : a*b ≤ 1 := by
    calc
      a*b ≤ 1*b := mul_le_mul_of_nonneg_right (hab.trans hb) hb0.le
      _ ≤ 1 := by simpa using hb
  have hnon : 0 ≤ (b-a)*(1-a*b)/((1+a)^2*(1+b)^2) := by
    apply div_nonneg (mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hp))
    positivity
  have hd := activityVariance_sub ha hb0
  linarith

/-- Source: the activity-endpoint monotonicity check in the mid transport
script, decreasing on `[1,∞)`. -/
theorem activityVariance_le_of_one_le {a b : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) : activityVariance b ≤ activityVariance a := by
  have ha0 : 0 < a := by linarith
  have hb0 := ha0.trans_le hab
  have hp : 1 ≤ a*b := by
    exact ha.trans (by simpa using mul_le_mul_of_nonneg_left (ha.trans hab) ha0.le)
  have hnon : (b-a)*(1-a*b)/((1+a)^2*(1+b)^2) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    · positivity
  have hd := activityVariance_sub ha0 hb0
  linarith

/-- Source: the restricted activity endpoint hull in the mid transport
script; crossing 1 is explicitly excluded. -/
theorem activityVariance_endpoint_corners {a lam b : ℝ}
    (ha : 0 < a) (hl : a ≤ lam) (hh : lam ≤ b)
    (hside : b ≤ 1 ∨ 1 ≤ a) :
    min (activityVariance a) (activityVariance b) ≤ activityVariance lam ∧
      activityVariance lam ≤ max (activityVariance a) (activityVariance b) := by
  rcases hside with h | h
  · exact ⟨(min_le_left _ _).trans (activityVariance_le_of_le_one ha hl (hh.trans h)),
      (activityVariance_le_of_le_one (ha.trans_le hl) hh h).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (activityVariance_le_of_one_le (h.trans hl) hh),
      (activityVariance_le_of_one_le h hl).trans (le_max_left _ _)⟩

/-- Source: the rational endpoint intervals used throughout Appendix N.4. -/
theorem ratSpan_mem {a b : Rat} {x : ℝ}
    (ha : (a : ℝ) ≤ x) (hb : x ≤ (b : ℝ)) : (ratSpan a b).Mem x :=
  ⟨(mem_ofRat a).1.trans ha, hb.trans (mem_ofRat b).2⟩

/-- Source: the endpoint hull in the activity-derivative enclosure. -/
theorem hull_mem_left {a b : Ival} {x : ℝ} (h : a.Mem x) :
    (hull a b).Mem x := by
  change toR (min a.lo b.lo) ≤ x ∧ x ≤ toR (max a.hi b.hi)
  rw [toR_min, toR_max]
  exact ⟨(min_le_left _ _).trans h.1, h.2.trans (le_max_left _ _)⟩

/-- Source: the endpoint hull in the activity-derivative enclosure. -/
theorem hull_mem_right {a b : Ival} {x : ℝ} (h : b.Mem x) :
    (hull a b).Mem x := by
  change toR (min a.lo b.lo) ≤ x ∧ x ≤ toR (max a.hi b.hi)
  rw [toR_min, toR_max]
  exact ⟨(min_le_right _ _).trans h.1, h.2.trans (le_max_right _ _)⟩

/-- Source: `tfun.phi2_piece`; an intersection preserves a value already
proved to lie in both retained enclosures. This does not supply the required
mean-value derivative proof for either enclosure. -/
theorem intersection_mem {a b : Ival} {x : ℝ}
    (ha : a.Mem x) (hb : b.Mem x) : (intersection a b).Mem x := by
  change toR (max a.lo b.lo) ≤ x ∧ x ≤ toR (min a.hi b.hi)
  rw [toR_max, toR_min]
  exact ⟨max_le ha.1 hb.1, le_min ha.2 hb.2⟩

/-- Source: fixed-point endpoint interpretation used by `pp_of`. -/
theorem endpoint_rat_cast (n : ℤ) :
    (((n : Rat) / (one : Rat) : Rat) : ℝ) = toR n := by
  simp only [Rat.cast_div, Rat.cast_intCast]
  unfold toR
  rw [one_eq]
  push_cast
  rfl

/-- Source: `pp_of`; the exact endpoint/quarter enclosure of `x(1-x)`. -/
theorem parabola_enclosure {a b x : ℝ} (ha : a ≤ x) (hb : x ≤ b) :
    min (a * (1-a)) (b * (1-b)) ≤ x * (1-x) ∧
      x * (1-x) ≤
        if a ≤ 1/2 ∧ 1/2 ≤ b then 1/4 else max (a*(1-a)) (b*(1-b)) := by
  constructor
  · rcases le_total x (1/2) with hx | hx
    · have hprod : 0 ≤ (x-a) * (1-x-a) :=
        mul_nonneg (by linarith) (by linarith)
      exact (min_le_left _ _).trans (by nlinarith)
    · have hprod : 0 ≤ (b-x) * (b+x-1) :=
        mul_nonneg (by linarith) (by linarith)
      exact (min_le_right _ _).trans (by nlinarith)
  · split_ifs with hcross
    · nlinarith [sq_nonneg (x-1/2)]
    · rcases lt_or_ge b (1/2) with hbhalf | hbhalf
      · have hprod : 0 ≤ (b-x) * (1-b-x) :=
          mul_nonneg (by linarith) (by linarith)
        exact (show x*(1-x) ≤ b*(1-b) by nlinarith).trans (le_max_right _ _)
      · have hahalf : 1/2 < a := by
          by_contra h
          exact hcross ⟨le_of_not_gt h, hbhalf⟩
        have hprod : 0 ≤ (x-a) * (x+a-1) :=
          mul_nonneg (by linarith) (by linarith)
        exact (show x*(1-x) ≤ a*(1-a) by nlinarith).trans (le_max_left _ _)

/-- Source: `pp_of`; rounded endpoint/quarter evaluation contains the
actual occupation variance, including intervals crossing one half. -/
theorem parabolaRange_mem {p : Ival} {x : ℝ} (hx : p.Mem x) :
    (parabolaRange p).Mem (x * (1-x)) := by
  let a : Rat := (p.lo : Rat) / (one : Rat)
  let b : Rat := (p.hi : Rat) / (one : Rat)
  have hca : (a : ℝ) = toR p.lo := endpoint_rat_cast p.lo
  have hcb : (b : ℝ) = toR p.hi := endpoint_rat_cast p.hi
  have ha : (a : ℝ) ≤ x := by rw [hca]; exact hx.1
  have hb : x ≤ (b : ℝ) := by rw [hcb]; exact hx.2
  obtain ⟨hlo, hhi⟩ := parabola_enclosure ha hb
  change (ratSpan (min (a*(1-a)) (b*(1-b)))
    (if a ≤ 1/2 ∧ 1/2 ≤ b then 1/4 else max (a*(1-a)) (b*(1-b)))).Mem _
  apply ratSpan_mem
  · simpa only [Rat.cast_min, Rat.cast_mul, Rat.cast_sub, Rat.cast_one] using hlo
  · by_cases hc : a ≤ 1/2 ∧ 1/2 ≤ b
    · have hcr : (a : ℝ) ≤ 1/2 ∧ 1/2 ≤ (b : ℝ) := by
        constructor
        · have h := (Rat.cast_le (K := ℝ)).mpr hc.1
          norm_num at h
          exact h
        · have h := (Rat.cast_le (K := ℝ)).mpr hc.2
          norm_num at h
          exact h
      simp only [if_pos hc] at *
      simpa only [if_pos hcr, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hhi
    · have hcr : ¬ ((a : ℝ) ≤ 1/2 ∧ 1/2 ≤ (b : ℝ)) := by
        intro h
        apply hc
        constructor
        · apply (Rat.cast_le (K := ℝ)).mp
          norm_num
          exact h.1
        · apply (Rat.cast_le (K := ℝ)).mp
          norm_num
          exact h.2
      simp only [if_neg hc]
      simpa only [if_neg hcr, Rat.cast_max, Rat.cast_mul, Rat.cast_sub,
        Rat.cast_one] using hhi

/-- Source: Section `hand:var:set`; the five actual parent primitives
enclosed by a fixed-precision point evaluation. -/
def Point.Mem (v : Point) (lam Y : ℝ) : Prop :=
  v.e.Mem (parentE lam Y) ∧ v.p.Mem (msg lam Y) ∧
    v.phi.Mem (lmass lam Y) ∧ v.k.Mem (parentK lam Y) ∧
      v.theta.Mem (parentTheta lam Y)

/-- Source: `tgt:lem:tr`; Boolean safety retains actual positive divisor
lower endpoints. In particular this does not assert that positive activity
alone forces a fixed-precision safety flag. -/
theorem point_mem {lam Y : Rat} (hs : (point lam Y).safe = true) :
    (point lam Y).Mem lam Y := by
  let li := ofRat lam
  let r := mul li (expI (ofRat (-Y)))
  let den := add oneI r
  let p := div r den
  let phi := logI den
  let k := div p phi
  change (decide (0 < li.lo) && decide (0 < den.lo) &&
    decide (0 < phi.lo)) = true at hs
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
  have hli : li.Mem (lam : ℝ) := mem_ofRat lam
  have hminus : (ofRat (-Y)).Mem (-(Y : ℝ)) := by
    simpa only [Rat.cast_neg] using mem_ofRat (-Y)
  have hr : r.Mem ((lam : ℝ) * exp (-(Y : ℝ))) := mem_mul hli (mem_expI hminus)
  have hone : oneI.Mem (1 : ℝ) := by simpa only [oneI, toR_one] using mem_pt one
  have hden : den.Mem (1 + (lam : ℝ) * exp (-(Y : ℝ))) := mem_add hone hr
  have hp : p.Mem (msg lam Y) := by
    simpa only [Reserve.msg] using mem_div hr hden hs.1.2
  have hphi : phi.Mem (lmass lam Y) := by
    simpa only [Reserve.lmass] using mem_logI hden hs.1.2
  have hk : k.Mem (parentK lam Y) := mem_div hp hphi hs.2
  have he : (div (expI (ofRat Y)) li).Mem (parentE lam Y) :=
    mem_div (mem_expI (mem_ofRat Y)) hli hs.1.1
  have ht : (sub (add k p) oneI).Mem (parentTheta lam Y) :=
    mem_sub (mem_add hk hp) hone
  exact ⟨he, hp, hphi, hk, ht⟩

/-- Source: the positive-activity point guard in `tgt:lem:tr`. -/
theorem point_activity_pos {lam Y : Rat} (hs : (point lam Y).safe = true) :
    (0 : ℝ) < lam := by
  change (decide (0 < (ofRat lam).lo) && decide (0 <
    (add oneI (mul (ofRat lam) (expI (ofRat (-Y))))).lo) &&
    decide (0 < (logI (add oneI (mul (ofRat lam) (expI (ofRat (-Y)))))).lo)) = true at hs
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
  exact (toR_pos.mpr hs.1.1).trans_le (mem_ofRat lam).1

/-- Source: `tgt:lem:tr`; a mixed endpoint interval contains every value
between the two actual corner values. -/
theorem cornerSpan_mem {a b : Ival} {lo hi x : ℝ}
    (ha : a.Mem lo) (hb : b.Mem hi) (hl : lo ≤ x) (hh : x ≤ hi) :
    (⟨a.lo, b.hi⟩ : Ival).Mem x := ⟨ha.1.trans hl, hh.trans hb.2⟩

/-- Source: `tgt:lem:tr`; the four unrestricted opposite-corner primitive
intervals used by `rawContext` contain the actual values throughout the box. -/
theorem rawContext_four_primitives_mem (par : Parameters) (ys ls : Span)
    (r J Jcap : Rat) (cornerTheta : Bool) {lam Y : ℝ}
    (hpa : (point ls.hi ys.lo).safe = true)
    (hpb : (point ls.lo ys.hi).safe = true)
    (hl : (ls.lo : ℝ) ≤ lam) (hh : lam ≤ (ls.hi : ℝ))
    (hYl : (ys.lo : ℝ) ≤ Y) (hYh : Y ≤ (ys.hi : ℝ)) :
    ((rawContext par ys ls r J Jcap cornerTheta).env 1).Mem (parentE lam Y) ∧
    ((rawContext par ys ls r J Jcap cornerTheta).env 2).Mem (msg lam Y) ∧
    ((rawContext par ys ls r J Jcap cornerTheta).env 18).Mem (lmass lam Y) ∧
    ((rawContext par ys ls r J Jcap cornerTheta).env 3).Mem (parentK lam Y) := by
  obtain ⟨hea, hpa', hphia, hka, _⟩ := point_mem hpa
  obtain ⟨heb, hpb', hphib, hkb, _⟩ := point_mem hpb
  obtain ⟨he, hp, hphi, hk⟩ :=
    primitive_corners (point_activity_pos hpb) hl hh hYl hYh
  exact ⟨cornerSpan_mem hea heb he.1 he.2,
    cornerSpan_mem hpb' hpa' hp.1 hp.2,
    cornerSpan_mem hphib hphia hphi.1 hphi.2,
    cornerSpan_mem hka hkb hk.1 hk.2⟩

/-- Source: `tgt:lem:tr`; both the restricted theta corner enclosure and
the unrestricted interval-addition enclosure preserve the actual theta. -/
theorem rawContext_theta_mem (par : Parameters) (ys ls : Span)
    (r J Jcap : Rat) (cornerTheta : Bool) {lam Y : ℝ}
    (hpa : (point ls.hi ys.lo).safe = true)
    (hpb : (point ls.lo ys.hi).safe = true)
    (hl : (ls.lo : ℝ) ≤ lam) (hh : lam ≤ (ls.hi : ℝ))
    (hYl : (ys.lo : ℝ) ≤ Y) (hYh : Y ≤ (ys.hi : ℝ))
    (hcorner : cornerTheta = true →
      (0 : ℝ) ≤ ys.lo ∧ (ls.hi : ℝ) ≤ 263/200) :
    ((rawContext par ys ls r J Jcap cornerTheta).env 4).Mem (parentTheta lam Y) := by
  cases cornerTheta with
  | false =>
      obtain ⟨_, hp, _, hk⟩ :=
        rawContext_four_primitives_mem par ys ls r J Jcap false hpa hpb hl hh hYl hYh
      have hone : oneI.Mem (1 : ℝ) := by
        simpa only [oneI, toR_one] using mem_pt one
      exact mem_sub (mem_add hk hp) hone
  | true =>
      obtain ⟨_, _, _, _, htha⟩ := point_mem hpa
      obtain ⟨_, _, _, _, hthb⟩ := point_mem hpb
      obtain ⟨hY0, hlb⟩ := hcorner rfl
      obtain ⟨htlo, hthi⟩ := parentTheta_corners
        (point_activity_pos hpb) hl hh hY0 hYl hYh hlb
      exact cornerSpan_mem hthb htha htlo hthi

/-- Source: the retained safety flags of the two actual corner evaluations. -/
theorem rawContext_point_safe (par : Parameters) (ys ls : Span)
    (r J Jcap : Rat) (cornerTheta : Bool)
    (hs : (rawContext par ys ls r J Jcap cornerTheta).safe = true) :
    (point ls.hi ys.lo).safe = true ∧ (point ls.lo ys.hi).safe = true := by
  simp only [rawContext, Id.run, pure, Bool.and_eq_true] at hs
  tauto

/-- Source: the restricted theta corner guard in `tgt:lem:tr`. -/
theorem rawContext_corner_guards (par : Parameters) (ys ls : Span)
    (r J Jcap : Rat) (cornerTheta : Bool)
    (hs : (rawContext par ys ls r J Jcap cornerTheta).safe = true)
    (hc : cornerTheta = true) :
    (0 : ℝ) ≤ ys.lo ∧ (ls.hi : ℝ) ≤ 263/200 := by
  subst cornerTheta
  simp only [rawContext, Id.run, pure, Bool.and_eq_true, Bool.not_true,
    Bool.false_or, decide_eq_true_eq] at hs
  have hY : (0 : Rat) ≤ ys.lo := by tauto
  have hl : ls.hi ≤ (263/200 : Rat) := by tauto
  refine ⟨by exact_mod_cast hY, ?_⟩
  have h := (Rat.cast_le (K := ℝ)).mpr hl
  norm_num at h
  exact h

/-- Source: `tgt:lem:tr`; safely retained primitive entries of the raw
context contain the actual parent coordinates throughout its rectangle. -/
theorem rawContext_primitives_mem (par : Parameters) (ys ls : Span)
    (r J Jcap : Rat) (cornerTheta : Bool) {lam Y : ℝ}
    (hs : (rawContext par ys ls r J Jcap cornerTheta).safe = true)
    (hl : (ls.lo : ℝ) ≤ lam) (hh : lam ≤ (ls.hi : ℝ))
    (hYl : (ys.lo : ℝ) ≤ Y) (hYh : Y ≤ (ys.hi : ℝ)) :
    ((rawContext par ys ls r J Jcap cornerTheta).env 1).Mem (parentE lam Y) ∧
    ((rawContext par ys ls r J Jcap cornerTheta).env 2).Mem (msg lam Y) ∧
    ((rawContext par ys ls r J Jcap cornerTheta).env 18).Mem (lmass lam Y) ∧
    ((rawContext par ys ls r J Jcap cornerTheta).env 3).Mem (parentK lam Y) ∧
    ((rawContext par ys ls r J Jcap cornerTheta).env 4).Mem (parentTheta lam Y) := by
  obtain ⟨hpa, hpb⟩ := rawContext_point_safe par ys ls r J Jcap cornerTheta hs
  obtain ⟨he, hp, hphi, hk⟩ :=
    rawContext_four_primitives_mem par ys ls r J Jcap cornerTheta hpa hpb hl hh hYl hYh
  exact ⟨he, hp, hphi, hk,
    rawContext_theta_mem par ys ls r J Jcap cornerTheta hpa hpb hl hh hYl hYh
      (rawContext_corner_guards par ys ls r J Jcap cornerTheta hs)⟩

/-- Source: the direct exponential evaluation in Section `hand:var:set`. -/
theorem rawContext_Y_exp_mem (par : Parameters) (ys ls : Span)
    (r J Jcap : Rat) (cornerTheta : Bool) {Y : ℝ}
    (hYl : (ys.lo : ℝ) ≤ Y) (hYh : Y ≤ (ys.hi : ℝ)) :
    ((rawContext par ys ls r J Jcap cornerTheta).env 0).Mem Y ∧
      ((rawContext par ys ls r J Jcap cornerTheta).env 14).Mem (exp Y) :=
  ⟨ratSpan_mem hYl hYh, mem_expI (ratSpan_mem hYl hYh)⟩

/-- Source: `pp_of`; the specialized parent-variance entry contains the
actual `p(1-p)` throughout a safely retained rectangle. -/
theorem rawContext_parent_variance_mem (par : Parameters) (ys ls : Span)
    (r J Jcap : Rat) (cornerTheta : Bool) {lam Y : ℝ}
    (hs : (rawContext par ys ls r J Jcap cornerTheta).safe = true)
    (hl : (ls.lo : ℝ) ≤ lam) (hh : lam ≤ (ls.hi : ℝ))
    (hYl : (ys.lo : ℝ) ≤ Y) (hYh : Y ≤ (ys.hi : ℝ)) :
    ((rawContext par ys ls r J Jcap cornerTheta).env 24).Mem
      (msg lam Y * (1 - msg lam Y)) := by
  obtain ⟨_, hp, _, _, _⟩ :=
    rawContext_primitives_mem par ys ls r J Jcap cornerTheta hs hl hh hYl hYh
  exact parabolaRange_mem hp

/-- Source: the retained rational child coordinates and cap parameters. -/
theorem rawContext_constants_mem (par : Parameters) (ys ls : Span)
    (r J Jcap : Rat) (cornerTheta : Bool) :
    ((rawContext par ys ls r J Jcap cornerTheta).env 11).Mem (r : ℝ) ∧
    ((rawContext par ys ls r J Jcap cornerTheta).env 12).Mem (J : ℝ) ∧
    ((rawContext par ys ls r J Jcap cornerTheta).env 15).Mem (Jcap : ℝ) ∧
    ((rawContext par ys ls r J Jcap cornerTheta).env 23).Mem (par.D : ℝ) :=
  ⟨mem_ofRat r, mem_ofRat J, mem_ofRat Jcap, mem_ofRat par.D⟩

/-- Source: `mc:def:curve`; rational and real leaf occupation agree. -/
theorem qRat_cast (lam : Rat) : (qRat lam : ℝ) = actQ lam := by
  simp [qRat, actQ]

/-- Source: `mc:def:curve`; rational and real reserve multiplier agree. -/
theorem alphaRat_cast (par : Parameters) (lam : Rat) :
    (alphaRat par lam : ℝ) = alpha par.asBand lam := by
  simp [alphaRat, qRat_cast, alpha, Parameters.asBand]

/-- Source: `mc:def:curve`; rational and real reserve multiplier agree. -/
theorem gammaRat_cast (par : Parameters) (lam : Rat) :
    (gammaRat par lam : ℝ) = gamma par.asBand lam := by
  simp [gammaRat, gamma, Parameters.asBand]

/-- Source: `mc:def:curve`; rational and real reserve cap agree. -/
theorem capARat_cast (par : Parameters) (lam : Rat) :
    (capARat par lam : ℝ) = capA par.asBand lam := by
  simp [capARat, qRat_cast, capA, Parameters.asBand]

/-- Source: `tgt:lem:dmu`; the activity derivative of gamma. -/
noncomputable def gammaDot (par : Parameters) (lam : ℝ) : ℝ :=
  lam * (3+2*lam) / (par.g : ℝ)

/-- Source: `tgt:lem:dmu`; rational and real gamma derivative agree. -/
theorem gammaDotRat_cast (par : Parameters) (lam : Rat) :
    (gammaDotRat par lam : ℝ) = gammaDot par lam := by
  simp [gammaDotRat, gammaDot]

/-- Source: the endpoint multiplier intervals in `tgt:lem:tr`. -/
theorem alpha_mono (par : Parameters) {a b : ℝ}
    (hcoef : (0 : ℝ) ≤ par.a) (ha : 0 ≤ a) (hab : a ≤ b) :
    alpha par.asBand a ≤ alpha par.asBand b :=
  mul_le_mul_of_nonneg_left (actQ_mono ha hab) hcoef

/-- Source: the endpoint multiplier intervals in `tgt:lem:tr`. -/
theorem capA_mono (par : Parameters) {a b : ℝ}
    (hcoef : (1 : ℝ) ≤ par.D) (ha : 0 ≤ a) (hab : a ≤ b) :
    capA par.asBand a ≤ capA par.asBand b := by
  unfold capA
  have hcoef' : (0 : ℝ) ≤ (par.asBand.D : ℝ)-1 := by
    change (0 : ℝ) ≤ (par.D : ℝ)-1
    linarith
  exact add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (actQ_mono ha hab) hcoef')

/-- Source: the endpoint multiplier intervals in `tgt:lem:tr`. -/
theorem gamma_mono (par : Parameters) {a b : ℝ}
    (hg : (0 : ℝ) < par.g) (ha : 0 ≤ a) (hab : a ≤ b) :
    gamma par.asBand a ≤ gamma par.asBand b := by
  unfold gamma Parameters.asBand
  apply div_le_div_of_nonneg_right _ hg.le
  nlinarith [mul_nonneg (show 0 ≤ b-a by linarith) (show 0 ≤ 3+a+b by linarith)]

/-- Source: the endpoint activity-derivative intervals in `tgt:lem:dmu`. -/
theorem gammaDot_mono (par : Parameters) {a b : ℝ}
    (hg : (0 : ℝ) < par.g) (ha : 0 ≤ a) (hab : a ≤ b) :
    gammaDot par a ≤ gammaDot par b := by
  unfold gammaDot
  apply div_le_div_of_nonneg_right _ hg.le
  nlinarith [mul_nonneg (show 0 ≤ b-a by linarith) (show 0 ≤ 3+2*(a+b) by linarith)]

/-- Source: positive parameter and activity guards in the raw rectangle. -/
theorem rawContext_parameter_guards (par : Parameters) (ys ls : Span)
    (r J Jcap : Rat) (cornerTheta : Bool)
    (hs : (rawContext par ys ls r J Jcap cornerTheta).safe = true) :
    (0 : ℝ) < par.a ∧ (0 : ℝ) < par.g ∧ (1 : ℝ) ≤ par.D := by
  simp only [rawContext, Id.run, pure, Bool.and_eq_true, decide_eq_true_eq] at hs
  have ha : (0 : Rat) < par.a := by tauto
  have hg : (0 : Rat) < par.g := by tauto
  have hD : (1 : Rat) ≤ par.D := by tauto
  exact ⟨by exact_mod_cast ha, by exact_mod_cast hg, by exact_mod_cast hD⟩

/-- Source: `tgt:lem:tr` and `tgt:lem:dmu`; all four endpoint multiplier
entries contain their actual values at every activity in the rectangle. -/
theorem rawContext_multipliers_mem (par : Parameters) (ys ls : Span)
    (r J Jcap : Rat) (cornerTheta : Bool) {lam : ℝ}
    (hs : (rawContext par ys ls r J Jcap cornerTheta).safe = true)
    (hl : (ls.lo : ℝ) ≤ lam) (hh : lam ≤ (ls.hi : ℝ)) :
    ((rawContext par ys ls r J Jcap cornerTheta).env 5).Mem (alpha par.asBand lam) ∧
    ((rawContext par ys ls r J Jcap cornerTheta).env 6).Mem (gamma par.asBand lam) ∧
    ((rawContext par ys ls r J Jcap cornerTheta).env 7).Mem (capA par.asBand lam) ∧
    ((rawContext par ys ls r J Jcap cornerTheta).env 9).Mem (gammaDot par lam) := by
  obtain ⟨ha, hg, hD⟩ := rawContext_parameter_guards par ys ls r J Jcap cornerTheta hs
  obtain ⟨_, hpb⟩ := rawContext_point_safe par ys ls r J Jcap cornerTheta hs
  have hlo := point_activity_pos hpb
  have hlam := hlo.trans_le hl
  refine ⟨ratSpan_mem ?_ ?_, ratSpan_mem ?_ ?_, ratSpan_mem ?_ ?_, ratSpan_mem ?_ ?_⟩
  · rw [alphaRat_cast]; exact alpha_mono par ha.le hlo.le hl
  · rw [alphaRat_cast]; exact alpha_mono par ha.le hlam.le hh
  · rw [gammaRat_cast]; exact gamma_mono par hg hlo.le hl
  · rw [gammaRat_cast]; exact gamma_mono par hg hlam.le hh
  · rw [capARat_cast]; exact capA_mono par hD hlo.le hl
  · rw [capARat_cast]; exact capA_mono par hD hlam.le hh
  · rw [gammaDotRat_cast]; exact gammaDot_mono par hg hlo.le hl
  · rw [gammaDotRat_cast]; exact gammaDot_mono par hg hlam.le hh

/-- Source: `tgt:lem:tr`; direct q and positive-log interval entries. -/
theorem rawContext_activity_log_mem (par : Parameters) (ys ls : Span)
    (r J Jcap : Rat) (cornerTheta : Bool) {lam : ℝ}
    (hs : (rawContext par ys ls r J Jcap cornerTheta).safe = true)
    (hl : (ls.lo : ℝ) ≤ lam) (hh : lam ≤ (ls.hi : ℝ)) :
    ((rawContext par ys ls r J Jcap cornerTheta).env 21).Mem (actQ lam) ∧
    ((rawContext par ys ls r J Jcap cornerTheta).env 13).Mem (log lam) ∧
    ((rawContext par ys ls r J Jcap cornerTheta).env 22).Mem (log (1+lam)) := by
  obtain ⟨_, hpb⟩ := rawContext_point_safe par ys ls r J Jcap cornerTheta hs
  have hlo := point_activity_pos hpb
  have hlam := hlo.trans_le hl
  have hli : 0 < (ofRat ls.lo).lo := by
    change (decide (0 < (ofRat ls.lo).lo) && decide (0 <
      (add oneI (mul (ofRat ls.lo) (expI (ofRat (-ys.hi))))).lo) &&
      decide (0 < (logI (add oneI (mul (ofRat ls.lo) (expI (ofRat (-ys.hi)))))).lo)) = true at hpb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hpb
    exact hpb.1.1
  have hspan : (ratSpan ls.lo ls.hi).Mem lam := ratSpan_mem hl hh
  have hone : oneI.Mem (1 : ℝ) := by simpa only [oneI, toR_one] using mem_pt one
  have hden : 0 < (add oneI (ratSpan ls.lo ls.hi)).lo := by
    change 0 < one + (ofRat ls.lo).lo
    have ho : (0 : ℤ) < one := by decide
    omega
  refine ⟨ratSpan_mem ?_ ?_, mem_logI hspan hli, mem_logI (mem_add hone hspan) hden⟩
  · rw [qRat_cast]; exact actQ_mono hlo.le hl
  · rw [qRat_cast]; exact actQ_mono hlam.le hh

/-- Source: the activity-derivative interval guard in the mid script. -/
theorem rawContext_activity_side (par : Parameters) (ys ls : Span)
    (r J Jcap : Rat) (cornerTheta : Bool)
    (hs : (rawContext par ys ls r J Jcap cornerTheta).safe = true)
    (hc : cornerTheta = true) : (ls.hi : ℝ) ≤ 1 ∨ (1 : ℝ) ≤ ls.lo := by
  subst cornerTheta
  simp only [rawContext, Id.run, pure, Bool.and_eq_true, Bool.not_true,
    Bool.false_or, decide_eq_true_eq] at hs
  have h : ls.hi ≤ (1 : Rat) ∨ (1 : Rat) ≤ ls.lo := by tauto
  exact_mod_cast h

/-- Source: both exact activity-variance methods in the transport scripts. -/
theorem rawContext_activity_variance_mem (par : Parameters) (ys ls : Span)
    (r J Jcap : Rat) (cornerTheta : Bool) {lam : ℝ}
    (hs : (rawContext par ys ls r J Jcap cornerTheta).safe = true)
    (hl : (ls.lo : ℝ) ≤ lam) (hh : lam ≤ (ls.hi : ℝ)) :
    ((rawContext par ys ls r J Jcap cornerTheta).env 25).Mem (activityVariance lam) := by
  obtain ⟨_, hpb⟩ := rawContext_point_safe par ys ls r J Jcap cornerTheta hs
  have hlo := point_activity_pos hpb
  cases cornerTheta with
  | false =>
      obtain ⟨hlo', hhi'⟩ := activityVariance_natural_corners hlo hl hh
      apply ratSpan_mem
      · simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_add, Rat.cast_one] using hlo'
      · simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_add, Rat.cast_one] using hhi'
  | true =>
      obtain ⟨hlo', hhi'⟩ := activityVariance_endpoint_corners hlo hl hh
        (rawContext_activity_side par ys ls r J Jcap true hs rfl)
      have ha : (ofRat (ls.lo/(1+ls.lo)^2)).Mem (activityVariance (ls.lo : ℝ)) := by
        convert mem_ofRat (ls.lo/(1+ls.lo)^2) using 1
        norm_num [activityVariance]
      have hb : (ofRat (ls.hi/(1+ls.hi)^2)).Mem (activityVariance (ls.hi : ℝ)) := by
        convert mem_ofRat (ls.hi/(1+ls.hi)^2) using 1
        norm_num [activityVariance]
      change toR (min _ _) ≤ activityVariance lam ∧ activityVariance lam ≤ toR (max _ _)
      rw [toR_min, toR_max]
      exact ⟨(min_le_min ha.1 hb.1).trans hlo', hhi'.trans (max_le_max ha.2 hb.2)⟩

/-- Source: `tgt:lem:dmu`; derivative multiplier entries retain the actual
activity-variance enclosure, including activities crossing 1. -/
theorem rawContext_multiplier_derivatives_mem (par : Parameters) (ys ls : Span)
    (r J Jcap : Rat) (cornerTheta : Bool) {lam : ℝ}
    (hs : (rawContext par ys ls r J Jcap cornerTheta).safe = true)
    (hl : (ls.lo : ℝ) ≤ lam) (hh : lam ≤ (ls.hi : ℝ)) :
    ((rawContext par ys ls r J Jcap cornerTheta).env 8).Mem
      ((par.a : ℝ)*activityVariance lam) ∧
    ((rawContext par ys ls r J Jcap cornerTheta).env 10).Mem
      (((par.D : ℝ)-1)*activityVariance lam) := by
  have hqq := rawContext_activity_variance_mem par ys ls r J Jcap cornerTheta hs hl hh
  refine ⟨mem_mul (mem_ofRat par.a) hqq, ?_⟩
  exact mem_mul (by simpa using mem_ofRat (par.D-1)) hqq

/-- Source: the retained real environment of Appendix N.4's formulas.
Polygon slope and intercept are zero until the caller supplies its line. -/
noncomputable def realEnv (par : Parameters) (lam Y r J Jcap : ℝ) : Nat → ℝ
  | 0 => Y
  | 1 => parentE lam Y
  | 2 => msg lam Y
  | 3 => parentK lam Y
  | 4 => parentTheta lam Y
  | 5 => alpha par.asBand lam
  | 6 => gamma par.asBand lam
  | 7 => capA par.asBand lam
  | 8 => (par.a : ℝ) * activityVariance lam
  | 9 => gammaDot par lam
  | 10 => ((par.D : ℝ)-1) * activityVariance lam
  | 11 => r
  | 12 => J
  | 13 => log lam
  | 14 => exp Y
  | 15 => Jcap
  | 16 => lBar par.asBand lam Y
  | 17 => lPrime par.asBand lam Y
  | 18 => lmass lam Y
  | 21 => actQ lam
  | 22 => log (1+lam)
  | 23 => (par.D : ℝ)
  | 24 => msg lam Y * (1-msg lam Y)
  | 25 => activityVariance lam
  | _ => 0

/-- Source: `tgt:lem:dY`; direct interval formulas for h and h′ contain
the actual normalized reserve values over the retained rectangle. -/
theorem rawContext_h_jets_mem (par : Parameters) (ys ls : Span)
    (r J Jcap : Rat) (cornerTheta : Bool) {lam Y : ℝ}
    (hs : (rawContext par ys ls r J Jcap cornerTheta).safe = true)
    (hl : (ls.lo : ℝ) ≤ lam) (hh : lam ≤ (ls.hi : ℝ))
    (hYl : (ys.lo : ℝ) ≤ Y) (hYh : Y ≤ (ys.hi : ℝ)) :
    (fh.evalI (rawContext par ys ls r J Jcap cornerTheta).env).Mem (hHat par.asBand lam Y) ∧
    (fhp.evalI (rawContext par ys ls r J Jcap cornerTheta).env).Mem (hPrime par.asBand lam Y) ∧
    (fhpp.evalI (rawContext par ys ls r J Jcap cornerTheta).env).Mem (hSecond par.asBand lam Y) := by
  obtain ⟨_, hp, _, hk, hw⟩ :=
    rawContext_primitives_mem par ys ls r J Jcap cornerTheta hs hl hh hYl hYh
  obtain ⟨_, hg, _, _⟩ := rawContext_multipliers_mem par ys ls r J Jcap cornerTheta hs hl hh
  have hpp := rawContext_parent_variance_mem par ys ls r J Jcap cornerTheta hs hl hh hYl hYh
  have hone : (ofRat 1).Mem (1 : ℝ) := by simpa using mem_ofRat 1
  have htwo : (ofRat 2).Mem (2 : ℝ) := by simpa using mem_ofRat 2
  refine ⟨?_, ?_, ?_⟩
  · simpa [fh, fp, fg, fk, Expr.evalI, hHat, Reserve.Cert.hF, parentK] using
      mem_add (mem_sub hone hp) (mem_mul hg hk)
  · simpa [fhp, fpp, fg, fk, fw, Expr.evalI, hPrime] using
      mem_add hpp (mem_mul (mem_mul hg hk) hw)
  · simpa [fhpp, fpp, fp, fg, fk, fw, Expr.evalI, hSecond] using
      mem_add (mem_mul (mem_neg hpp) (mem_sub hone (mem_mul htwo hp)))
        (mem_mul (mem_mul hg hk)
          (mem_sub (mem_add (Reserve.Cert.mem_sqI hw) (mem_mul hk hw)) hpp))

/-- Source: `tgt:lem:dY`; the direct L and L′ entries and the explicit L″
formula enclose the actual derivatives, without a mean-value assumption. -/
theorem rawContext_l_jets_mem (par : Parameters) (ys ls : Span)
    (r J Jcap : Rat) (cornerTheta : Bool) {lam Y : ℝ}
    (hs : (rawContext par ys ls r J Jcap cornerTheta).safe = true)
    (hl : (ls.lo : ℝ) ≤ lam) (hh : lam ≤ (ls.hi : ℝ))
    (hYl : (ys.lo : ℝ) ≤ Y) (hYh : Y ≤ (ys.hi : ℝ)) :
    ((rawContext par ys ls r J Jcap cornerTheta).env 16).Mem (lBar par.asBand lam Y) ∧
    ((rawContext par ys ls r J Jcap cornerTheta).env 17).Mem (lPrime par.asBand lam Y) ∧
    (fLpp.evalI (rawContext par ys ls r J Jcap cornerTheta).env).Mem (lSecond par.asBand lam Y) := by
  obtain ⟨he, _, _, _, _⟩ :=
    rawContext_primitives_mem par ys ls r J Jcap cornerTheta hs hl hh hYl hYh
  obtain ⟨hY, _⟩ := rawContext_Y_exp_mem par ys ls r J Jcap cornerTheta hYl hYh
  obtain ⟨_, hg, _, _⟩ := rawContext_multipliers_mem par ys ls r J Jcap cornerTheta hs hl hh
  obtain ⟨hh', hhp, hhpp⟩ :=
    rawContext_h_jets_mem par ys ls r J Jcap cornerTheta hs hl hh hYl hYh
  have htwo : (ofRat 2).Mem (2 : ℝ) := by simpa using mem_ofRat 2
  refine ⟨?_, ?_, ?_⟩
  · simpa [fLdirect, fg, fe, fY, Expr.evalI, lBar] using
      mem_sub (mem_mul hg he) (mem_mul hh' hY)
  · simpa [fLpdirect, fg, fe, fY, Expr.evalI, lPrime] using
      mem_sub (mem_sub (mem_mul hg he) hh') (mem_mul hhp hY)
  · simpa [fLpp, fg, fe, fY, Expr.evalI, lSecond] using
      mem_sub (mem_sub (mem_mul hg he) (mem_mul htwo hhp)) (mem_mul hhpp hY)

/-- Source: `tgt:lem:tr` and `tgt:lem:dY`; every entry of the safely
evaluated raw environment encloses its actual parent/child value. -/
theorem rawContext_mem (par : Parameters) (ys ls : Span)
    (r J Jcap : Rat) (cornerTheta : Bool) {lam Y : ℝ}
    (hs : (rawContext par ys ls r J Jcap cornerTheta).safe = true)
    (hl : (ls.lo : ℝ) ≤ lam) (hh : lam ≤ (ls.hi : ℝ))
    (hYl : (ys.lo : ℝ) ≤ Y) (hYh : Y ≤ (ys.hi : ℝ)) :
    ∀ i, ((rawContext par ys ls r J Jcap cornerTheta).env i).Mem
      (realEnv par lam Y r J Jcap i) := by
  obtain ⟨he, hp, hphi, hk, hw⟩ :=
    rawContext_primitives_mem par ys ls r J Jcap cornerTheta hs hl hh hYl hYh
  obtain ⟨hY, hexp⟩ := rawContext_Y_exp_mem par ys ls r J Jcap cornerTheta hYl hYh
  obtain ⟨ha, hg, hAD, hgd⟩ := rawContext_multipliers_mem par ys ls r J Jcap cornerTheta hs hl hh
  obtain ⟨had, hADd⟩ := rawContext_multiplier_derivatives_mem par ys ls r J Jcap cornerTheta hs hl hh
  obtain ⟨hq, hmu, hbarphi⟩ := rawContext_activity_log_mem par ys ls r J Jcap cornerTheta hs hl hh
  obtain ⟨hr, hJ, hJcap, hD⟩ := rawContext_constants_mem par ys ls r J Jcap cornerTheta
  obtain ⟨hL, hLp, _⟩ := rawContext_l_jets_mem par ys ls r J Jcap cornerTheta hs hl hh hYl hYh
  have hpp := rawContext_parent_variance_mem par ys ls r J Jcap cornerTheta hs hl hh hYl hYh
  have hqq := rawContext_activity_variance_mem par ys ls r J Jcap cornerTheta hs hl hh
  have hz : zeroI.Mem (0 : ℝ) := by simpa only [zeroI, toR_zero] using mem_pt 0
  intro i
  by_cases hi : i < 26
  · interval_cases i <;> assumption
  · have hi' : 26 ≤ i := by omega
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hi'
    simpa only [Nat.add_succ, Nat.add_zero] using hz

/-- Source: `tfun.phi2_piece`; the mean-value enclosure consumes a named
derivative and its uniform interval enclosure on the same retained segment. -/
theorem meanValue_enclosure_mem (ys : Span) {f f' : ℝ → ℝ} {C D : Ival} {x : ℝ}
    (hx : (ys.lo : ℝ) ≤ x ∧ x ≤ (ys.hi : ℝ))
    (hderiv : ∀ t ∈ Set.Icc (ys.lo : ℝ) (ys.hi : ℝ), HasDerivAt f (f' t) t)
    (hD : ∀ t ∈ Set.Icc (ys.lo : ℝ) (ys.hi : ℝ), D.Mem (f' t))
    (hC : C.Mem (f (((ys.lo+ys.hi)/2 : Rat) : ℝ))) :
    (add C (mul (ratSpan (-((ys.hi-ys.lo)/2)) ((ys.hi-ys.lo)/2)) D)).Mem (f x) := by
  let c : ℝ := (((ys.lo+ys.hi)/2 : Rat) : ℝ)
  let rad : ℝ := (((ys.hi-ys.lo)/2 : Rat) : ℝ)
  have hcval : c = ((ys.lo : ℝ)+(ys.hi : ℝ))/2 := by simp [c]
  have hrval : rad = ((ys.hi : ℝ)-(ys.lo : ℝ))/2 := by simp [rad]
  have hc : c ∈ Set.Icc (ys.lo : ℝ) (ys.hi : ℝ) := by
    rw [Set.mem_Icc, hcval]
    constructor <;> linarith [hx.1, hx.2]
  have hdelta : (ratSpan (-((ys.hi-ys.lo)/2)) ((ys.hi-ys.lo)/2)).Mem (x-c) := by
    apply ratSpan_mem
    · rw [Rat.cast_neg]
      change -rad ≤ x-c
      rw [hcval, hrval]
      linarith [hx.1]
    · change x-c ≤ rad
      rw [hcval, hrval]
      linarith [hx.2]
  have hcont : ∀ a b, Set.Icc a b ⊆ Set.Icc (ys.lo : ℝ) (ys.hi : ℝ) →
      ContinuousOn f (Set.Icc a b) := by
    intro a b hsub t ht
    exact (hderiv t (hsub ht)).continuousAt.continuousWithinAt
  by_cases hxc : x = c
  · have h := mem_add hC (mem_mul hdelta (hD c hc))
    simpa only [hxc, sub_self, zero_mul, add_zero] using h
  · rcases lt_or_gt_of_ne hxc with hxc | hcx
    · have hsub : Set.Icc x c ⊆ Set.Icc (ys.lo : ℝ) (ys.hi : ℝ) := by
        intro t ht
        exact ⟨hx.1.trans ht.1, ht.2.trans hc.2⟩
      obtain ⟨t, ht, heq⟩ := exists_hasDerivAt_eq_slope f f' hxc
        (hcont x c hsub) (fun t ht => hderiv t (hsub ⟨ht.1.le, ht.2.le⟩))
      have htm : t ∈ Set.Icc (ys.lo : ℝ) (ys.hi : ℝ) := hsub ⟨ht.1.le, ht.2.le⟩
      have heq' : f x = f c + (x-c)*f' t := by
        have hm := (eq_div_iff (sub_ne_zero.mpr hxc.ne')).mp heq
        nlinarith
      rw [heq']
      exact mem_add hC (mem_mul hdelta (hD t htm))
    · have hsub : Set.Icc c x ⊆ Set.Icc (ys.lo : ℝ) (ys.hi : ℝ) := by
        intro t ht
        exact ⟨hc.1.trans ht.1, ht.2.trans hx.2⟩
      obtain ⟨t, ht, heq⟩ := exists_hasDerivAt_eq_slope f f' hcx
        (hcont c x hsub) (fun t ht => hderiv t (hsub ⟨ht.1.le, ht.2.le⟩))
      have htm : t ∈ Set.Icc (ys.lo : ℝ) (ys.hi : ℝ) := hsub ⟨ht.1.le, ht.2.le⟩
      have heq' : f x = f c + (x-c)*f' t := by
        have hm := (eq_div_iff (sub_ne_zero.mpr hcx.ne')).mp heq
        nlinarith
      rw [heq']
      exact mem_add hC (mem_mul hdelta (hD t htm))

/-- Source: `tfun.phi2_piece`; both mean-value intersections consume the
actual L′ and L″ functions. L′ is first tightened uniformly using L″;
that retained tightened enclosure is then used to tighten L. -/
theorem context_mem (par : Parameters) (ys ls : Span)
    (r J Jcap : Rat) (midMethod : Bool) {lam Y : ℝ}
    (hs : (context par ys ls r J Jcap midMethod).safe = true)
    (hl : (ls.lo : ℝ) ≤ lam) (hh : lam ≤ (ls.hi : ℝ))
    (hYl : (ys.lo : ℝ) ≤ Y) (hYh : Y ≤ (ys.hi : ℝ)) :
    ∀ i, ((context par ys ls r J Jcap midMethod).env i).Mem
      (realEnv par lam Y r J Jcap i) := by
  cases midMethod with
  | true => exact rawContext_mem par ys ls r J Jcap true hs hl hh hYl hYh
  | false =>
      let raw := rawContext par ys ls r J Jcap false
      let center : Rat := (ys.lo+ys.hi)/2
      let radius : Rat := (ys.hi-ys.lo)/2
      let atCenter := rawContext par ⟨center,center⟩ ls r J Jcap false
      let delta := ratSpan (-radius) radius
      let lp := intersection (raw.env 17)
        (add (atCenter.env 17) (mul delta (fLpp.evalI raw.env)))
      let l := intersection (raw.env 16) (add (atCenter.env 16) (mul delta lp))
      change (raw.safe && atCenter.safe && fLpp.safe raw.env &&
        decide (l.lo ≤ l.hi) && decide (lp.lo ≤ lp.hi)) = true at hs
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
      have hraw : raw.safe = true := hs.1.1.1.1
      have hcenter : atCenter.safe = true := hs.1.1.1.2
      have hcv : (center : ℝ) = ((ys.lo : ℝ)+(ys.hi : ℝ))/2 := by simp [center]
      have hcl : (ys.lo : ℝ) ≤ center := by rw [hcv]; linarith
      have hch : (center : ℝ) ≤ ys.hi := by rw [hcv]; linarith
      obtain ⟨_, hpb⟩ := rawContext_point_safe par ys ls r J Jcap false hraw
      have hlam : 0 < lam := (point_activity_pos hpb).trans_le hl
      have hbase := rawContext_mem par ys ls r J Jcap false hraw hl hh hYl hYh
      obtain ⟨hLc, hLpc, _⟩ := rawContext_l_jets_mem par ⟨center,center⟩ ls
        r J Jcap false hcenter hl hh (Y := (center : ℝ)) le_rfl le_rfl
      have hlp : ∀ t ∈ Set.Icc (ys.lo : ℝ) (ys.hi : ℝ), lp.Mem (lPrime par.asBand lam t) := by
        intro t ht
        obtain ⟨_, hLp, hLpp⟩ := rawContext_l_jets_mem par ys ls
          r J Jcap false hraw hl hh ht.1 ht.2
        apply intersection_mem hLp
        exact meanValue_enclosure_mem ys (f := lPrime par.asBand lam)
          (f' := lSecond par.asBand lam) (x := t) ht
          (fun x _ => hasDerivAt_lPrime_Y par.asBand hlam)
          (fun x hx => (rawContext_l_jets_mem par ys ls r J Jcap false
            hraw hl hh hx.1 hx.2).2.2) hLpc
      have hlbar : l.Mem (lBar par.asBand lam Y) := by
        apply intersection_mem (hbase 16)
        exact meanValue_enclosure_mem ys (f := lBar par.asBand lam)
          (f' := lPrime par.asBand lam) (x := Y) ⟨hYl,hYh⟩
          (fun x _ => hasDerivAt_lBar_Y par.asBand hlam) hlp hLc
      intro i
      by_cases hi16 : i = 16
      · subst i; exact hlbar
      · by_cases hi17 : i = 17
        · subst i; exact hlp Y ⟨hYl,hYh⟩
        · simpa [context, raw, center, radius, atCenter, delta, lp, l,
            hi16, hi17] using hbase i

/-- Source: Appendix N.4's formula evaluation in each retained rectangle;
the exact checker value encloses the actual formula when evaluation succeeds. -/
theorem eval_context_mem (par : Parameters) (ys ls : Span)
    (r J Jcap : Rat) (midMethod : Bool) (e : Expr) {v : Ival} {lam Y : ℝ}
    (heval : eval (context par ys ls r J Jcap midMethod) e = some v)
    (hl : (ls.lo : ℝ) ≤ lam) (hh : lam ≤ (ls.hi : ℝ))
    (hYl : (ys.lo : ℝ) ≤ Y) (hYh : Y ≤ (ys.hi : ℝ)) :
    v.Mem (e.evalR (realEnv par lam Y r J Jcap)) := by
  unfold eval at heval
  split_ifs at heval with hs
  · simp only [Bool.and_eq_true] at hs
    cases Option.some.inj heval
    exact e.evalI_mem (context_mem par ys ls r J Jcap midMethod hs.1 hl hh hYl hYh) hs.2

/-- Source: the child-polygon paragraph after `tgt:lem:poly`; replacing
the retained line entries preserves the actual rational slope/intercept. -/
theorem override_line_mem {env : Nat → Ival} {values : Nat → ℝ}
    (h : ∀ i, (env i).Mem (values i)) (slope intercept : Rat) :
    ∀ i, (if i == 19 then ofRat slope else if i == 20 then ofRat intercept else env i).Mem
      (if i == 19 then (slope : ℝ) else if i == 20 then (intercept : ℝ) else values i) := by
  intro i
  split_ifs <;> first | exact mem_ofRat slope | exact mem_ofRat intercept | exact h i

end Erdos993Lean.Analytic.HandVariance.Compute
