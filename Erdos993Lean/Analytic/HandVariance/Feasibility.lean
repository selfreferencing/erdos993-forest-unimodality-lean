import Erdos993Lean.Analytic.HandVariance.Normalized
import Erdos993Lean.Analytic.Reserve.AnalyticBounds
import Erdos993Lean.Analytic.Reserve.StepBand

/-!
# Hand variance: consequences of an actual feasible parent/child pair

Source: `ProofRuns/2026-09-28_analytic_large_n/LEAN/for_tong/TWIN_v1.8/apx_hand.tex`,
Appendix N.4, Lemma `tgt:lem:feas` (a,b) and Lemma `tgt:lem:cut`.
The activity and the actual parent/child log-masses are retained. These results
do not provide a child polygon or any finite interval certificate.
-/

namespace Erdos993Lean.Analytic.HandVariance

open Real Reserve

/-- Source: Appendix N.4, Lemma `tgt:lem:feas` (a); the lower entropy function
`E₋(Y)`, using the parent's normalized coordinates. -/
noncomputable def eMinus (lam Y : ℝ) : ℝ :=
  parentE lam Y + (log lam - log (exp Y - 1) - 1 / parentK lam Y) / Y

/-- Source: Appendix N.4, Lemma `tgt:lem:feas` (b); the lower CA function
`C(Y)` with the child polygon's cap retained as a parameter. -/
noncomputable def cLower (c : Band) (lam Y Jcap : ℝ) : ℝ :=
  alpha c lam * eMinus lam Y -
    gamma c lam * (-lBar c lam Y) / (gamma c lam - Jcap * (-lBar c lam Y))

/-- Source: Appendix N.4, feasible-pair definition in `hand:var:set`.
Positive activity and the mass comparison imply positive parent log-mass. -/
theorem feasible_parent_pos {lam T Y : ℝ} (hlam : 0 < lam)
    (hTY : lmass lam T ≤ Y) : 0 < Y :=
  lt_of_lt_of_le (Reserve.Cert.lmass_pos (X := T) hlam) hTY

/-- Source: Appendix N.4, Lemma `tgt:lem:feas` (a), first comparison:
`r = T/φ ≥ T/Y` at the actual child. -/
theorem childR_ge_div_parent {lam T Y : ℝ} (hlam : 0 < lam)
    (hT : 0 ≤ T) (hTY : lmass lam T ≤ Y) : T / Y ≤ childR lam T := by
  unfold childR
  exact div_le_div_of_nonneg_left hT (Reserve.Cert.lmass_pos (X := T) hlam) hTY

/-- Source: Appendix N.4, Lemma `tgt:lem:feas` (a), second comparison:
feasibility implies `T ≥ log λ - log(exp Y - 1)`. -/
theorem feasible_child_log_lower {lam T Y : ℝ} (hlam : 0 < lam)
    (hTY : lmass lam T ≤ Y) : log lam - log (exp Y - 1) ≤ T := by
  have hu : 0 < lam * exp (-T) := mul_pos hlam (exp_pos (-T))
  have harg : 0 < 1 + lam * exp (-T) := by linarith
  have he : 1 + lam * exp (-T) ≤ exp Y := by
    apply (Real.log_le_iff_le_exp harg).mp
    exact hTY
  have hlog := Real.log_le_log hu (show lam * exp (-T) ≤ exp Y - 1 by linarith)
  rw [Real.log_mul hlam.ne' (Real.exp_ne_zero (-T)), Real.log_exp] at hlog
  linarith

/-- Source: Appendix N.4, Lemma `tgt:lem:feas` (a), its entropy conclusion,
using the exact reserve entropy normalization at the actual feasible child. -/
theorem coefE_div_msg_ge_eMinus {lam T Y : ℝ} (hlam : 0 < lam)
    (hT : 0 ≤ T) (hTY : lmass lam T ≤ Y) :
    eMinus lam Y ≤ coefE lam T Y / msg lam Y := by
  have hY := feasible_parent_pos hlam hTY
  have hr := childR_ge_div_parent hlam hT hTY
  have ht := div_le_div_of_nonneg_right (feasible_child_log_lower hlam hTY) hY.le
  rw [coefE_div_msg hlam T hY]
  unfold eMinus
  rw [sub_div, div_div]
  linarith

/-- Source: Appendix N.4, Lemma `tgt:lem:feas` (b); the positive cap
denominator also certifies the denominator at the actual child. -/
theorem zBar_pos_of_negative_lBar_cap {c : Band} {lam T Y Jcap : ℝ}
    (hL : lBar c lam Y < 0) (hJ : coefJ lam T ≤ Jcap)
    (hcap : 0 < gamma c lam - Jcap * (-lBar c lam Y)) :
    0 < zBar c lam Y (coefJ lam T) := by
  have hprod := mul_le_mul_of_nonpos_right hJ hL.le
  unfold zBar
  linarith

/-- Source: Appendix N.4, Lemma `tgt:lem:feas` (b), the normalized CA lower
bound. The multiplier signs are explicit; every source segment supplies them.
The child message/mass ratio is the actual one and is bounded by the existing
`Reserve.Tails` lemmas. -/
theorem compC_div_msg_ge_cLower
    {c : Band} {lam T Y Jcap : ℝ} (hlam : 0 < lam)
    (hT : 0 ≤ T) (hTY : lmass lam T ≤ Y)
    (hα : 0 ≤ alpha c lam) (hγ : 0 ≤ gamma c lam)
    (hL : lBar c lam Y < 0) (hJ : coefJ lam T ≤ Jcap)
    (hcap : 0 < gamma c lam - Jcap * (-lBar c lam Y)) :
    cLower c lam Y Jcap ≤ compC c lam T Y / msg lam Y := by
  have hY := feasible_parent_pos hlam hTY
  have hz := zBar_pos_of_negative_lBar_cap hL hJ hcap
  have hE := mul_le_mul_of_nonneg_left (coefE_div_msg_ge_eMinus hlam hT hTY) hα
  rw [coefE_div_msg hlam T hY] at hE
  have hratio0 := Tails.msg_div_lmass_nonneg hlam T
  have hratio1 := Tails.msg_div_lmass_le_one hlam T
  have hsq : (msg lam T / lmass lam T) ^ 2 ≤ 1 := pow_le_one₀ hratio0 hratio1
  have hnum : 0 ≤ gamma c lam * (-lBar c lam Y) :=
    mul_nonneg hγ (neg_nonneg.mpr hL.le)
  have hden : gamma c lam - Jcap * (-lBar c lam Y) ≤
      zBar c lam Y (coefJ lam T) := by
    have hprod := mul_le_mul_of_nonpos_right hJ hL.le
    unfold zBar
    linarith
  have hfrac := div_le_div_of_nonneg_left hnum hcap hden
  have hsqnum := mul_le_mul_of_nonneg_left hsq hnum
  have hsqfrac := div_le_div_of_nonneg_right hsqnum hz.le
  have hsqfrac' : gamma c lam * (-lBar c lam Y) * (msg lam T / lmass lam T) ^ 2 /
      zBar c lam Y (coefJ lam T) ≤
      gamma c lam * (-lBar c lam Y) / zBar c lam Y (coefJ lam T) := by
    simpa only [mul_one] using hsqfrac
  have hloss : gamma c lam * (-lBar c lam Y) * (msg lam T / lmass lam T) ^ 2 /
      zBar c lam Y (coefJ lam T) ≤
      gamma c lam * (-lBar c lam Y) / (gamma c lam - Jcap * (-lBar c lam Y)) := by
    exact hsqfrac'.trans hfrac
  rw [compC_div_msg c hlam T hY hz.ne']
  unfold cLower
  have hsign : gamma c lam * lBar c lam Y * (msg lam T / lmass lam T) ^ 2 /
      zBar c lam Y (coefJ lam T) =
      -(gamma c lam * (-lBar c lam Y) * (msg lam T / lmass lam T) ^ 2 /
        zBar c lam Y (coefJ lam T)) := by ring
  rw [hsign]
  linarith

/-- Source: Appendix N.4, Lemma `tgt:lem:feas` (b), for the multipliers of
every source segment; their signs are proved by `segment_bandSide`. -/
theorem segment_compC_div_msg_ge_cLower
    (s : Segment) {lam T Y Jcap : ℝ} (hlam : 0 < lam)
    (hT : 0 ≤ T) (hTY : lmass lam T ≤ Y)
    (hL : lBar s.band lam Y < 0) (hJ : coefJ lam T ≤ Jcap)
    (hcap : 0 < gamma s.band lam - Jcap * (-lBar s.band lam Y)) :
    cLower s.band lam Y Jcap ≤ compC s.band lam T Y / msg lam Y := by
  exact compC_div_msg_ge_cLower hlam hT hTY
    ((segment_bandSide s).alpha_pos hlam).le ((segment_bandSide s).gamma_pos hlam).le
    hL hJ hcap

/-- Source: Appendix N.4, Lemma `tgt:lem:cut`; the feasibility cut with the
actual activity, actual child coordinate and an upper parent log-mass endpoint. -/
theorem childR_ge_feasibility_cut {lam lo T Y Y1 : ℝ}
    (hlo : 0 < lo) (hlam : lo ≤ lam) (hT : 0 ≤ T)
    (hTY : lmass lam T ≤ Y) (hY1 : Y ≤ Y1) :
    max 0 (log lo - log (exp Y1 - 1)) / Y1 ≤ childR lam T := by
  have hlampos : 0 < lam := lt_of_lt_of_le hlo hlam
  have hY := feasible_parent_pos hlampos hTY
  have hY1pos : 0 < Y1 := lt_of_lt_of_le hY hY1
  have hexpY : 0 < exp Y - 1 := by linarith [Real.one_lt_exp_iff.mpr hY]
  have hlogLam := Real.log_le_log hlo hlam
  have hlogY := Real.log_le_log hexpY
    (show exp Y - 1 ≤ exp Y1 - 1 by linarith [Real.exp_le_exp.mpr hY1])
  have htLower := feasible_child_log_lower hlampos hTY
  have htCut : log lo - log (exp Y1 - 1) ≤ T := by linarith
  have hmax : max 0 (log lo - log (exp Y1 - 1)) ≤ T := max_le hT htCut
  have hmaxDiv := div_le_div_of_nonneg_right hmax hY1pos.le
  have hTDiv : T / Y1 ≤ T / Y := div_le_div_of_nonneg_left hT hY hY1
  exact hmaxDiv.trans (hTDiv.trans (childR_ge_div_parent hlampos hT hTY))

end Erdos993Lean.Analytic.HandVariance

#print axioms Erdos993Lean.Analytic.HandVariance.coefE_div_msg_ge_eMinus
#print axioms Erdos993Lean.Analytic.HandVariance.segment_compC_div_msg_ge_cLower
#print axioms Erdos993Lean.Analytic.HandVariance.childR_ge_feasibility_cut
