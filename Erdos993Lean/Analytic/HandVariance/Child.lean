import Erdos993Lean.Analytic.HandVariance.Calculus
import Erdos993Lean.Analytic.HandVariance.Normalized

/-!
# Child curve monotonicity and polygon transport

Source: `for_tong/TWIN_v1.8/apx_hand.tex`, Lemmas `tgt:lem:child`
and `tgt:lem:poly`. The child log-mass and activity are retained in every
comparison. The finite-chain condition includes the final infinite segment,
where the message at infinity is zero.
-/

namespace Erdos993Lean.Analytic.HandVariance

open Real Reserve

/-- Source: the child paragraph following `tgt:lem:poly`; `r` increases in
child log-mass on the physical half-line. -/
theorem childR_monotoneOn {lam : ℝ} (hlam : 0 < lam) :
    MonotoneOn (childR lam) (Set.Ici 0) := by
  intro T hT T' hT' hTT'
  unfold childR
  calc
    T / lmass lam T ≤ T / lmass lam T' :=
      div_le_div_of_nonneg_left hT (Reserve.lmass_pos hlam T')
        (Reserve.Cert.lmass_anti hlam.le hTT')
    _ ≤ T' / lmass lam T' :=
      div_le_div_of_nonneg_right hTT' (Reserve.lmass_pos hlam T').le

/-- Source: `tgt:lem:child` (a); increasing activity increases child mass. -/
theorem lmass_monotone_activity {lam lam' T : ℝ} (hlam : 0 < lam)
    (hll : lam ≤ lam') : lmass lam T ≤ lmass lam' T := by
  unfold lmass
  apply Real.log_le_log (by positivity)
  exact add_le_add (le_refl 1)
    (mul_le_mul_of_nonneg_right hll (exp_pos (-T)).le)

/-- Source: `tgt:lem:child` (a); the actual child coordinate decreases
with activity. -/
theorem childR_antitone_activity {lam lam' T : ℝ} (hlam : 0 < lam)
    (hll : lam ≤ lam') (hT : 0 ≤ T) : childR lam' T ≤ childR lam T := by
  unfold childR
  exact div_le_div_of_nonneg_left hT (Reserve.lmass_pos hlam T)
    (lmass_monotone_activity hlam hll)

/-- Exact analytic endpoint used in the child activity derivative. This uses
Mathlib's Taylor remainder bound, with no native computation. -/
theorem exp_five_fourths_lt : exp (5 / 4 : ℝ) < 7 / 2 := by
  have hquarter : exp (1 / 4 : ℝ) ≤ (394453 / 307200 : ℝ) := by
    have h := Real.exp_bound' (x := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
      (n := 5) (by norm_num)
    refine h.trans (le_of_eq ?_)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have heq : exp (5 / 4 : ℝ) = exp (1 / 4 : ℝ) ^ 5 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  rw [heq]
  calc
    exp (1 / 4 : ℝ) ^ 5 ≤ (394453 / 307200 : ℝ) ^ 5 :=
      pow_le_pow_left₀ (exp_pos _).le hquarter 5
    _ < 7 / 2 := by norm_num

/-- Source: `tgt:lem:child` (a), positivity of its activity logarithmic
numerator. Concavity of log interpolates the exact upper endpoint. -/
theorem two_log_one_add_gt {z : ℝ} (hz : 0 < z) (hzhi : z ≤ 5 / 2) :
    z < 2 * log (1 + z) := by
  have hend : (5 / 4 : ℝ) < log (7 / 2 : ℝ) :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2 exp_five_fourths_lt
  have hw : 0 < z / (5 / 2 : ℝ) := by positivity
  have hconc := strictConcaveOn_log_Ioi.concaveOn.2
    (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show (7 / 2 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show 0 ≤ 1 - z / (5 / 2 : ℝ) by linarith)
    hw.le (by ring : 1 - z / (5 / 2 : ℝ) + z / (5 / 2 : ℝ) = 1)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add, mul_one] at hconc
  have harg : 1 - z / (5 / 2 : ℝ) + z / (5 / 2 : ℝ) * (7 / 2 : ℝ) = 1 + z := by ring
  rw [harg] at hconc
  have hstrict := mul_lt_mul_of_pos_left hend hw
  nlinarith

/-- Source: `tgt:lem:child` (a), the activity kernel `p²/φ`. -/
noncomputable def childActivityKernel (z : ℝ) : ℝ :=
  (z / (1 + z)) ^ 2 / log (1 + z)

/-- Source: `tgt:lem:child` (a), its activity derivative in the `z` coordinate. -/
theorem hasDerivAt_childActivityKernel {z : ℝ} (hz : 0 < z) :
    HasDerivAt childActivityKernel
      (z * (2 * log (1 + z) - z) / ((1 + z) ^ 3 * log (1 + z) ^ 2)) z := by
  have hd : 1 + z ≠ 0 := by positivity
  have hl : log (1 + z) ≠ 0 := (Real.log_pos (by linarith : 1 < 1 + z)).ne'
  have hdplus := (hasDerivAt_const z (1 : ℝ)).add (hasDerivAt_id z)
  have hq := (hasDerivAt_id z).div hdplus hd
  have h := (hq.pow 2).div (hdplus.log hd) hl
  convert h using 1
  dsimp
  field_simp [hd, hl]
  ring

/-- Source: `tgt:lem:child` (a); the activity kernel increases through `5/2`. -/
theorem childActivityKernel_monotoneOn :
    MonotoneOn childActivityKernel (Set.Ioc 0 (5 / 2)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 (5 / 2))
  · intro z hz
    exact (hasDerivAt_childActivityKernel hz.1).continuousAt.continuousWithinAt
  · intro z hz
    exact (hasDerivAt_childActivityKernel (interior_subset hz).1).differentiableAt.differentiableWithinAt
  · intro z hz
    have hzD := interior_subset hz
    rw [(hasDerivAt_childActivityKernel hzD.1).deriv]
    have hnum : 0 < 2 * log (1 + z) - z := by
      linarith [two_log_one_add_gt hzD.1 hzD.2]
    have hlog : 0 < log (1 + z) := Real.log_pos (by linarith [hzD.1])
    have hone : 0 < 1 + z := by linarith [hzD.1]
    exact (div_pos (mul_pos hzD.1 hnum)
      (mul_pos (pow_pos hone 3) (sq_pos_of_pos hlog))).le

/-- Source: `tgt:lem:child` (a), the exact kernel factorization of `J`. -/
theorem coefJ_eq_activityKernel (lam T : ℝ) :
    coefJ lam T = T * childActivityKernel (lam * exp (-T)) := by
  unfold coefJ childActivityKernel msg lmass
  ring

/-- Source: `tgt:lem:child` (a); `J` increases with activity on the stated
physical domain. -/
theorem coefJ_monotone_activity {lam lam' T : ℝ} (hlam : 0 < lam)
    (hll : lam ≤ lam') (hlam' : lam' ≤ 5 / 2) (hT : 0 ≤ T) :
    coefJ lam T ≤ coefJ lam' T := by
  have hlam'pos : 0 < lam' := hlam.trans_le hll
  have hexp : exp (-T) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hz : 0 < lam * exp (-T) := mul_pos hlam (exp_pos _)
  have hz' : 0 < lam' * exp (-T) := mul_pos hlam'pos (exp_pos _)
  have hzhi : lam * exp (-T) ≤ 5 / 2 :=
    (mul_le_of_le_one_right hlam.le hexp).trans (hll.trans hlam')
  have hz'hi : lam' * exp (-T) ≤ 5 / 2 :=
    (mul_le_of_le_one_right hlam'pos.le hexp).trans hlam'
  have hzz' : lam * exp (-T) ≤ lam' * exp (-T) :=
    mul_le_mul_of_nonneg_right hll (exp_pos _).le
  rw [coefJ_eq_activityKernel, coefJ_eq_activityKernel]
  exact mul_le_mul_of_nonneg_left
    (childActivityKernel_monotoneOn ⟨hz, hzhi⟩ ⟨hz', hz'hi⟩ hzz') hT

/-- Source: `tgt:lem:child` (b); the message decreases in child log-mass. -/
theorem msg_antitone_logmass {lam : ℝ} (hlam : 0 < lam) : Antitone (msg lam) := by
  apply antitone_of_hasDerivAt_nonpos (fun T => hasDerivAt_msg_Y hlam)
  intro T
  change -msg lam T * (1 - msg lam T) ≤ 0
  have hp := Reserve.msg_pos hlam T
  have hp1 := Reserve.msg_lt_one hlam T
  have hprod := mul_nonneg hp.le (sub_nonneg.mpr hp1.le)
  nlinarith

/-- Source: the polygon Taylor paragraph following `tgt:lem:poly`;
the first derivative of the actual child coordinate. -/
noncomputable def childRPrime (lam T : ℝ) : ℝ :=
  1 / lmass lam T + T * msg lam T / lmass lam T ^ 2

/-- Source: the same polygon Taylor paragraph; the second child derivative. -/
noncomputable def childRSecond (lam T : ℝ) : ℝ :=
  2 * msg lam T / lmass lam T ^ 2 + T *
    (-msg lam T * (1 - msg lam T) / lmass lam T ^ 2 +
      2 * msg lam T ^ 2 / lmass lam T ^ 3)

/-- Source: the polygon Taylor jets, `r' = 1/φ + T p/φ²`. -/
theorem hasDerivAt_childR_Y {lam T : ℝ} (hlam : 0 < lam) :
    HasDerivAt (childR lam) (childRPrime lam T) T := by
  have hl : lmass lam T ≠ 0 := (Reserve.lmass_pos hlam T).ne'
  have h := (hasDerivAt_id T).div (hasDerivAt_lmass_Y hlam) hl
  convert h using 1
  unfold childRPrime
  dsimp
  field_simp [hl]
  ring

/-- Source: the polygon Taylor jets, the second derivative of `r`. -/
theorem hasDerivAt_childRPrime_Y {lam T : ℝ} (hlam : 0 < lam) :
    HasDerivAt (childRPrime lam) (childRSecond lam T) T := by
  have hl : lmass lam T ≠ 0 := (Reserve.lmass_pos hlam T).ne'
  have hp := hasDerivAt_msg_Y (Y := T) hlam
  have hphi := hasDerivAt_lmass_Y (Y := T) hlam
  have hinv := (hasDerivAt_const T (1 : ℝ)).div hphi hl
  have htp := ((hasDerivAt_id T).mul hp).div (hphi.pow 2) (pow_ne_zero 2 hl)
  convert hinv.add htp using 1
  unfold childRSecond
  dsimp
  field_simp [hl]
  ring

/-- Source: the polygon Taylor jets, the first derivative of `J = p² r`. -/
noncomputable def coefJPrime (lam T : ℝ) : ℝ :=
  (-2) * (msg lam T * (msg lam T * (1 - msg lam T))) * childR lam T +
    msg lam T ^ 2 * childRPrime lam T

/-- Source: the polygon Taylor jets, the second derivative of `J`. -/
noncomputable def coefJSecond (lam T : ℝ) : ℝ :=
  2 * ((msg lam T * (1 - msg lam T)) ^ 2 +
    msg lam T * (msg lam T * (1 - msg lam T)) * (1 - 2 * msg lam T)) * childR lam T -
    4 * msg lam T * (msg lam T * (1 - msg lam T)) * childRPrime lam T +
      msg lam T ^ 2 * childRSecond lam T

/-- Source: the polygon Taylor jets, the first child derivative of `J`. -/
theorem hasDerivAt_coefJ_Y {lam T : ℝ} (hlam : 0 < lam) :
    HasDerivAt (coefJ lam) (coefJPrime lam T) T := by
  have hfun : coefJ lam = fun x => msg lam x ^ 2 * childR lam x := by
    funext x
    unfold coefJ childR
    ring
  rw [hfun]
  have h := ((hasDerivAt_msg_Y (Y := T) hlam).pow 2).mul
    (hasDerivAt_childR_Y (T := T) hlam)
  convert h using 1
  unfold coefJPrime
  dsimp
  ring

/-- Source: the polygon Taylor jets, the second child derivative of `J`. -/
theorem hasDerivAt_coefJPrime_Y {lam T : ℝ} (hlam : 0 < lam) :
    HasDerivAt (coefJPrime lam) (coefJSecond lam T) T := by
  have hp := hasDerivAt_msg_Y (Y := T) hlam
  have hu := hp.mul ((hasDerivAt_const T (1 : ℝ)).sub hp)
  have hfirst := ((hp.mul hu).const_mul (-2)).mul (hasDerivAt_childR_Y hlam)
  have hsecond := (hp.pow 2).mul (hasDerivAt_childRPrime_Y hlam)
  convert hfirst.add hsecond using 1
  unfold coefJSecond
  dsimp
  ring

/-- Source: `tgt:lem:child` (b), the elementary two-term log lower bound. -/
theorem neg_log_one_sub_ge_quadratic {p : ℝ} (hp : 0 ≤ p) (hp1 : p < 1) :
    p + p ^ 2 / 2 ≤ -log (1 - p) := by
  let f : ℝ → ℝ := fun x => -log (1 - x) - x - x ^ 2 / 2
  have hderiv : ∀ x ∈ Set.Icc 0 p,
      HasDerivAt f (x ^ 2 / (1 - x)) x := by
    intro x hx
    have hd : 1 - x ≠ 0 := by linarith [hx.2]
    have hlog := (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).log hd).neg
    have h := (hlog.sub (hasDerivAt_id x)).sub (((hasDerivAt_id x).pow 2).div_const 2)
    convert h using 1
    dsimp
    field_simp [hd]
    ring
  have hmono : MonotoneOn f (Set.Icc 0 p) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 p)
    · intro x hx
      exact (hderiv x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hderiv x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hxD := interior_subset hx
      rw [(hderiv x hxD).deriv]
      apply div_nonneg (sq_nonneg x)
      linarith [hxD.2]
  have h := hmono (show (0 : ℝ) ∈ Set.Icc 0 p by exact ⟨le_rfl, hp⟩)
    (show p ∈ Set.Icc 0 p by exact ⟨hp, le_rfl⟩) hp
  have hzero : f 0 = 0 := by norm_num [f]
  rw [hzero] at h
  dsimp [f] at h
  linarith

/-- Source: `tgt:lem:child` (b); the log lower bound controls `p/φ`. -/
theorem msg_div_lmass_le {lam : ℝ} (hlam : 0 < lam) (T : ℝ) :
    msg lam T / lmass lam T ≤ 1 / (1 + msg lam T / 2) := by
  have hp := Reserve.msg_pos hlam T
  have hp1 := Reserve.msg_lt_one hlam T
  have hmass := Reserve.lmass_pos hlam T
  have hlog := neg_log_one_sub_ge_quadratic hp.le hp1
  rw [← Reserve.lmass_eq_neg_log hlam T] at hlog
  rw [div_le_div_iff₀ hmass (by positivity : 0 < 1 + msg lam T / 2)]
  nlinarith

/-- Source: `tgt:lem:child` (b), its logarithmic derivative factor. -/
noncomputable def childSlope (lam T : ℝ) : ℝ :=
  1 / T + msg lam T / lmass lam T - 2 + 2 * msg lam T

/-- Source: `tgt:lem:child` (b), without taking a logarithm at `T=0`. -/
theorem hasDerivAt_coefJ_logmass {lam T : ℝ} (hlam : 0 < lam) (hT : 0 < T) :
    HasDerivAt (coefJ lam) (coefJ lam T * childSlope lam T) T := by
  have hl : lmass lam T ≠ 0 := (Reserve.lmass_pos hlam T).ne'
  have h := (((hasDerivAt_msg_Y hlam).pow 2).mul (hasDerivAt_id T)).div
    (hasDerivAt_lmass_Y hlam) hl
  convert h using 1
  unfold coefJ childSlope
  dsimp
  field_simp [hl, hT.ne']
  ring

/-- Source: `tgt:lem:child` (b); a finite segment's checked chain number
bounds the actual child's logarithmic derivative. -/
theorem childSlope_le_segment {lam a b T : ℝ} (hlam : 0 < lam)
    (ha : 0 < a) (haT : a ≤ T) (hTb : T ≤ b) :
    childSlope lam T ≤ 1 / a + 1 / (1 + msg lam b / 2) - 2 + 2 * msg lam a := by
  have hpT := Reserve.msg_pos hlam T
  have hpb := Reserve.msg_pos hlam b
  have hpa := Reserve.msg_pos hlam a
  have hpTa : msg lam T ≤ msg lam a := msg_antitone_logmass hlam haT
  have hpbT : msg lam b ≤ msg lam T := msg_antitone_logmass hlam hTb
  have hrecip : 1 / T ≤ 1 / a := div_le_div_of_nonneg_left (by norm_num) ha haT
  have hrat := msg_div_lmass_le hlam T
  have hrat' : 1 / (1 + msg lam T / 2) ≤ 1 / (1 + msg lam b / 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  unfold childSlope
  linarith

/-- Source: `tgt:lem:child` (b); the final segment uses `p(∞)=0`. -/
theorem childSlope_le_terminal {lam a T : ℝ} (hlam : 0 < lam)
    (ha : 0 < a) (haT : a ≤ T) :
    childSlope lam T ≤ 1 / a + 1 - 2 + 2 * msg lam a := by
  have hpT := Reserve.msg_pos hlam T
  have hpTa : msg lam T ≤ msg lam a := msg_antitone_logmass hlam haT
  have hrecip : 1 / T ≤ 1 / a := div_le_div_of_nonneg_left (by norm_num) ha haT
  have hrat := msg_div_lmass_le hlam T
  have hrat' : 1 / (1 + msg lam T / 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  unfold childSlope
  linarith

/-- Source: `tgt:lem:child` (b), the finite chain including the terminal ray. -/
theorem childSlope_neg_of_chain {lam : ℝ} (hlam : 0 < lam) (n : ℕ)
    (t : ℕ → ℝ) (ht : 0 < t 0)
    (hinc : ∀ i < n, t i < t (i + 1))
    (hseg : ∀ i < n,
      1 / t i + 1 / (1 + msg lam (t (i + 1)) / 2) - 2 + 2 * msg lam (t i) < 0)
    (hlast : 1 / t n + 1 - 2 + 2 * msg lam (t n) < 0)
    {T : ℝ} (hT : t 0 ≤ T) : childSlope lam T < 0 := by
  induction n generalizing t with
  | zero =>
      exact (childSlope_le_terminal hlam ht hT).trans_lt hlast
  | succ n ih =>
      by_cases hT1 : T ≤ t 1
      · exact (childSlope_le_segment hlam ht hT hT1).trans_lt (hseg 0 (by omega))
      · apply ih (fun i => t (i + 1))
        · exact ht.trans (hinc 0 (by omega))
        · intro i hi
          exact hinc (i + 1) (by omega)
        · intro i hi
          exact hseg (i + 1) (by omega)
        · exact hlast
        · exact (le_of_not_ge hT1)

/-- Source: `tgt:lem:child` (b); a checked chain certifies the whole
infinite child tail, including its segment boundaries. -/
theorem coefJ_antitoneOn_of_chain {lam : ℝ} (hlam : 0 < lam) (n : ℕ)
    (t : ℕ → ℝ) (ht : 0 < t 0)
    (hinc : ∀ i < n, t i < t (i + 1))
    (hseg : ∀ i < n,
      1 / t i + 1 / (1 + msg lam (t (i + 1)) / 2) - 2 + 2 * msg lam (t i) < 0)
    (hlast : 1 / t n + 1 - 2 + 2 * msg lam (t n) < 0) :
    AntitoneOn (coefJ lam) (Set.Ici (t 0)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici (t 0))
  · intro T hT
    exact (hasDerivAt_coefJ_logmass hlam (ht.trans_le hT)).continuousAt.continuousWithinAt
  · intro T hT
    exact (hasDerivAt_coefJ_logmass hlam (ht.trans_le (interior_subset hT))).differentiableAt.differentiableWithinAt
  · intro T hT
    have hT' := interior_subset hT
    rw [(hasDerivAt_coefJ_logmass hlam (ht.trans_le hT')).deriv]
    have hs := childSlope_neg_of_chain hlam n t ht hinc hseg hlast hT'
    have hJ : 0 < coefJ lam T := by
      unfold coefJ
      exact div_pos (mul_pos (sq_pos_of_pos (Reserve.msg_pos hlam T)) (ht.trans_le hT'))
        (Reserve.lmass_pos hlam T)
    exact (mul_neg_of_pos_of_neg hJ hs).le

/-- Source: the child paragraph following `tgt:lem:poly`; a certified tail
also controls each polygon slack `J - b r` when its slope is nonnegative. -/
theorem child_polygon_slack_antitoneOn {lam T₀ b : ℝ} (hlam : 0 < lam)
    (hT₀ : 0 ≤ T₀) (hb : 0 ≤ b)
    (hJ : AntitoneOn (coefJ lam) (Set.Ici T₀)) :
    AntitoneOn (fun T => coefJ lam T - b * childR lam T) (Set.Ici T₀) := by
  intro T hT T' hT' hTT'
  have hj := hJ hT hT' hTT'
  have hr := childR_monotoneOn hlam (hT₀.trans hT) (hT₀.trans hT') hTT'
  have hbr := mul_le_mul_of_nonneg_left hr hb
  linarith

/-- Source: `tgt:lem:poly`; each nonnegative-slope upper line transports
from its polygon activity to every smaller positive activity. -/
theorem child_polygon_line_transport {lam lamp T a b : ℝ} (hlam : 0 < lam)
    (hll : lam ≤ lamp) (hlamp : lamp ≤ 5 / 2) (hT : 0 ≤ T) (hb : 0 ≤ b)
    (hline : coefJ lamp T ≤ a + b * childR lamp T) :
    coefJ lam T ≤ a + b * childR lam T := by
  calc
    coefJ lam T ≤ coefJ lamp T := coefJ_monotone_activity hlam hll hlamp hT
    _ ≤ a + b * childR lamp T := hline
    _ ≤ a + b * childR lam T := add_le_add (le_refl a)
      (mul_le_mul_of_nonneg_left (childR_antitone_activity hlam hll hT) hb)

/-- Source: `tgt:lem:poly`; the polygon cap transports with its lines. -/
theorem child_polygon_cap_transport {lam lamp T cap : ℝ} (hlam : 0 < lam)
    (hll : lam ≤ lamp) (hlamp : lamp ≤ 5 / 2) (hT : 0 ≤ T)
    (hcap : coefJ lamp T ≤ cap) : coefJ lam T ≤ cap :=
  (coefJ_monotone_activity hlam hll hlamp hT).trans hcap

/-- Source: `tgt:lem:poly`; all three lines and the cap transport on the
whole physical child curve. -/
theorem child_polygon_transport {lam lamp : ℝ} (hlam : 0 < lam)
    (hll : lam ≤ lamp) (hlamp : lamp ≤ 5 / 2) (a b : Fin 3 → ℝ) (cap : ℝ)
    (hb : ∀ i, 0 ≤ b i)
    (hlines : ∀ T ≥ 0, ∀ i, coefJ lamp T ≤ a i + b i * childR lamp T)
    (hcap : ∀ T ≥ 0, coefJ lamp T ≤ cap) :
    (∀ T ≥ 0, ∀ i, coefJ lam T ≤ a i + b i * childR lam T) ∧
      (∀ T ≥ 0, coefJ lam T ≤ cap) := by
  constructor
  · intro T hT i
    exact child_polygon_line_transport hlam hll hlamp hT (hb i) (hlines T hT i)
  · intro T hT
    exact child_polygon_cap_transport hlam hll hlamp hT (hcap T hT)

end Erdos993Lean.Analytic.HandVariance
