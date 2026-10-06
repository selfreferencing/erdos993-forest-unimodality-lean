import Erdos993Lean.Analytic.V22.Checks.EarlyStatements

/-!
# Analytic transport of the capped coefficient checks

Source: repaired note Lemmas 4.10 and 4.13, and checks 7.4--7.7.
Activities, real endpoints, and the exact cap `(6/r_m)^2` are retained.
Endpoint positivity and numerical margins are separate certificate inputs.
No finite numerical check is asserted by this module.
-/

namespace Erdos993Lean.Analytic.V22

noncomputable section
open Checks

theorem activity_denominator_pos {rm : ℝ} (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) :
    0 < 1 - rm^2 := by
  nlinarith [mul_nonneg hrm (sub_nonneg.mpr hrmhi)]

theorem cCoef_pos {N : ℝ} (hN : 1 < N) : 0 < cCoef N := by
  have hrecip : (1 : ℝ)/N < 1 := (div_lt_one (by linarith)).mpr hN
  dsimp [cCoef]
  linarith

theorem rho_monotone_parameter {N N0 : ℝ} (hN0 : 0 < N0) (hN : N0 ≤ N) :
    rho N0 ≤ rho N := by
  have h0 : 0 < N0+1 := by linarith
  have h1 : 0 < N+1 := by linarith
  apply (div_le_div_iff₀ h0 h1).mpr
  nlinarith

theorem cCoef_monotone_parameter {N N0 : ℝ} (hN0 : 0 < N0) (hN : N0 ≤ N) :
    cCoef N0 ≤ cCoef N := by
  have hquot : (1 : ℝ)/N ≤ 1/N0 := div_le_div_of_nonneg_left (by norm_num) hN0 hN
  dsimp [cCoef]
  linarith

/-- The all-`ν` coefficient lower bound increases in the retained size. -/
theorem rhoStar_monotone_parameter {rm N N0 : ℝ}
    (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) (hN0 : 1 < N0) (hN : N0 ≤ N) :
    rhoStar N0 rm ≤ rhoStar N rm := by
  have hd := activity_denominator_pos hrm hrmhi
  have hc0 := cCoef_pos hN0
  have hNgt : 1 < N := hN0.trans_le hN
  have hc := cCoef_pos hNgt
  have hs0 : 0 < Real.sqrt (cCoef N0) := Real.sqrt_pos.mpr hc0
  have hs : 0 < Real.sqrt (cCoef N) := Real.sqrt_pos.mpr hc
  have hsorder := Real.sqrt_le_sqrt (cCoef_monotone_parameter (by linarith) hN)
  have hfirst : (1-rm^2)*rho N0 ≤ (1-rm^2)*rho N :=
    mul_le_mul_of_nonneg_left (rho_monotone_parameter (by linarith) hN) hd.le
  have hdenorder : (N0+1)*Real.sqrt (cCoef N0) ≤ (N+1)*Real.sqrt (cCoef N) :=
    mul_le_mul (add_le_add hN (le_refl 1)) hsorder hs0.le (by linarith)
  have hsecond : 2/((N+1)*Real.sqrt (cCoef N)) ≤
      2/((N0+1)*Real.sqrt (cCoef N0)) :=
    div_le_div_of_nonneg_left (by norm_num) (mul_pos (by linarith) hs0) hdenorder
  have hthird : rm^2/(3*(1-rm^2)*Real.sqrt (cCoef N)) ≤
      rm^2/(3*(1-rm^2)*Real.sqrt (cCoef N0)) :=
    div_le_div_of_nonneg_left (sq_nonneg rm)
      (mul_pos (mul_pos (by norm_num) hd) hs0)
      (mul_le_mul_of_nonneg_left hsorder (by positivity))
  dsimp [rhoStar]
  linarith

/-- A positive endpoint certificate remains positive at every larger size. -/
theorem rhoStar_pos_of_endpoint {rm N N0 : ℝ}
    (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) (hN0 : 1 < N0) (hN : N0 ≤ N)
    (hstart : 0 < rhoStar N0 rm) : 0 < rhoStar N rm :=
  hstart.trans_le (rhoStar_monotone_parameter hrm hrmhi hN0 hN)

theorem e5_nonneg (rm : ℝ) : 0 ≤ e5 rm := by dsimp [e5]; positivity

theorem e3_nonneg {rm : ℝ} (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) : 0 ≤ e3 rm := by
  have hd := activity_denominator_pos hrm hrmhi
  dsimp [e3]
  positivity

theorem e4_eq_e5 {rm N : ℝ} (hN : 0 < N) (hd : 1-rm^2 ≠ 0) :
    e4 N rm = e5 rm + e5 rm/N := by
  dsimp [e4, e5]
  field_simp [ne_of_gt hN, hd] <;> ring

/-- The only size-dependent coefficient of `E₂` decreases in `N`. -/
theorem e4_antitone_parameter {rm N N0 : ℝ}
    (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) (hN0 : 0 < N0) (hN : N0 ≤ N) :
    e4 N rm ≤ e4 N0 rm := by
  have hd := ne_of_gt (activity_denominator_pos hrm hrmhi)
  rw [e4_eq_e5 (hN0.trans_le hN) hd, e4_eq_e5 hN0 hd]
  exact add_le_add (le_refl _) (div_le_div_of_nonneg_left (e5_nonneg rm) hN0 hN)

theorem e5_le_e4 {rm N : ℝ} (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) (hN : 0 < N) :
    e5 rm ≤ e4 N rm := by
  rw [e4_eq_e5 hN (ne_of_gt (activity_denominator_pos hrm hrmhi))]
  exact le_add_of_nonneg_right (div_nonneg (e5_nonneg rm) hN.le)

theorem E2_nonneg {rm N nu : ℝ}
    (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) (hN : 0 < N) (hnu : 0 ≤ nu) :
    0 ≤ E2 N rm nu := by
  have he3 := e3_nonneg hrm hrmhi
  have he4 : 0 ≤ e4 N rm := (e5_nonneg rm).trans (e5_le_e4 hrm hrmhi hN)
  have he5 := e5_nonneg rm
  dsimp [E2, e2]
  positivity

/-- With `ν` fixed, `E₂` decreases termwise in the real size. -/
theorem E2_antitone_parameter {rm N N0 nu : ℝ}
    (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) (hN0 : 0 < N0) (hN : N0 ≤ N) :
    E2 N rm nu ≤ E2 N0 rm nu := by
  have hpiece := mul_le_mul_of_nonneg_right
    (e4_antitone_parameter hrm hrmhi hN0 hN) (sq_nonneg nu)
  dsimp [E2]
  linarith

/-- The fixed-`ν` denominator increases once its retained `ρ_*` is positive. -/
theorem betaE_monotone_fixed_nu {rm N N0 nu : ℝ}
    (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) (hN0 : 1 < N0) (hN : N0 ≤ N)
    (hnu : 0 ≤ nu) (hstart : 0 < rhoStar N0 rm) :
    betaE N0 rm nu ≤ betaE N rm nu := by
  have hrs := rhoStar_monotone_parameter hrm hrmhi hN0 hN
  have hrspos := hstart.trans_le hrs
  have hquot : 2/rhoStar N rm ≤ 2/rhoStar N0 rm :=
    div_le_div_of_nonneg_left (by norm_num) hstart hrs
  have he := E2_antitone_parameter (nu := nu) hrm hrmhi (by linarith) hN
  have hepos := E2_nonneg hrm hrmhi (show 0 < N from (by linarith)) hnu
  have hprod : 2/rhoStar N rm*E2 N rm nu ≤ 2/rhoStar N0 rm*E2 N0 rm nu :=
    mul_le_mul hquot he hepos (div_nonneg (by norm_num) hstart.le)
  dsimp [betaE]
  linarith

theorem sqrt_cap {rm : ℝ} (hrm : 0 < rm) :
    Real.sqrt ((6/rm)^2) = 6/rm := by
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (div_nonneg (by norm_num) hrm.le)]

theorem capped_nu_eq_pre {rm N : ℝ} (hrm : 0 < rm) (hN : N ≤ (6/rm)^2) :
    min 6 (rm*Real.sqrt N) = rm*Real.sqrt N := by
  have hsqrt : Real.sqrt N ≤ 6/rm :=
    Real.sqrt_le_iff.mpr ⟨div_nonneg (by norm_num) hrm.le, hN⟩
  have hnu : rm*Real.sqrt N ≤ 6 := by
    simpa only [mul_comm] using (le_div_iff₀ hrm).mp hsqrt
  exact min_eq_right hnu

theorem capped_nu_eq_tail {rm N : ℝ} (hrm : 0 < rm) (hN : (6/rm)^2 ≤ N) :
    min 6 (rm*Real.sqrt N) = 6 := by
  have hsqrt : 6/rm ≤ Real.sqrt N := by
    simpa only [sqrt_cap hrm] using Real.sqrt_le_sqrt hN
  have hnu : 6 ≤ rm*Real.sqrt N := by
    simpa only [mul_comm] using (div_le_iff₀ hrm).mp hsqrt
  exact min_eq_left hnu

/-- The cap tail is termwise monotone from any positive endpoint below it. -/
theorem cappedBeta_monotone_tail {rm N0 : ℝ}
    (hrm : 0 < rm) (hrmhi : rm ≤ 1/2) (hN0 : 1 < N0)
    (hcap : N0 ≤ (6/rm)^2) (hstart : 0 < rhoStar N0 rm) :
    MonotoneOn (cappedBeta rm) (Set.Ici ((6/rm)^2)) := by
  intro x hx y hy hxy
  have hxs : N0 ≤ x := hcap.trans hx
  have hxgt : 1 < x := hN0.trans_le hxs
  have hxrho := rhoStar_pos_of_endpoint hrm.le hrmhi hN0 hxs hstart
  dsimp [cappedBeta]
  rw [capped_nu_eq_tail hrm hx, capped_nu_eq_tail hrm hy]
  exact betaE_monotone_fixed_nu hrm.le hrmhi hxgt hxy (by norm_num) hxrho

/-- Exact derivative of `c=1-1/N`. -/
theorem cCoef_hasDerivAt {N : ℝ} (hN : 0 < N) :
    HasDerivAt cCoef (1/N^2) N := by
  convert (hasDerivAt_const N (1 : ℝ)).sub
    ((hasDerivAt_const N (1 : ℝ)).div (hasDerivAt_id N) (ne_of_gt hN)) using 1 <;>
    dsimp [cCoef] <;> ring

theorem rho_hasDerivAt {N : ℝ} (hN : 0 < N) :
    HasDerivAt rho (1/(N+1)^2) N := by
  convert (hasDerivAt_id N).div ((hasDerivAt_id N).add_const 1)
    (show N+1 ≠ 0 from ne_of_gt (by linarith)) using 1 <;> dsimp [rho] <;> ring

/-- A positive derivative formula for the actual retained `ρ_*`. -/
def rhoStarDerivative (rm N : ℝ) : ℝ :=
  let cD := (1/N^2)/(2*Real.sqrt (cCoef N))
  (1-rm^2)/(N+1)^2
    + 2*(Real.sqrt (cCoef N)+(N+1)*cD)/((N+1)*Real.sqrt (cCoef N))^2
    + rm^2*(3*(1-rm^2)*cD)/(3*(1-rm^2)*Real.sqrt (cCoef N))^2

theorem rhoStar_hasDerivAt {rm N : ℝ}
    (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) (hN : 1 < N) :
    HasDerivAt (fun n => rhoStar n rm) (rhoStarDerivative rm N) N := by
  have hd := activity_denominator_pos hrm hrmhi
  have hc := cCoef_pos hN
  have hs : 0 < Real.sqrt (cCoef N) := Real.sqrt_pos.mpr hc
  have hsder := (cCoef_hasDerivAt (show 0 < N by linarith)).sqrt (ne_of_gt hc)
  have hden1 := ((hasDerivAt_id N).add_const 1).mul hsder
  have hden2 := hsder.const_mul (3*(1-rm^2))
  have hterm1 := (rho_hasDerivAt (show 0 < N by linarith)).const_mul (1-rm^2)
  have hterm2 := (hasDerivAt_const N (2 : ℝ)).div hden1
    (ne_of_gt (mul_pos (show 0 < N+1 by linarith) hs))
  have hterm3 := (hasDerivAt_const N (rm^2)).div hden2
    (ne_of_gt (mul_pos (mul_pos (by norm_num) hd) hs))
  convert (hterm1.sub hterm2).sub hterm3 using 1 <;>
    dsimp [rhoStar, rhoStarDerivative] <;> ring

theorem rhoStarDerivative_nonneg {rm N : ℝ}
    (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) (hN : 1 < N) :
    0 ≤ rhoStarDerivative rm N := by
  have hd := activity_denominator_pos hrm hrmhi
  have hc := cCoef_pos hN
  have hs : 0 < Real.sqrt (cCoef N) := Real.sqrt_pos.mpr hc
  have hn : 0 < N+1 := by linarith
  dsimp [rhoStarDerivative]
  positivity

/-- An algebraically identical pre-cap expression, with the cancelled
`e₄(N) r_m² N` written so its derivative is transparent. -/
def preCapE2 (rm N : ℝ) : ℝ :=
  e2 + e3 rm*rm*Real.sqrt N + e5 rm*rm^2*(N+1)
    + e5 rm*rm^3*(Real.sqrt N)^3

def preCapE2Derivative (rm N : ℝ) : ℝ :=
  e3 rm*rm/(2*Real.sqrt N) + e5 rm*rm^2
    + (3/2)*e5 rm*rm^3*Real.sqrt N

theorem preCapE2_eq {rm N : ℝ}
    (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) (hN : 0 < N) :
    preCapE2 rm N = E2 N rm (rm*Real.sqrt N) := by
  have hd := ne_of_gt (activity_denominator_pos hrm hrmhi)
  dsimp [preCapE2, E2]
  rw [e4_eq_e5 hN hd]
  simp only [mul_pow, Real.sq_sqrt hN.le]
  field_simp [ne_of_gt hN] <;> ring

theorem preCapE2_hasDerivAt {rm N : ℝ} (hN : 0 < N) :
    HasDerivAt (preCapE2 rm) (preCapE2Derivative rm N) N := by
  have hs := Real.hasDerivAt_sqrt (ne_of_gt hN)
  have hspos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have h := (((hasDerivAt_const N e2).add (hs.const_mul (e3 rm*rm))).add
    (((hasDerivAt_id N).add_const 1).const_mul (e5 rm*rm^2))).add
    ((hs.pow 3).const_mul (e5 rm*rm^3))
  convert h using 1
  dsimp [preCapE2Derivative]
  norm_num
  field_simp [ne_of_gt hspos] <;> ring

theorem preCapE2_nonneg {rm N : ℝ}
    (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) (hN : 0 < N) :
    0 ≤ preCapE2 rm N := by
  rw [preCapE2_eq hrm hrmhi hN]
  exact E2_nonneg hrm hrmhi hN (by positivity)

theorem preCapE2Derivative_nonneg {rm N : ℝ}
    (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) : 0 ≤ preCapE2Derivative rm N := by
  have he3 := e3_nonneg hrm hrmhi
  have he5 := e5_nonneg rm
  dsimp [preCapE2Derivative]
  positivity

/-- The source's termwise endpoint expression bounds the actual pre-cap
derivative, including the exact cap. -/
theorem preCapE2Derivative_le {rm N Nlo : ℝ}
    (hrm : 0 < rm) (hrmhi : rm ≤ 1/2) (hNlo : 0 < Nlo)
    (hN : Nlo ≤ N) (hcap : N ≤ (6/rm)^2) :
    preCapE2Derivative rm N ≤ e2DerivativeBound rm Nlo := by
  have he3 := e3_nonneg hrm.le hrmhi
  have he5 := e5_nonneg rm
  have hslo : 0 < Real.sqrt Nlo := Real.sqrt_pos.mpr hNlo
  have hsord := Real.sqrt_le_sqrt hN
  have hfirst : e3 rm*rm/(2*Real.sqrt N) ≤ e3 rm*rm/(2*Real.sqrt Nlo) :=
    div_le_div_of_nonneg_left (mul_nonneg he3 hrm.le)
      (mul_pos (by norm_num) hslo) (mul_le_mul_of_nonneg_left hsord (by norm_num))
  have hsecond : e5 rm*rm^2 ≤ e4 Nlo rm*rm^2 :=
    mul_le_mul_of_nonneg_right (e5_le_e4 hrm.le hrmhi hNlo) (sq_nonneg rm)
  have hthird : (3/2)*e5 rm*rm^3*Real.sqrt N ≤
      (3/2)*e5 rm*rm^3*Real.sqrt ((6/rm)^2) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcap) (by positivity)
  dsimp [preCapE2Derivative, e2DerivativeBound]
  linarith

def preCapBeta (rm N : ℝ) : ℝ := N-1-2/rhoStar N rm*preCapE2 rm N

def preCapBetaDerivative (rm N : ℝ) : ℝ :=
  1-2/rhoStar N rm*preCapE2Derivative rm N
    + 2*preCapE2 rm N*rhoStarDerivative rm N/(rhoStar N rm)^2

theorem preCapBeta_hasDerivAt {rm N : ℝ}
    (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) (hN : 1 < N)
    (hrs : 0 < rhoStar N rm) :
    HasDerivAt (preCapBeta rm) (preCapBetaDerivative rm N) N := by
  have hquot := (hasDerivAt_const N (2 : ℝ)).div
    (rhoStar_hasDerivAt hrm hrmhi hN) (ne_of_gt hrs)
  have hprod := hquot.mul (preCapE2_hasDerivAt (rm := rm) (show 0 < N by linarith))
  convert ((hasDerivAt_id N).sub_const 1).sub hprod using 1 <;>
    dsimp [preCapBetaDerivative] <;> field_simp [ne_of_gt hrs] <;> ring

theorem cappedBeta_eq_pre {rm N : ℝ}
    (hrm : 0 < rm) (hrmhi : rm ≤ 1/2) (hN : 0 < N) (hcap : N ≤ (6/rm)^2) :
    cappedBeta rm N = preCapBeta rm N := by
  dsimp [cappedBeta]
  rw [capped_nu_eq_pre hrm hcap]
  dsimp [betaE, preCapBeta]
  rw [preCapE2_eq hrm.le hrmhi hN]

/-- The actual pre-cap derivative retains the positive derivative of `ρ_*`.
Dropping that term gives the source's endpoint lower bound. -/
theorem preCapBetaDerivative_lower {rm N Nlo : ℝ}
    (hrm : 0 < rm) (hrmhi : rm ≤ 1/2) (hNlo : 1 < Nlo)
    (hN : Nlo ≤ N) (hcap : N ≤ (6/rm)^2) (hstart : 0 < rhoStar Nlo rm) :
    betaDerivativeBound rm Nlo ≤ preCapBetaDerivative rm N := by
  have hNgt : 1 < N := hNlo.trans_le hN
  have hrs := rhoStar_monotone_parameter hrm.le hrmhi hNlo hN
  have hrspos := hstart.trans_le hrs
  have he := preCapE2_nonneg hrm.le hrmhi (show 0 < N by linarith)
  have heD := preCapE2Derivative_nonneg (N := N) hrm.le hrmhi
  have hrD := rhoStarDerivative_nonneg hrm.le hrmhi hNgt
  have hD := preCapE2Derivative_le hrm hrmhi (show 0 < Nlo by linarith) hN hcap
  have hquot : 2/rhoStar N rm ≤ 2/rhoStar Nlo rm :=
    div_le_div_of_nonneg_left (by norm_num) hstart hrs
  have hprod : 2/rhoStar N rm*preCapE2Derivative rm N ≤
      2/rhoStar Nlo rm*e2DerivativeBound rm Nlo :=
    mul_le_mul hquot hD heD (div_nonneg (by norm_num) hstart.le)
  have hcorrection : 0 ≤ 2*preCapE2 rm N*rhoStarDerivative rm N/(rhoStar N rm)^2 :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) he) hrD) (sq_nonneg _)
  dsimp [betaDerivativeBound, preCapBetaDerivative]
  linarith

/-- The cap is handled by a derivative within the closed pre-cap interval,
so no two-sided derivative of the kink is assumed. -/
theorem cappedBeta_hasDerivWithinAt_pre {rm N Nlo : ℝ}
    (hrm : 0 < rm) (hrmhi : rm ≤ 1/2) (hNlo : 1 < Nlo)
    (hN : N ∈ Set.Icc Nlo ((6/rm)^2)) (hstart : 0 < rhoStar Nlo rm) :
    HasDerivWithinAt (cappedBeta rm) (preCapBetaDerivative rm N)
      (Set.Icc Nlo ((6/rm)^2)) N := by
  have hNgt := hNlo.trans_le hN.1
  have hpos := rhoStar_pos_of_endpoint hrm.le hrmhi hNlo hN.1 hstart
  exact (preCapBeta_hasDerivAt hrm.le hrmhi hNgt hpos).hasDerivWithinAt.congr_of_mem
    (fun n hn => cappedBeta_eq_pre hrm hrmhi (by linarith [hn.1]) hn.2) hN

/-- Exact analytic consumer of the A3/A3′ endpoint margin, including both
ends of a nondegenerate closed pre-cap interval. -/
theorem betaDerivativeOn_lower {rm N Nlo : ℝ}
    (hrm : 0 < rm) (hrmhi : rm ≤ 1/2) (hNlo : 1 < Nlo)
    (hinterval : Nlo < (6/rm)^2) (hN : N ∈ Set.Icc Nlo ((6/rm)^2))
    (hstart : 0 < rhoStar Nlo rm) :
    betaDerivativeBound rm Nlo ≤ betaDerivativeOn rm Nlo N := by
  dsimp [betaDerivativeOn]
  rw [(cappedBeta_hasDerivWithinAt_pre hrm hrmhi hNlo hN hstart).derivWithin
    (uniqueDiffOn_Icc hinterval N hN)]
  exact preCapBetaDerivative_lower hrm hrmhi hNlo hN.1 hN.2 hstart

theorem cappedBeta_monotone_pre {rm Nlo : ℝ}
    (hrm : 0 < rm) (hrmhi : rm ≤ 1/2) (hNlo : 1 < Nlo)
    (hstart : 0 < rhoStar Nlo rm) (hmargin : 0 ≤ betaDerivativeBound rm Nlo) :
    MonotoneOn (cappedBeta rm) (Set.Icc Nlo ((6/rm)^2)) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
  · intro n hn
    exact (cappedBeta_hasDerivWithinAt_pre hrm hrmhi hNlo hn hstart).continuousWithinAt
  · intro n hn
    exact (cappedBeta_hasDerivWithinAt_pre hrm hrmhi hNlo
      (interior_subset hn) hstart).mono interior_subset
  · intro n hn
    have hclosed := interior_subset hn
    exact hmargin.trans (preCapBetaDerivative_lower hrm hrmhi hNlo
      hclosed.1 hclosed.2 hstart)

/-- Splicing the pre-cap derivative transport with the constant-`ν` tail
gives the complete monotonic consumer. Its inputs are finite endpoint facts. -/
theorem cappedBeta_monotone_from_endpoint {rm Nlo : ℝ}
    (hrm : 0 < rm) (hrmhi : rm ≤ 1/2) (hNlo : 1 < Nlo)
    (hstart : 0 < rhoStar Nlo rm)
    (hmargin : Nlo < (6/rm)^2 → 0 ≤ betaDerivativeBound rm Nlo) :
    MonotoneOn (cappedBeta rm) (Set.Ici Nlo) := by
  by_cases hbefore : Nlo < (6/rm)^2
  · have hpre := cappedBeta_monotone_pre hrm hrmhi hNlo hstart (hmargin hbefore)
    have htail := cappedBeta_monotone_tail hrm hrmhi hNlo hbefore.le hstart
    intro x hx y hy hxy
    by_cases hxcap : x ≤ (6/rm)^2
    · by_cases hycap : y ≤ (6/rm)^2
      · exact hpre ⟨hx,hxcap⟩ ⟨hy,hycap⟩ hxy
      · exact (hpre ⟨hx,hxcap⟩ ⟨hbefore.le,le_refl _⟩ hxcap).trans
          (htail (Set.mem_Ici.mpr (le_refl _)) (Set.mem_Ici.mpr (le_of_not_ge hycap))
            (le_of_not_ge hycap))
    · exact htail (Set.mem_Ici.mpr (le_of_not_ge hxcap))
        (Set.mem_Ici.mpr ((le_of_not_ge hxcap).trans hxy)) hxy
  · intro x hx y hy hxy
    have hafter : (6/rm)^2 ≤ Nlo := le_of_not_gt hbefore
    dsimp [cappedBeta]
    rw [capped_nu_eq_tail hrm (hafter.trans hx), capped_nu_eq_tail hrm (hafter.trans hy)]
    exact betaE_monotone_fixed_nu hrm.le hrmhi (hNlo.trans_le hx) hxy (by norm_num)
      (rhoStar_pos_of_endpoint hrm.le hrmhi hNlo hx hstart)

def preCapBonus (rm N : ℝ) : ℝ :=
  (N-1)*rhoStar N rm/2-preCapE2 rm N-(N+1)/((71/20)*N)

def preCapBonusDerivative (rm N : ℝ) : ℝ :=
  rhoStar N rm/2+(N-1)*rhoStarDerivative rm N/2-preCapE2Derivative rm N
    + 1/((71/20)*N^2)

theorem preCapBonus_hasDerivAt {rm N : ℝ}
    (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) (hN : 1 < N) :
    HasDerivAt (preCapBonus rm) (preCapBonusDerivative rm N) N := by
  have hNpos : 0 < N := by linarith
  have hfirst := (((hasDerivAt_id N).sub_const 1).mul
    (rhoStar_hasDerivAt hrm hrmhi hN)).div_const 2
  have hsecond := preCapE2_hasDerivAt (rm := rm) (show 0 < N by linarith)
  have hthird := ((hasDerivAt_id N).add_const 1).div
    ((hasDerivAt_id N).const_mul (71/20))
    (show (71/20:ℝ)*N ≠ 0 from ne_of_gt (mul_pos (by norm_num) hNpos))
  convert (hfirst.sub hsecond).sub hthird using 1 <;>
    dsimp [preCapBonusDerivative] <;> field_simp [ne_of_gt hNpos] <;> ring

theorem lambdaBonusF_eq_pre {rm N : ℝ}
    (hrm : 0 < rm) (hrmhi : rm ≤ 1/2) (hN : 0 < N) (hcap : N ≤ (6/rm)^2) :
    lambdaBonusF N rm = preCapBonus rm N := by
  dsimp [lambdaBonusF]
  rw [capped_nu_eq_pre hrm hcap]
  dsimp [preCapBonus]
  rw [preCapE2_eq hrm.le hrmhi hN]

theorem preCapBonusDerivative_lower {rm N Nlo : ℝ}
    (hrm : 0 < rm) (hrmhi : rm ≤ 1/2) (hNlo : 1 < Nlo)
    (hN : Nlo ≤ N) (hcap : N ≤ (6/rm)^2) :
    rhoStar Nlo rm/2-e2DerivativeBound rm Nlo ≤ preCapBonusDerivative rm N := by
  have hrs := rhoStar_monotone_parameter hrm.le hrmhi hNlo hN
  have hrD := rhoStarDerivative_nonneg hrm.le hrmhi (hNlo.trans_le hN)
  have hD := preCapE2Derivative_le hrm hrmhi (show 0 < Nlo by linarith) hN hcap
  have hNminus : 0 ≤ N-1 := by linarith
  have hproduct : 0 ≤ (N-1)*rhoStarDerivative rm N/2 := by positivity
  have hquot : 0 ≤ 1/((71/20:ℝ)*N^2) := by positivity
  dsimp [preCapBonusDerivative]
  linarith

/-- The A4 pre-cap inequality is transported to the actual within derivative
of `f`, retaining its closed cap endpoint. -/
theorem lambdaBonusF_derivWithin_lower {rm N Nlo : ℝ}
    (hrm : 0 < rm) (hrmhi : rm ≤ 1/2) (hNlo : 1 < Nlo)
    (hinterval : Nlo < (6/rm)^2) (hN : N ∈ Set.Icc Nlo ((6/rm)^2)) :
    rhoStar Nlo rm/2-e2DerivativeBound rm Nlo ≤
      derivWithin (fun n => lambdaBonusF n rm) (Set.Icc Nlo ((6/rm)^2)) N := by
  have hwithin := (preCapBonus_hasDerivAt hrm.le hrmhi
    (hNlo.trans_le hN.1)).hasDerivWithinAt (s := Set.Icc Nlo ((6/rm)^2))
  have hactual := hwithin.congr_of_mem
    (fun n hn => lambdaBonusF_eq_pre hrm hrmhi (by linarith [hn.1]) hn.2) hN
  rw [hactual.derivWithin (uniqueDiffOn_Icc hinterval N hN)]
  exact preCapBonusDerivative_lower hrm hrmhi hNlo hN.1 hN.2

def bonusTailDerivative (rm N : ℝ) : ℝ :=
  rhoStar ((6/rm)^2) rm*(N-1/2)-E2 ((6/rm)^2) rm 6-1/(71/20)

theorem bonusTail_hasDerivAt (rm N : ℝ) :
    HasDerivAt (bonusTail rm) (bonusTailDerivative rm N) N := by
  have hfirst := (((hasDerivAt_id N).mul ((hasDerivAt_id N).sub_const 1)).mul_const
    (rhoStar ((6/rm)^2) rm)).div_const 2
  have hsecond := (hasDerivAt_id N).mul_const (E2 ((6/rm)^2) rm 6)
  have hthird := ((hasDerivAt_id N).add_const 1).div_const (71/20)
  convert (hfirst.sub hsecond).sub hthird using 1 <;>
    dsimp [bonusTail, bonusTailDerivative] <;> ring

/-- The fixed-coefficient quadratic tail grows from its checked value and
derivative at the exact cap; no all-`N` target is used as an input. -/
theorem bonusTail_transport {rm : ℝ}
    (hrs : 0 ≤ rhoStar ((6/rm)^2) rm)
    (hvalue : 0 < bonusTail rm ((6/rm)^2))
    (hderiv : 0 ≤ deriv (bonusTail rm) ((6/rm)^2)) :
    (∀ N : ℝ, (6/rm)^2 ≤ N → 0 < bonusTail rm N) ∧
      MonotoneOn (bonusTail rm) (Set.Ici ((6/rm)^2)) := by
  have hstart : 0 ≤ bonusTailDerivative rm ((6/rm)^2) := by
    rwa [(bonusTail_hasDerivAt rm ((6/rm)^2)).deriv] at hderiv
  have hD : ∀ n : ℝ, (6/rm)^2 ≤ n → 0 ≤ bonusTailDerivative rm n := by
    intro n hn
    have hdiff := mul_nonneg hrs (sub_nonneg.mpr hn)
    dsimp [bonusTailDerivative] at hstart ⊢
    nlinarith
  have hmono : MonotoneOn (bonusTail rm) (Set.Ici ((6/rm)^2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · exact (fun n hn => (bonusTail_hasDerivAt rm n).continuousAt.continuousWithinAt)
    · intro n hn
      exact (bonusTail_hasDerivAt rm n).differentiableAt.differentiableWithinAt
    · intro n hn
      rw [(bonusTail_hasDerivAt rm n).deriv]
      exact hD n (interior_subset hn)
  refine ⟨?_, hmono⟩
  intro n hn
  exact hvalue.trans_le (hmono (Set.mem_Ici.mpr (le_refl _)) (Set.mem_Ici.mpr hn) hn)

/-- A3′ packages only the numerical starting facts after the analytic
pre-cap and tail transports have been proved. -/
theorem betaRange_of_endpoint {rm Nlo : ℝ}
    (hrm : 0 < rm) (hrmhi : rm ≤ 1/2) (hNlo : 1 < Nlo)
    (hstart : 0 < rhoStar Nlo rm)
    (hmargin : Nlo < (6/rm)^2 → 0 < betaDerivativeBound rm Nlo) :
    betaRange rm Nlo := by
  refine ⟨cappedBeta_monotone_from_endpoint hrm hrmhi hNlo hstart
    (fun h => (hmargin h).le), ?_⟩
  intro hinterval
  refine ⟨hmargin hinterval, ?_⟩
  intro n hn
  exact betaDerivativeOn_lower hrm hrmhi hNlo hinterval hn hstart

/-- A4/A4′ package the local starting and cap checks after proving the
closed pre-cap derivative inequality and the quadratic tail transport. -/
theorem bonusConditions_of_endpoints {rm Nlo : ℝ}
    (hrm : 0 < rm) (hrmhi : rm ≤ 1/2) (hNlo : 1 < Nlo)
    (hinterval : Nlo < (6/rm)^2) (hstart : 0 < rhoStar Nlo rm)
    (hf : 0 < lambdaBonusF Nlo rm)
    (hmargin : 0 < rhoStar Nlo rm/2-e2DerivativeBound rm Nlo)
    (hvalue : 0 < bonusTail rm ((6/rm)^2))
    (hderiv : 0 < deriv (bonusTail rm) ((6/rm)^2)) : bonusConditions rm Nlo := by
  have hrscap := rhoStar_pos_of_endpoint hrm.le hrmhi hNlo hinterval.le hstart
  have htail := bonusTail_transport hrscap.le hvalue hderiv.le
  refine ⟨hf, hmargin, ?_, hvalue, hderiv, htail.1, htail.2⟩
  intro n hn
  exact lambdaBonusF_derivWithin_lower hrm hrmhi hNlo hinterval hn

end

end Erdos993Lean.Analytic.V22
