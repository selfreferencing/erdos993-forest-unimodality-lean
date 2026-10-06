import Erdos993Lean.Analytic.HandVariance.Flanks
import Erdos993Lean.Analytic.HandVariance.ContextSound

/-!
# Soundness of the five finite hand-flank bounds

Source: TWIN v1.8 Appendix N.4, `tgt:lem:hand`, and the exact
`Compute.flankBounds` recipe. Positive lower endpoints for both reciprocal
`k` evaluations and an upper enclosure certifying the exact large `N<0`
proviso are retained as explicit coverage guards.
-/

namespace Erdos993Lean.Analytic.HandVariance.Compute

open Real Reserve Erdos993Lean.Analytic.TailCert
open Erdos993Lean.Analytic.TailCert.Compute

/-- Source: fixed-point endpoint interpretation in the flank recipes. -/
theorem flank_loRat_le {v : Ival} {x : ℝ} (h : v.Mem x) : (loRat v : ℝ) ≤ x := by
  rw [show (loRat v : ℝ) = toR v.lo from endpoint_rat_cast v.lo]
  exact h.1

/-- Source: fixed-point endpoint interpretation in the flank recipes. -/
theorem flank_le_hiRat {v : Ival} {x : ℝ} (h : v.Mem x) : x ≤ (hiRat v : ℝ) := by
  rw [show (hiRat v : ℝ) = toR v.hi from endpoint_rat_cast v.hi]
  exact h.2

/-- Source: the closed exp/log calls of `flankBounds`; successful guarded
evaluation encloses the real formula. -/
theorem flank_evalClosed_mem {e : Expr} {v : Ival} (h : evalClosed e = some v) :
    v.Mem (e.evalR (fun _ => 0)) := by
  unfold evalClosed at h
  split_ifs at h with hs
  cases h
  apply Expr.evalI_mem
  · intro i
    simpa only [zeroI, toR_zero] using mem_pt (0 : ℤ)
  · exact hs

/-- Source: the guarded upper logarithm used by the large-flank proviso. -/
theorem flank_logUpper_bound {q u : Rat} (h : logUpper q = some u) :
    log (q : ℝ) ≤ (u : ℝ) := by
  unfold logUpper at h
  dsimp only at h
  split_ifs at h with hs
  cases h
  exact flank_le_hiRat (mem_logI (mem_ofRat q) hs)

def flankNumH (a : Activity) : Rat :=
  1 - loRat (point a.activity.lo a.leftEnd).p +
    gammaRat (parameters a.segment) a.activity.hi * hiRat (point a.activity.lo a.leftEnd).k
def flankNumN (a : Activity) : Rat :=
  capARat (parameters a.segment) a.activity.lo - flankNumH a -
    alphaRat (parameters a.segment) a.activity.hi / loRat (point a.activity.hi 0).k
def flankNumSmallZ (a : Activity) : Rat :=
  gammaRat (parameters a.segment) a.activity.lo + a.Jcap *
    min 0 (gammaRat (parameters a.segment) a.activity.lo / a.activity.hi - flankNumH a * a.leftEnd)
def flankNumLargeN (a : Activity) : Rat :=
  capARat (parameters a.segment) a.activity.lo - 1 - gammaRat (parameters a.segment) a.activity.hi -
    alphaRat (parameters a.segment) a.activity.hi / loRat (point a.activity.hi 3).k
/-- Source: the exact `N^(3)<0` proviso; this upper recipe is a coverage
guard, separate from the lower `N` used in the numerical AC estimate. -/
def flankNumLargeNUpper (a : Activity) : Rat :=
  capARat (parameters a.segment) a.activity.lo - 1 - gammaRat (parameters a.segment) a.activity.hi -
    alphaRat (parameters a.segment) a.activity.hi / hiRat (point a.activity.hi 3).k
def flankNumLargeZ (a : Activity) (er : Ival) : Rat :=
  min (gammaRat (parameters a.segment) a.activity.lo)
    (gammaRat (parameters a.segment) a.activity.lo - a.Jcap * max 0
      (3 * (1 + gammaRat (parameters a.segment) a.activity.hi) -
        gammaRat (parameters a.segment) a.activity.lo * loRat er / a.activity.hi))
def flankNumGlobalZ (a : Activity) (lg : Ival) : Rat :=
  gammaRat (parameters a.segment) a.activity.lo - a.Jcap *
    (1 + gammaRat (parameters a.segment) a.activity.hi) * (hiRat lg - 1)
def flankNumSmallAC (a : Activity) (t : Ival) : Rat :=
  alphaRat (parameters a.segment) a.activity.lo / a.activity.hi +
    (flankNumN a + alphaRat (parameters a.segment) a.activity.lo * loRat t) / a.leftEnd -
    a.Jcap * flankNumH a ^ 2 / flankNumSmallZ a
def flankNumLargeAC (a : Activity) (er : Ival) : Rat :=
  alphaRat (parameters a.segment) a.activity.lo * loRat er / a.activity.hi + flankNumLargeN a / 3 -
    (1 + gammaRat (parameters a.segment) a.activity.hi) ^ 2 * a.Jcap / flankNumLargeZ a er
def flankNumTinyL (a : Activity) : Rat :=
  gammaRat (parameters a.segment) a.activity.lo / a.activity.hi -
    (1 + gammaRat (parameters a.segment) a.activity.hi) / 500
def flankNumLargeL (a : Activity) (er : Ival) : Rat :=
  gammaRat (parameters a.segment) a.activity.lo * loRat er / a.activity.hi -
    3 * (1 + gammaRat (parameters a.segment) a.activity.hi)

def flankLogExpr (a : Activity) : Expr := .log (.rat
  ((1 + gammaRat (parameters a.segment) a.activity.hi) /
    (gammaRat (parameters a.segment) a.activity.lo / a.activity.hi)))
def flankTExpr (a : Activity) : Expr :=
  .maximum 0 (.log (.rat a.activity.lo) - .log (.exp (.rat a.leftEnd) - 1))
def flankLogR (a : Activity) : Rat :=
  (1 + gammaRat (parameters a.segment) a.activity.hi) * a.activity.hi /
    gammaRat (parameters a.segment) a.activity.lo

/-- Source: `flankBounds`, retaining every successful closed evaluation,
the two actual corner points and the source's rational sign provisos. -/
structure FlankEvaluation (a : Activity) where
  logarithm : Ival
  threshold : Ival
  expThree : Ival
  logR : Rat
  log_eval : evalClosed (flankLogExpr a) = some logarithm
  threshold_eval : evalClosed (flankTExpr a) = some threshold
  exp_eval : evalClosed (.exp 3) = some expThree
  logR_eval : logUpper (flankLogR a) = some logR
  left_pos : 0 < a.leftEnd
  left_le_three : a.leftEnd ≤ 3
  cap_nonneg : 0 ≤ a.Jcap
  pa_safe : (point a.activity.lo a.leftEnd).safe = true
  pb_safe : (point a.activity.hi 0).safe = true
  p3_safe : (point a.activity.hi 3).safe = true
  logarithm_lower : 1 ≤ loRat logarithm
  small_numerator_nonneg : 0 ≤ flankNumN a + alphaRat (parameters a.segment) a.activity.lo * loRat threshold
  small_denominator_pos : 0 < flankNumSmallZ a
  largeN_neg : flankNumLargeN a < 0
  large_denominator_pos : 0 < flankNumLargeZ a expThree
  large_threshold : logR ≤ 3
  globalZ_pos : 0 < flankNumGlobalZ a logarithm
  smallAC_pos : 0 < flankNumSmallAC a threshold
  largeAC_pos : 0 < flankNumLargeAC a expThree
  tinyL_pos : 0 < flankNumTinyL a
  largeL_pos : 0 < flankNumLargeL a expThree

/-- Source: the exact five-item `flankBounds` return; all early failures
are excluded by successful evaluation, and each positive item is preserved. -/
theorem flankBounds_evaluation {a : Activity} {xs : List Rat}
    (hresult : flankBounds a = some xs) (hpositive : allPositive xs = true) :
    Nonempty (FlankEvaluation a) := by
  cases hlg : evalClosed (flankLogExpr a) with
  | none =>
    dsimp [flankLogExpr] at hlg
    simp [flankBounds, hlg] at hresult
  | some lg =>
    have hlg' := hlg
    dsimp [flankLogExpr] at hlg'
    cases ht : evalClosed (flankTExpr a) with
    | none =>
      dsimp [flankTExpr] at ht
      simp [flankBounds, hlg', ht] at hresult
    | some tv =>
      have ht' := ht
      dsimp [flankTExpr] at ht'
      cases hr : logUpper (flankLogR a) with
      | none =>
        dsimp [flankLogR] at hr
        simp [flankBounds, hlg', ht', hr] at hresult
      | some rv =>
        have hr' := hr
        dsimp [flankLogR] at hr'
        cases he : evalClosed (.exp 3) with
        | none => simp [flankBounds, hlg', ht', hr', he] at hresult
        | some ev =>
          simp only [flankBounds, Bind.bind, pure, hlg', ht', hr', he,
            Option.bind_some] at hresult
          split_ifs at hresult with hbad hunsafe hlgBad hsmallBad hlargeBad <;> try cases hresult
          have hstart : 0 < a.leftEnd ∧ a.leftEnd ≤ 3 ∧ 0 ≤ a.Jcap := by
            simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hbad
            exact ⟨lt_of_not_ge hbad.1.1, le_of_not_gt hbad.1.2, le_of_not_gt hbad.2⟩
          have hpoints : (point a.activity.lo a.leftEnd).safe = true ∧
              (point a.activity.hi 0).safe = true ∧ (point a.activity.hi 3).safe = true := by
            simpa only [Bool.not_eq_true, Bool.not_eq_false_eq_eq_true,
              Bool.and_eq_true, and_assoc] using hunsafe
          have hsmall : 0 ≤ flankNumN a + alphaRat (parameters a.segment) a.activity.lo * loRat tv ∧
              0 < flankNumSmallZ a := by
            simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hsmallBad
            exact ⟨le_of_not_gt hsmallBad.1, lt_of_not_ge hsmallBad.2⟩
          have hlarge : flankNumLargeN a < 0 ∧ rv ≤ 3 ∧ 0 < flankNumLargeZ a ev := by
            simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hlargeBad
            exact ⟨lt_of_not_ge hlargeBad.1.1, le_of_not_gt hlargeBad.1.2, lt_of_not_ge hlargeBad.2⟩
          have hpos : 0 < flankNumGlobalZ a lg ∧ 0 < flankNumSmallAC a tv ∧
              0 < flankNumLargeAC a ev ∧ 0 < flankNumTinyL a ∧ 0 < flankNumLargeL a ev := by
            simpa only [allPositive, List.all_cons, List.all_nil, Bool.and_eq_true,
              decide_eq_true_eq, and_true, flankNumGlobalZ, flankNumSmallAC,
              flankNumLargeAC, flankNumTinyL, flankNumLargeL, flankNumH,
              flankNumN, flankNumSmallZ, flankNumLargeN, flankNumLargeZ] using hpositive
          exact ⟨{
            logarithm := lg, threshold := tv, expThree := ev, logR := rv,
            log_eval := hlg, threshold_eval := ht, exp_eval := he, logR_eval := hr,
            left_pos := hstart.1, left_le_three := hstart.2.1, cap_nonneg := hstart.2.2,
            pa_safe := hpoints.1, pb_safe := hpoints.2.1, p3_safe := hpoints.2.2,
            logarithm_lower := le_of_not_gt hlgBad,
            small_numerator_nonneg := hsmall.1, small_denominator_pos := hsmall.2,
            largeN_neg := hlarge.1, large_denominator_pos := hlarge.2.2,
            large_threshold := hlarge.2.1, globalZ_pos := hpos.1,
            smallAC_pos := hpos.2.1, largeAC_pos := hpos.2.2.1,
            tinyL_pos := hpos.2.2.2.1, largeL_pos := hpos.2.2.2.2 }⟩

/-- Source: `tgt:lem:hand` (ii), comparison of the square correction
using a nonnegative numerator enclosure and positive denominator enclosure. -/
private theorem nonneg_square_correction {H Hhi Z Zlo j : ℝ}
    (hH : 0 ≤ H) (hHH : H ≤ Hhi) (hj : 0 ≤ j)
    (hZlo : 0 < Zlo) (hZZ : Zlo ≤ Z) :
    j * H ^ 2 / Z ≤ j * Hhi ^ 2 / Zlo := by
  have hZ : 0 < Z := lt_of_lt_of_le hZlo hZZ
  have hsq : H ^ 2 ≤ Hhi ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hHH) (show 0 ≤ Hhi + H by linarith)]
  calc
    j * H ^ 2 / Z ≤ j * Hhi ^ 2 / Z :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hj) hZ.le
    _ ≤ j * Hhi ^ 2 / Zlo :=
      div_le_div_of_nonneg_left (mul_nonneg hj (sq_nonneg Hhi)) hZlo hZZ

/-- Source: `tgt:lem:hand`, rigorous transport of the five flank recipes
from lower/upper primitive enclosures. The exact large `N<0` proviso uses
the upper `k` endpoint, while its AC estimate uses the lower endpoint. -/
theorem flankChecks_of_enclosures (c : Band) {lo hi YL Jcap : ℝ}
    (hlo : 0 < lo) (hhi : 0 < hi) (hYL : 0 < YL) (hJ : 0 ≤ Jcap)
    (haLo : 0 ≤ alpha c lo) (haHi : 0 ≤ alpha c hi)
    (hgLo : 0 ≤ gamma c lo) (hgHi : 0 ≤ gamma c hi)
    {pLo kHi k0Lo k3Lo k3Hi tLo expLo logHi logRHi : ℝ}
    (hp : pLo ≤ msg lo YL) (hk : parentK lo YL ≤ kHi)
    (hk0 : 0 < k0Lo) (hk0le : k0Lo ≤ parentK hi 0)
    (hk3 : 0 < k3Lo) (hk3le : k3Lo ≤ parentK hi 3)
    (hk3hi : parentK hi 3 ≤ k3Hi)
    (ht : tLo ≤ flankSmallT lo YL) (he : expLo ≤ exp 3)
    (hlg : log (flankC1 c hi / flankC2 c lo hi) ≤ logHi)
    (hr : log ((1 + gamma c hi) * hi / gamma c lo) ≤ logRHi)
    (hglobal : 0 < gamma c lo - Jcap * (1 + gamma c hi) * (logHi - 1))
    (hnum : 0 ≤ capA c lo - (1 - pLo + gamma c hi * kHi) -
      alpha c hi / k0Lo + alpha c lo * tLo)
    (hsmallZ : 0 < gamma c lo + Jcap * min 0
      (gamma c lo / hi - (1 - pLo + gamma c hi * kHi) * YL))
    (hsmall : 0 < alpha c lo / hi +
      (capA c lo - (1 - pLo + gamma c hi * kHi) - alpha c hi / k0Lo +
        alpha c lo * tLo) / YL - Jcap * (1 - pLo + gamma c hi * kHi) ^ 2 /
        (gamma c lo + Jcap * min 0
          (gamma c lo / hi - (1 - pLo + gamma c hi * kHi) * YL)))
    (hNupper : capA c lo - 1 - gamma c hi - alpha c hi / k3Hi < 0)
    (hlargeZ : 0 < min (gamma c lo) (gamma c lo - Jcap * max 0
      (3 * (1 + gamma c hi) - gamma c lo * expLo / hi)))
    (hlarge : 0 < alpha c lo * expLo / hi +
      (capA c lo - 1 - gamma c hi - alpha c hi / k3Lo) / 3 -
      (1 + gamma c hi) ^ 2 * Jcap /
      min (gamma c lo) (gamma c lo - Jcap * max 0
        (3 * (1 + gamma c hi) - gamma c lo * expLo / hi)))
    (hr3 : logRHi ≤ 3)
    (htiny : 0 < gamma c lo / hi - (1 + gamma c hi) / 500)
    (hlargel : 0 < gamma c lo * expLo / hi - 3 * (1 + gamma c hi)) :
    FlankChecks c lo hi YL Jcap := by
  let H := 1 - pLo + gamma c hi * kHi
  let N := capA c lo - H - alpha c hi / k0Lo
  let Z := gamma c lo + Jcap * min 0 (gamma c lo / hi - H * YL)
  let N3 := capA c lo - 1 - gamma c hi - alpha c hi / k3Lo
  let Z3 := min (gamma c lo) (gamma c lo - Jcap * max 0
    (3 * (1 + gamma c hi) - gamma c lo * expLo / hi))
  have hH : flankSmallH c lo hi YL ≤ H := by
    have hh := mul_le_mul_of_nonneg_left hk hgHi
    dsimp [flankSmallH, H]
    linarith
  have hHpos : 0 ≤ flankSmallH c lo hi YL := by
    have hp1 := Entropy.msg_lt_one hlo YL
    have hk1 := mul_nonneg hgHi (parentK_pos hlo YL).le
    dsimp [flankSmallH]
    linarith
  have hN : N ≤ flankSmallN c lo hi YL := by
    have hrec := div_le_div_of_nonneg_left haHi hk0 hk0le
    dsimp [N, flankSmallN]
    linarith
  have hnumle : N + alpha c lo * tLo ≤
      flankSmallN c lo hi YL + alpha c lo * flankSmallT lo YL := by
    have ht1 := mul_le_mul_of_nonneg_left ht haLo
    linarith
  have hZ : Z ≤ flankSmallZ c lo hi YL Jcap := by
    have hh := mul_le_mul_of_nonneg_right hH hYL.le
    have hmin : min 0 (gamma c lo / hi - H * YL) ≤
        min 0 (gamma c lo / hi - flankSmallH c lo hi YL * YL) :=
      min_le_min le_rfl (by linarith)
    simpa only [Z, flankSmallZ, add_comm] using
      add_le_add_left (mul_le_mul_of_nonneg_left hmin hJ) (gamma c lo)
  have hZpos : 0 < flankSmallZ c lo hi YL Jcap := lt_of_lt_of_le hsmallZ hZ
  have hcorr := nonneg_square_correction hHpos hH hJ hsmallZ hZ
  have hsmallle : alpha c lo / hi + (N + alpha c lo * tLo) / YL -
      Jcap * H ^ 2 / Z ≤ flankSmallAC c lo hi YL Jcap := by
    have hd := div_le_div_of_nonneg_right hnumle hYL.le
    dsimp [flankSmallAC]
    linarith
  have hN3 : N3 ≤ flankLargeN c lo hi := by
    have hrec := div_le_div_of_nonneg_left haHi hk3 hk3le
    dsimp [N3, flankLargeN]
    linarith
  have hN3upper : flankLargeN c lo hi ≤
      capA c lo - 1 - gamma c hi - alpha c hi / k3Hi := by
    have hrec := div_le_div_of_nonneg_left haHi (parentK_pos hhi 3) hk3hi
    dsimp [flankLargeN]
    linarith
  have heG := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he hgLo) hhi.le
  have heA := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he haLo) hhi.le
  have hZ3 : Z3 ≤ flankLargeZ c lo hi Jcap := by
    have hm : max 0 (3 * (1 + gamma c hi) - gamma c lo * exp 3 / hi) ≤
        max 0 (3 * (1 + gamma c hi) - gamma c lo * expLo / hi) :=
      max_le_max le_rfl (by linarith)
    have hj := mul_le_mul_of_nonneg_left hm hJ
    exact min_le_min le_rfl (by linarith)
  have hZ3pos : 0 < flankLargeZ c lo hi Jcap := lt_of_lt_of_le hlargeZ hZ3
  have hcorr3 := div_le_div_of_nonneg_left
    (mul_nonneg (sq_nonneg (1 + gamma c hi)) hJ) hlargeZ hZ3
  have hlargele : alpha c lo * expLo / hi + N3 / 3 -
      (1 + gamma c hi) ^ 2 * Jcap / Z3 ≤ flankLargeAC c lo hi Jcap := by
    have hn := div_le_div_of_nonneg_right hN3 (show (0 : ℝ) ≤ 3 by norm_num)
    dsimp [flankLargeAC]
    linarith
  have hgloballe : gamma c lo - Jcap * (1 + gamma c hi) * (logHi - 1) ≤
      flankGlobalZ c lo hi Jcap := by
    have hh : log (flankC1 c hi / flankC2 c lo hi) - 1 ≤ logHi - 1 := by linarith
    have hm := mul_le_mul_of_nonneg_left hh
      (mul_nonneg hJ (show 0 ≤ 1 + gamma c hi by linarith))
    dsimp only [flankC1] at hm
    dsimp [flankGlobalZ, flankC1]
    linarith
  exact {
    globalZ_pos := lt_of_lt_of_le hglobal hgloballe
    small_numerator_nonneg := le_trans hnum hnumle
    small_denominator_pos := hZpos
    smallAC_pos := lt_of_lt_of_le hsmall hsmallle
    largeN_neg := lt_of_le_of_lt hN3upper hNupper
    large_denominator_pos := hZ3pos
    largeAC_pos := lt_of_lt_of_le hlarge hlargele
    large_threshold := hr.trans hr3
    tinyL_pos := htiny
    largeL_pos := by dsimp [flankLargeL]; linarith }

/-- Source: the six multiplier rows in `mc:def:curve`. -/
theorem flank_parameters_pos (n : Nat) :
    (0 : ℝ) < (parameters n).a ∧ (0 : ℝ) < (parameters n).g := by
  rcases n with _ | n
  · norm_num [parameters]
  rcases n with _ | n
  · norm_num [parameters]
  rcases n with _ | n
  · norm_num [parameters]
  rcases n with _ | n
  · norm_num [parameters]
  rcases n with _ | n
  · norm_num [parameters]
  have hdef : parameters (n + 5) = ⟨21 / 10, 57 / 100, 39 / 4⟩ := by
    unfold parameters
    split <;> (try omega)
    rfl
  change (0 : ℝ) < (parameters (n + 5)).a ∧ (0 : ℝ) < (parameters (n + 5)).g
  rw [hdef]
  norm_num

/-- Source: `tgt:lem:hand`, the actual five source bounds and all exact
sign provisos, from the successful finite recipe and retained coverage guards. -/
theorem flankBounds_sound {a : Activity} {xs : List Rat}
    (hresult : flankBounds a = some xs) (hpositive : allPositive xs = true)
    (hpbk : 0 < loRat (point a.activity.hi 0).k)
    (hp3k : 0 < loRat (point a.activity.hi 3).k)
    (hNupper : capARat (parameters a.segment) a.activity.lo - 1 -
      gammaRat (parameters a.segment) a.activity.hi -
      alphaRat (parameters a.segment) a.activity.hi / hiRat (point a.activity.hi 3).k < 0) :
    FlankChecks (parameters a.segment).asBand (a.activity.lo : ℝ)
      (a.activity.hi : ℝ) (a.leftEnd : ℝ) (a.Jcap : ℝ) := by
  obtain ⟨v⟩ := flankBounds_evaluation hresult hpositive
  let c := (parameters a.segment).asBand
  let lo : ℝ := a.activity.lo
  let hi : ℝ := a.activity.hi
  let YL : ℝ := a.leftEnd
  let Jcap : ℝ := a.Jcap
  let pLo : ℝ := loRat (point a.activity.lo a.leftEnd).p
  let kHi : ℝ := hiRat (point a.activity.lo a.leftEnd).k
  let k0Lo : ℝ := loRat (point a.activity.hi 0).k
  let k3Lo : ℝ := loRat (point a.activity.hi 3).k
  let k3Hi : ℝ := hiRat (point a.activity.hi 3).k
  let tLo : ℝ := loRat v.threshold
  let expLo : ℝ := loRat v.expThree
  let logHi : ℝ := hiRat v.logarithm
  let logRHi : ℝ := v.logR
  have hlo : 0 < lo := point_activity_pos v.pa_safe
  have hhi : 0 < hi := point_activity_pos v.pb_safe
  have hYL : 0 < YL := by dsimp only [YL]; exact_mod_cast v.left_pos
  have hJ : 0 ≤ Jcap := by dsimp only [Jcap]; exact_mod_cast v.cap_nonneg
  have ha := (flank_parameters_pos a.segment).1
  have hg := (flank_parameters_pos a.segment).2
  have haLo : 0 ≤ alpha c lo := by
    change 0 ≤ ((parameters a.segment).a : ℝ) * (lo / (1 + lo))
    exact (mul_pos ha (div_pos hlo (by linarith))).le
  have haHi : 0 ≤ alpha c hi := by
    change 0 ≤ ((parameters a.segment).a : ℝ) * (hi / (1 + hi))
    exact (mul_pos ha (div_pos hhi (by linarith))).le
  have hgLo : 0 ≤ gamma c lo := by
    change 0 ≤ lo * (3 + lo) / ((parameters a.segment).g : ℝ)
    exact (div_pos (mul_pos hlo (by linarith)) hg).le
  have hgHi : 0 ≤ gamma c hi := by
    change 0 ≤ hi * (3 + hi) / ((parameters a.segment).g : ℝ)
    exact (div_pos (mul_pos hhi (by linarith)) hg).le
  have hpa := point_mem v.pa_safe
  have hpb := point_mem v.pb_safe
  have hp3 := point_mem v.p3_safe
  have hp : pLo ≤ msg lo YL := flank_loRat_le hpa.2.1
  have hk : parentK lo YL ≤ kHi := flank_le_hiRat hpa.2.2.2.1
  have hk0 : 0 < k0Lo := by dsimp only [k0Lo]; exact_mod_cast hpbk
  have hk0le : k0Lo ≤ parentK hi 0 := by
    simpa only [Rat.cast_zero, hi, k0Lo] using flank_loRat_le hpb.2.2.2.1
  have hk3 : 0 < k3Lo := by dsimp only [k3Lo]; exact_mod_cast hp3k
  have hk3le : k3Lo ≤ parentK hi 3 := flank_loRat_le hp3.2.2.2.1
  have hk3hi : parentK hi 3 ≤ k3Hi := flank_le_hiRat hp3.2.2.2.1
  have ht : tLo ≤ flankSmallT lo YL := by
    simpa [flankTExpr, Expr.evalR, flankSmallT, lo, YL, tLo] using
      flank_loRat_le (flank_evalClosed_mem v.threshold_eval)
  have he : expLo ≤ exp 3 := by
    simpa [Expr.evalR, expLo] using flank_loRat_le (flank_evalClosed_mem v.exp_eval)
  have hlg : log (flankC1 c hi / flankC2 c lo hi) ≤ logHi := by
    simpa only [flankLogExpr, Expr.evalR, Rat.cast_div, Rat.cast_add, Rat.cast_one,
      gammaRat_cast, flankC1, flankC2, c, lo, hi, logHi] using
      flank_le_hiRat (flank_evalClosed_mem v.log_eval)
  have hr : log ((1 + gamma c hi) * hi / gamma c lo) ≤ logRHi := by
    simpa only [flankLogR, Rat.cast_div, Rat.cast_mul, Rat.cast_add, Rat.cast_one,
      gammaRat_cast, c, hi, lo, logRHi] using flank_logUpper_bound v.logR_eval
  have hHcast : (flankNumH a : ℝ) = 1 - pLo + gamma c hi * kHi := by
    simp only [flankNumH, Rat.cast_add, Rat.cast_sub, Rat.cast_one, Rat.cast_mul,
      gammaRat_cast, c, pLo, hi, kHi]
  have hNcast : (flankNumN a : ℝ) =
      capA c lo - (1 - pLo + gamma c hi * kHi) - alpha c hi / k0Lo := by
    simp only [flankNumN, Rat.cast_sub, Rat.cast_div, capARat_cast,
      alphaRat_cast, hHcast, c, lo, hi, k0Lo]
  have hSmallZcast : (flankNumSmallZ a : ℝ) = gamma c lo + Jcap * min 0
      (gamma c lo / hi - (1 - pLo + gamma c hi * kHi) * YL) := by
    simp only [flankNumSmallZ, Rat.cast_add, Rat.cast_mul, Rat.cast_min,
      Rat.cast_zero, Rat.cast_sub, Rat.cast_div, gammaRat_cast, hHcast,
      c, lo, hi, Jcap, YL]
  have hLargeNcast : (flankNumLargeN a : ℝ) =
      capA c lo - 1 - gamma c hi - alpha c hi / k3Lo := by
    simp only [flankNumLargeN, Rat.cast_sub, Rat.cast_one, Rat.cast_div,
      capARat_cast, gammaRat_cast, alphaRat_cast, c, lo, hi, k3Lo]
  have hLargeZcast : (flankNumLargeZ a v.expThree : ℝ) = min (gamma c lo)
      (gamma c lo - Jcap * max 0 (3 * (1 + gamma c hi) - gamma c lo * expLo / hi)) := by
    simp only [flankNumLargeZ, Rat.cast_min, Rat.cast_sub, Rat.cast_mul,
      Rat.cast_max, Rat.cast_zero, Rat.cast_add, Rat.cast_one, Rat.cast_ofNat,
      Rat.cast_div, gammaRat_cast, c, lo, hi, Jcap, expLo]
  have hglobal : 0 < gamma c lo - Jcap * (1 + gamma c hi) * (logHi - 1) := by
    have h : (0 : ℝ) < (flankNumGlobalZ a v.logarithm : ℝ) := by exact_mod_cast v.globalZ_pos
    simpa only [flankNumGlobalZ, Rat.cast_sub, Rat.cast_mul, Rat.cast_add,
      Rat.cast_one, gammaRat_cast, c, lo, hi, Jcap, logHi] using h
  have hnum : 0 ≤ capA c lo - (1 - pLo + gamma c hi * kHi) -
      alpha c hi / k0Lo + alpha c lo * tLo := by
    have h : (0 : ℝ) ≤ ((flankNumN a + alphaRat (parameters a.segment) a.activity.lo *
      loRat v.threshold : Rat) : ℝ) := by exact_mod_cast v.small_numerator_nonneg
    simpa only [Rat.cast_add, Rat.cast_mul, hNcast, alphaRat_cast, c, lo, tLo] using h
  have hsmallZ : 0 < gamma c lo + Jcap * min 0
      (gamma c lo / hi - (1 - pLo + gamma c hi * kHi) * YL) := by
    have h : (0 : ℝ) < (flankNumSmallZ a : ℝ) := by exact_mod_cast v.small_denominator_pos
    simpa only [hSmallZcast] using h
  have hsmall : 0 < alpha c lo / hi +
      (capA c lo - (1 - pLo + gamma c hi * kHi) - alpha c hi / k0Lo +
        alpha c lo * tLo) / YL - Jcap * (1 - pLo + gamma c hi * kHi) ^ 2 /
        (gamma c lo + Jcap * min 0
          (gamma c lo / hi - (1 - pLo + gamma c hi * kHi) * YL)) := by
    have h : (0 : ℝ) < (flankNumSmallAC a v.threshold : ℝ) := by exact_mod_cast v.smallAC_pos
    simpa only [flankNumSmallAC, Rat.cast_add, Rat.cast_sub, Rat.cast_div,
      Rat.cast_mul, Rat.cast_pow, alphaRat_cast, hNcast, hHcast, hSmallZcast,
      c, lo, hi, YL, Jcap, tLo] using h
  have hNup : capA c lo - 1 - gamma c hi - alpha c hi / k3Hi < 0 := by
    have h : ((capARat (parameters a.segment) a.activity.lo - 1 -
      gammaRat (parameters a.segment) a.activity.hi -
      alphaRat (parameters a.segment) a.activity.hi / hiRat (point a.activity.hi 3).k : Rat) : ℝ) < 0 :=
      by exact_mod_cast hNupper
    simpa only [Rat.cast_sub, Rat.cast_one, Rat.cast_div, capARat_cast,
      gammaRat_cast, alphaRat_cast, c, lo, hi, k3Hi] using h
  have hlargeZ : 0 < min (gamma c lo) (gamma c lo - Jcap * max 0
      (3 * (1 + gamma c hi) - gamma c lo * expLo / hi)) := by
    have h : (0 : ℝ) < (flankNumLargeZ a v.expThree : ℝ) := by exact_mod_cast v.large_denominator_pos
    simpa only [hLargeZcast] using h
  have hlarge : 0 < alpha c lo * expLo / hi +
      (capA c lo - 1 - gamma c hi - alpha c hi / k3Lo) / 3 -
      (1 + gamma c hi) ^ 2 * Jcap /
      min (gamma c lo) (gamma c lo - Jcap * max 0
        (3 * (1 + gamma c hi) - gamma c lo * expLo / hi)) := by
    have h : (0 : ℝ) < (flankNumLargeAC a v.expThree : ℝ) := by exact_mod_cast v.largeAC_pos
    simpa only [flankNumLargeAC, Rat.cast_sub, Rat.cast_add, Rat.cast_div,
      Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_one, alphaRat_cast,
      gammaRat_cast, hLargeNcast, hLargeZcast, c, lo, hi, expLo, Jcap] using h
  have hr3 : logRHi ≤ 3 := by dsimp only [logRHi]; exact_mod_cast v.large_threshold
  have htiny : 0 < gamma c lo / hi - (1 + gamma c hi) / 500 := by
    have h : (0 : ℝ) < (flankNumTinyL a : ℝ) := by exact_mod_cast v.tinyL_pos
    simpa only [flankNumTinyL, Rat.cast_sub, Rat.cast_add, Rat.cast_div,
      Rat.cast_one, Rat.cast_ofNat, gammaRat_cast, c, lo, hi] using h
  have hlargel : 0 < gamma c lo * expLo / hi - 3 * (1 + gamma c hi) := by
    have h : (0 : ℝ) < (flankNumLargeL a v.expThree : ℝ) := by exact_mod_cast v.largeL_pos
    simpa only [flankNumLargeL, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
      Rat.cast_add, Rat.cast_one, Rat.cast_ofNat, gammaRat_cast, c, lo, hi, expLo] using h
  exact flankChecks_of_enclosures c hlo hhi hYL hJ haLo haHi hgLo hgHi hp hk hk0 hk0le
    hk3 hk3le hk3hi ht he hlg hr hglobal hnum hsmallZ hsmall hNup hlargeZ hlarge hr3 htiny hlargel

#print axioms flankChecks_of_enclosures
#print axioms flankBounds_sound

end Erdos993Lean.Analytic.HandVariance.Compute
