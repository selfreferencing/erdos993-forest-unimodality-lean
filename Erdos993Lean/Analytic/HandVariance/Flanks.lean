import Erdos993Lean.Analytic.HandVariance.Feasibility
import Erdos993Lean.Analytic.HandVariance.Primitives

/-!
# Hand variance: flank bounds and local polygon comparison

Source: `ProofRuns/2026-09-28_analytic_large_n/LEAN/for_tong/TWIN_v1.8/apx_hand.tex`,
Appendix N.4, Lemma `tgt:lem:hand` and Proposition `tgt:prop:red`.
Finite checks enter as explicitly named numeric hypotheses. The actual activity,
parent/child coordinates and reserve comparisons are retained.
-/

namespace Erdos993Lean.Analytic.HandVariance

open Real Reserve

/-- Source: `tgt:prop:red`; the lower comparison evaluated at a polygon point. -/
noncomputable def polygonFloor (c : Band) (lam Y r J : ℝ) : ℝ :=
  min (vertexA c lam Y r J) (vertexAgamma c lam Y r J)

/-- Source: `tgt:prop:red`; the rational penalty with nonpositive slope. -/
noncomputable def rationalPenalty (h2 gamma m J : ℝ) : ℝ := h2 * J / (gamma + m * J)

/-- Source: `tgt:prop:red`; its penalty `M(J)` at the retained parent. -/
noncomputable def polygonPenalty (c : Band) (lam Y J : ℝ) : ℝ :=
  rationalPenalty (hHat c lam Y ^ 2) (gamma c lam) (min 0 (lBar c lam Y)) J

private theorem positive_convex_combination {a b w0 w1 : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hw0 : 0 ≤ w0) (hw1 : 0 ≤ w1) (hw : w0 + w1 = 1) :
    0 < w0 * a + w1 * b := by
  have h0 := mul_le_mul_of_nonneg_left (min_le_left a b) hw0
  have h1 := mul_le_mul_of_nonneg_left (min_le_right a b) hw1
  have hsum : w0 * min a b + w1 * min a b = min a b := by
    rw [← add_mul, hw, one_mul]
  have hm : 0 < min a b := lt_min ha hb
  linarith

/-- Source: `tgt:prop:red`; the rational penalty increases with its coordinate
where its two denominators are positive. -/
theorem rationalPenalty_mono {h2 g m J0 J1 : ℝ}
    (hh2 : 0 ≤ h2) (hg : 0 < g) (hJ : J0 ≤ J1)
    (hd0 : 0 < g + m * J0) (hd1 : 0 < g + m * J1) :
    rationalPenalty h2 g m J0 ≤ rationalPenalty h2 g m J1 := by
  unfold rationalPenalty
  apply (div_le_div_iff₀ hd0 hd1).mpr
  have hprod := mul_nonneg (mul_nonneg hh2 hg.le) (sub_nonneg.mpr hJ)
  nlinarith

/-- Source: `tgt:prop:red`; the exact convexity gap for its rational penalty.
This identity supplies an algebraic proof with no higher regularity assumptions. -/
theorem rationalPenalty_mix_gap {h2 g m J0 J1 w0 w1 : ℝ}
    (hw : w0 + w1 = 1)
    (hd0 : g + m * J0 ≠ 0) (hd1 : g + m * J1 ≠ 0)
    (hdmix : g + m * (w0 * J0 + w1 * J1) ≠ 0) :
    w0 * rationalPenalty h2 g m J0 + w1 * rationalPenalty h2 g m J1 -
      rationalPenalty h2 g m (w0 * J0 + w1 * J1) =
      -h2 * g * m * w0 * w1 * (J0 - J1) ^ 2 /
        ((g + m * J0) * (g + m * J1) * (g + m * (w0 * J0 + w1 * J1))) := by
  have hw1 : w1 = 1 - w0 := by linarith
  unfold rationalPenalty
  rw [hw1] at hdmix ⊢
  generalize hd0eq : g + m * J0 = d0 at hd0 ⊢
  generalize hd1eq : g + m * J1 = d1 at hd1 ⊢
  generalize hdmeq : g + m * (w0 * J0 + (1 - w0) * J1) = dm at hdmix ⊢
  field_simp [hd0, hd1, hdmix]
  rw [← hd0eq, ← hd1eq, ← hdmeq]
  ring

/-- Source: `tgt:prop:red`; convexity of the penalty for nonpositive slope,
on the full positive-denominator domain. -/
theorem rationalPenalty_mix_le {h2 g m J0 J1 w0 w1 : ℝ}
    (hh2 : 0 ≤ h2) (hg : 0 < g) (hm : m ≤ 0)
    (hw0 : 0 ≤ w0) (hw1 : 0 ≤ w1) (hw : w0 + w1 = 1)
    (hd0 : 0 < g + m * J0) (hd1 : 0 < g + m * J1) :
    rationalPenalty h2 g m (w0 * J0 + w1 * J1) ≤
      w0 * rationalPenalty h2 g m J0 + w1 * rationalPenalty h2 g m J1 := by
  have hdenEq : g + m * (w0 * J0 + w1 * J1) =
      w0 * (g + m * J0) + w1 * (g + m * J1) := by
    have hconst : w0 * g + w1 * g = g := by rw [← add_mul, hw, one_mul]
    nlinarith
  have hdmix : 0 < g + m * (w0 * J0 + w1 * J1) := by
    rw [hdenEq]
    exact positive_convex_combination hd0 hd1 hw0 hw1 hw
  have hgap := rationalPenalty_mix_gap (h2 := h2) hw hd0.ne' hd1.ne' hdmix.ne'
  have hnegm : 0 ≤ -m := neg_nonneg.mpr hm
  have hnonneg : 0 ≤ h2 * g * (-m) * w0 * w1 * (J0 - J1) ^ 2 /
      ((g + m * J0) * (g + m * J1) * (g + m * (w0 * J0 + w1 * J1))) := by
    positivity
  have hsign : -h2 * g * m * w0 * w1 * (J0 - J1) ^ 2 /
      ((g + m * J0) * (g + m * J1) * (g + m * (w0 * J0 + w1 * J1))) =
      h2 * g * (-m) * w0 * w1 * (J0 - J1) ^ 2 /
      ((g + m * J0) * (g + m * J1) * (g + m * (w0 * J0 + w1 * J1))) := by ring
  rw [hsign] at hgap
  linarith

/-- Source: `tgt:prop:red`; the denominator of `M` is positive when the
original reserve denominator and `γ` are positive. -/
theorem polygonPenalty_den_pos {c : Band} {lam Y J : ℝ}
    (hγ : 0 < gamma c lam) (hZ : 0 < zBar c lam Y J) :
    0 < gamma c lam + min 0 (lBar c lam Y) * J := by
  by_cases hL : 0 ≤ lBar c lam Y
  · simpa only [min_eq_left hL, zero_mul, add_zero] using hγ
  · have hL' : lBar c lam Y ≤ 0 := (lt_of_not_ge hL).le
    simpa only [min_eq_right hL', zBar, mul_comm] using hZ

/-- Source: `tgt:prop:red`; the source's exact equality
`min(A,Aγ) = α e + N/Y + α r - M(J)`. -/
theorem polygonFloor_eq {c : Band} {lam Y r J : ℝ}
    (hγ : 0 < gamma c lam) (hZ : 0 < zBar c lam Y J) :
    polygonFloor c lam Y r J =
      alpha c lam * parentE lam Y + nTerm c lam Y / Y + alpha c lam * r -
        polygonPenalty c lam Y J := by
  have hdiff := vertexA_sub_vertexAgamma c lam Y r J hγ.ne' hZ.ne'
  unfold polygonFloor
  by_cases hL : 0 ≤ lBar c lam Y
  · have hsign : 0 ≤ hHat c lam Y ^ 2 * lBar c lam Y * J ^ 2 /
        (gamma c lam * zBar c lam Y J) := by positivity
    have hle : vertexAgamma c lam Y r J ≤ vertexA c lam Y r J := by linarith
    rw [min_eq_right hle]
    unfold vertexAgamma polygonPenalty rationalPenalty
    simp only [min_eq_left hL, zero_mul, add_zero]
    ring
  · have hL' : lBar c lam Y ≤ 0 := (lt_of_not_ge hL).le
    have hsign : hHat c lam Y ^ 2 * lBar c lam Y * J ^ 2 /
        (gamma c lam * zBar c lam Y J) ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hL') (sq_nonneg _))
        (mul_pos hγ hZ).le
    have hle : vertexA c lam Y r J ≤ vertexAgamma c lam Y r J := by linarith
    rw [min_eq_left hle]
    unfold vertexA polygonPenalty rationalPenalty zBar
    simp only [min_eq_right hL']
    rw [mul_comm J (lBar c lam Y)]
    ring

/-- Source: `tgt:prop:red`; increasing the retained polygon coordinate `r`
increases its lower comparison when `α` is nonnegative. -/
theorem polygonFloor_mono_r {c : Band} {lam Y r0 r1 J : ℝ}
    (hα : 0 ≤ alpha c lam) (hr : r0 ≤ r1) :
    polygonFloor c lam Y r0 J ≤ polygonFloor c lam Y r1 J := by
  have hprod := mul_le_mul_of_nonneg_left hr hα
  unfold polygonFloor
  apply min_le_min <;> dsimp [vertexA, vertexAgamma] <;> linarith

/-- Source: `tgt:prop:red`; increasing `J` decreases the lower comparison,
with positivity of the actual two denominators explicitly retained. -/
theorem polygonFloor_antitone_J {c : Band} {lam Y r J0 J1 : ℝ}
    (hγ : 0 < gamma c lam) (hJ : J0 ≤ J1)
    (hZ0 : 0 < zBar c lam Y J0) (hZ1 : 0 < zBar c lam Y J1) :
    polygonFloor c lam Y r J1 ≤ polygonFloor c lam Y r J0 := by
  have hmono := rationalPenalty_mono (sq_nonneg (hHat c lam Y)) hγ hJ
    (polygonPenalty_den_pos hγ hZ0) (polygonPenalty_den_pos hγ hZ1)
  rw [polygonFloor_eq hγ hZ0, polygonFloor_eq hγ hZ1]
  unfold polygonPenalty
  linarith

/-- Source: `tgt:prop:red`; the lower comparison is concave along every
affine polygon edge, with the actual endpoint coordinates and denominator
certificates retained. This is the mixture interface for the finite polygon chain. -/
theorem polygonFloor_mix_le {c : Band} {lam Y r0 r1 J0 J1 w0 w1 : ℝ}
    (hγ : 0 < gamma c lam)
    (hZ0 : 0 < zBar c lam Y J0) (hZ1 : 0 < zBar c lam Y J1)
    (hw0 : 0 ≤ w0) (hw1 : 0 ≤ w1) (hw : w0 + w1 = 1) :
    w0 * polygonFloor c lam Y r0 J0 + w1 * polygonFloor c lam Y r1 J1 ≤
      polygonFloor c lam Y (w0 * r0 + w1 * r1) (w0 * J0 + w1 * J1) := by
  have hZeq : zBar c lam Y (w0 * J0 + w1 * J1) =
      w0 * zBar c lam Y J0 + w1 * zBar c lam Y J1 := by
    unfold zBar
    have hconst : w0 * gamma c lam + w1 * gamma c lam = gamma c lam := by
      rw [← add_mul, hw, one_mul]
    nlinarith
  have hZmix : 0 < zBar c lam Y (w0 * J0 + w1 * J1) := by
    rw [hZeq]
    exact positive_convex_combination hZ0 hZ1 hw0 hw1 hw
  have hpen := rationalPenalty_mix_le (sq_nonneg (hHat c lam Y)) hγ
    (min_le_left (0 : ℝ) (lBar c lam Y)) hw0 hw1 hw
    (polygonPenalty_den_pos hγ hZ0) (polygonPenalty_den_pos hγ hZ1)
  rw [polygonFloor_eq hγ hZ0, polygonFloor_eq hγ hZ1, polygonFloor_eq hγ hZmix]
  unfold polygonPenalty
  have hconst : w0 * (alpha c lam * parentE lam Y + nTerm c lam Y / Y) +
      w1 * (alpha c lam * parentE lam Y + nTerm c lam Y / Y) =
      alpha c lam * parentE lam Y + nTerm c lam Y / Y := by
    rw [← add_mul, hw, one_mul]
  nlinarith

/-! ## Exact functions submitted to the five flank checks -/

/-- Source: `tgt:lem:hand` (i), the constant `c₁`. -/
noncomputable def flankC1 (c : Band) (hi : ℝ) : ℝ := 1 + gamma c hi

/-- Source: `tgt:lem:hand` (i), the constant `c₂`. -/
noncomputable def flankC2 (c : Band) (lo hi : ℝ) : ℝ := gamma c lo / hi

/-- Source: `tgt:lem:hand` (i), the global denominator lower bound. -/
noncomputable def flankGlobalZ (c : Band) (lo hi Jcap : ℝ) : ℝ :=
  gamma c lo - Jcap * flankC1 c hi * (log (flankC1 c hi / flankC2 c lo hi) - 1)

/-- Source: `tgt:lem:hand` (ii), the feasible child threshold `t_L`. -/
noncomputable def flankSmallT (lo YL : ℝ) : ℝ :=
  max 0 (log lo - log (exp YL - 1))

/-- Source: `tgt:lem:hand` (ii), the upper enclosure `ĥ_hi`. -/
noncomputable def flankSmallH (c : Band) (lo hi YL : ℝ) : ℝ :=
  1 - msg lo YL + gamma c hi * parentK lo YL

/-- Source: `tgt:lem:hand` (ii), the lower enclosure `N_lo`. -/
noncomputable def flankSmallN (c : Band) (lo hi YL : ℝ) : ℝ :=
  capA c lo - flankSmallH c lo hi YL - alpha c hi / parentK hi 0

/-- Source: `tgt:lem:hand` (ii), the small-parent denominator enclosure. -/
noncomputable def flankSmallZ (c : Band) (lo hi YL Jcap : ℝ) : ℝ :=
  gamma c lo + Jcap * min 0 (gamma c lo / hi - flankSmallH c lo hi YL * YL)

/-- Source: `tgt:lem:hand` (ii), the checked AC lower bound. -/
noncomputable def flankSmallAC (c : Band) (lo hi YL Jcap : ℝ) : ℝ :=
  alpha c lo / hi + (flankSmallN c lo hi YL + alpha c lo * flankSmallT lo YL) / YL -
    Jcap * flankSmallH c lo hi YL ^ 2 / flankSmallZ c lo hi YL Jcap

/-- Source: `tgt:lem:hand` (iii), the lower enclosure `N_lo^(3)`. -/
noncomputable def flankLargeN (c : Band) (lo hi : ℝ) : ℝ :=
  capA c lo - 1 - gamma c hi - alpha c hi / parentK hi 3

/-- Source: `tgt:lem:hand` (iii), the large-parent denominator enclosure. -/
noncomputable def flankLargeZ (c : Band) (lo hi Jcap : ℝ) : ℝ :=
  min (gamma c lo) (gamma c lo -
    Jcap * max 0 (3 * (1 + gamma c hi) - gamma c lo * exp 3 / hi))

/-- Source: `tgt:lem:hand` (iii), the checked AC lower bound. -/
noncomputable def flankLargeAC (c : Band) (lo hi Jcap : ℝ) : ℝ :=
  alpha c lo * exp 3 / hi + flankLargeN c lo hi / 3 -
    (1 + gamma c hi) ^ 2 * Jcap / flankLargeZ c lo hi Jcap

/-- Source: `tgt:lem:hand` (iv), the tiny-parent `L̄` endpoint check. -/
noncomputable def flankTinyL (c : Band) (lo hi : ℝ) : ℝ :=
  gamma c lo / hi - (1 + gamma c hi) / 500

/-- Source: `tgt:lem:hand` (iv), the large-parent `L̄` endpoint check. -/
noncomputable def flankLargeL (c : Band) (lo hi : ℝ) : ℝ :=
  gamma c lo * exp 3 / hi - 3 * (1 + gamma c hi)

/-- Source: `tgt:lem:hand`, its five finite checks and their explicitly
stated provisos. This record contains only the numeric hypotheses, retaining
their concrete analytic functions for the finite checker linkage. -/
structure FlankChecks (c : Band) (lo hi YL Jcap : ℝ) : Prop where
  globalZ_pos : 0 < flankGlobalZ c lo hi Jcap
  small_numerator_nonneg : 0 ≤ flankSmallN c lo hi YL + alpha c lo * flankSmallT lo YL
  small_denominator_pos : 0 < flankSmallZ c lo hi YL Jcap
  smallAC_pos : 0 < flankSmallAC c lo hi YL Jcap
  largeN_neg : flankLargeN c lo hi < 0
  large_denominator_pos : 0 < flankLargeZ c lo hi Jcap
  largeAC_pos : 0 < flankLargeAC c lo hi Jcap
  large_threshold : log ((1 + gamma c hi) * hi / gamma c lo) ≤ 3
  tinyL_pos : 0 < flankTinyL c lo hi
  largeL_pos : 0 < flankLargeL c lo hi

/-- Source: `tgt:lem:hand`, monotonicity of `q=λ/(1+λ)` on positive activities. -/
theorem flank_actQ_mono {lo hi : ℝ} (hlo : 0 < lo) (h : lo ≤ hi) :
    actQ lo ≤ actQ hi := by
  unfold actQ
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  linarith

/-- Source: `tgt:lem:hand`, monotonicity of the segment multiplier `α`. -/
theorem flank_alpha_mono {c : Band} (hc : BandSide c) {lo hi : ℝ}
    (hlo : 0 < lo) (h : lo ≤ hi) : alpha c lo ≤ alpha c hi := by
  have ha : (0 : ℝ) ≤ c.aCoef := by exact_mod_cast hc.2.2.2.2.1.le
  exact mul_le_mul_of_nonneg_left (flank_actQ_mono hlo h) ha

/-- Source: `tgt:lem:hand`, monotonicity of the segment multiplier `γ`. -/
theorem flank_gamma_mono {c : Band} (hc : BandSide c) {lo hi : ℝ}
    (hlo : 0 < lo) (h : lo ≤ hi) : gamma c lo ≤ gamma c hi := by
  have hg : (0 : ℝ) ≤ c.gDen := by exact_mod_cast hc.2.2.2.2.2.le
  unfold gamma
  apply div_le_div_of_nonneg_right _ hg
  exact mul_le_mul h (by linarith) (by linarith) (by linarith)

/-- Source: `tgt:lem:hand`, monotonicity of the segment cap `A_D`. -/
theorem flank_capA_mono {c : Band} (hc : BandSide c) {lo hi : ℝ}
    (hlo : 0 < lo) (h : lo ≤ hi) : capA c lo ≤ capA c hi := by
  have hD := hc.one_le_D
  have hq := mul_le_mul_of_nonneg_left (flank_actQ_mono hlo h)
    (show 0 ≤ (c.D : ℝ) - 1 by linarith)
  unfold capA
  linarith

/-- Source: `tgt:lem:hand` (i–iv), positivity of the retained `ĥ`. -/
theorem flank_hHat_pos {c : Band} (hc : BandSide c) {lam : ℝ}
    (hlam : 0 < lam) (Y : ℝ) : 0 < hHat c lam Y := by
  have hp := Entropy.msg_lt_one hlam Y
  have hk := parentK_pos hlam Y
  have hg := hc.gamma_pos hlam
  change 0 < 1 - msg lam Y + gamma c lam * parentK lam Y
  exact add_pos (by linarith) (mul_pos hg hk)

/-- Source: `tgt:lem:hand` (i,iii,iv), the global upper enclosure for `ĥ`. -/
theorem flank_hHat_le {c : Band} (hc : BandSide c) {lam hi : ℝ}
    (hlam : 0 < lam) (hhi : lam ≤ hi) (Y : ℝ) :
    hHat c lam Y ≤ 1 + gamma c hi := by
  have hp := Entropy.msg_pos hlam Y
  have hk := Tails.msg_div_lmass_le_one hlam Y
  have hg := hc.gamma_pos hlam
  have hmul := mul_le_mul_of_nonneg_left hk hg.le
  have hgam := flank_gamma_mono hc hlam hhi
  change (1 - msg lam Y) + gamma c lam * parentK lam Y ≤ _
  change parentK lam Y ≤ 1 at hk
  change gamma c lam * parentK lam Y ≤ gamma c lam * 1 at hmul
  linarith

/-- Source: `tgt:lem:hand` (i,iv), the activity endpoint enclosure for `γe`. -/
theorem flank_gamma_parentE_ge {c : Band} (hc : BandSide c) {lo lam hi Y : ℝ}
    (hlo : 0 < lo) (hl : lo ≤ lam) (hh : lam ≤ hi) :
    gamma c lo * exp Y / hi ≤ gamma c lam * parentE lam Y := by
  have hlam : 0 < lam := lt_of_lt_of_le hlo hl
  have hhi : 0 < hi := lt_of_lt_of_le hlam hh
  have hγ := hc.gamma_pos hlo
  have hγl := flank_gamma_mono hc hlo hl
  have he := div_le_div_of_nonneg_left (exp_pos Y).le hlam hh
  have he0 : 0 ≤ exp Y / hi := by positivity
  have hmul := mul_le_mul hγl he he0 (hc.gamma_pos hlam).le
  simpa only [parentE, mul_div_assoc] using hmul

/-- Source: `tgt:lem:hand` (iv), its exponential envelope, valid for every
nonnegative parent log-mass. -/
theorem flank_lBar_exp_lower {c : Band} (hc : BandSide c) {lo lam hi Y : ℝ}
    (hlo : 0 < lo) (hl : lo ≤ lam) (hh : lam ≤ hi) (hY : 0 ≤ Y) :
    gamma c lo * exp Y / hi - (1 + gamma c hi) * Y ≤ lBar c lam Y := by
  have he := flank_gamma_parentE_ge hc hlo hl hh (Y := Y)
  have hhY := mul_le_mul_of_nonneg_right
    (flank_hHat_le hc (lt_of_lt_of_le hlo hl) hh Y) hY
  unfold lBar
  linarith

/-- Source: `tgt:lem:hand` (iv), its tiny-parent linear envelope. -/
theorem flank_lBar_linear_lower {c : Band} (hc : BandSide c) {lo lam hi Y : ℝ}
    (hlo : 0 < lo) (hl : lo ≤ lam) (hh : lam ≤ hi) (hY : 0 ≤ Y) :
    gamma c lo / hi - (1 + gamma c hi) * Y ≤ lBar c lam Y := by
  have hhi : 0 < hi := lt_of_lt_of_le hlo (hl.trans hh)
  have he := Real.one_le_exp_iff.mpr hY
  have hmul := mul_le_mul_of_nonneg_left he (hc.gamma_pos hlo).le
  have hdiv := div_le_div_of_nonneg_right hmul hhi.le
  have hL := flank_lBar_exp_lower hc hlo hl hh hY
  simp only [mul_one] at hdiv
  linarith

/-- Source: `tgt:lem:hand` (i), the exact maximum of `c₁Y-c₂exp Y`. -/
theorem flank_exp_peak {c1 c2 Y : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) :
    c1 * Y - c2 * exp Y ≤ c1 * (log (c1 / c2) - 1) := by
  have hratio : 0 < c1 / c2 := div_pos hc1 hc2
  have he := Real.add_one_le_exp (Y - log (c1 / c2))
  rw [Real.exp_sub, Real.exp_log hratio] at he
  have hm := mul_le_mul_of_nonneg_left he hc1.le
  have hid : c1 * (exp Y / (c1 / c2)) = c2 * exp Y := by
    field_simp [hc1.ne', hc2.ne']
  rw [hid] at hm
  nlinarith

/-- Source: `tgt:lem:hand` (iii,iv), the exponential envelope is increasing
to the right of any point above its logarithmic threshold. -/
theorem flank_exp_envelope_mono {c1 c2 a Y : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2)
    (hthreshold : log (c1 / c2) ≤ a) (haY : a ≤ Y) :
    c2 * exp a - c1 * a ≤ c2 * exp Y - c1 * Y := by
  have hratio : 0 < c1 / c2 := div_pos hc1 hc2
  have hroot : c1 / c2 ≤ exp a := (Real.log_le_iff_le_exp hratio).mp hthreshold
  have hroot' : c1 ≤ c2 * exp a := by
    simpa only [mul_comm] using (div_le_iff₀ hc2).mp hroot
  have he := Real.add_one_le_exp (Y - a)
  rw [Real.exp_sub] at he
  have hm := mul_le_mul_of_nonneg_left he (mul_pos hc2 (exp_pos a)).le
  have hid : c2 * exp a * (exp Y / exp a) = c2 * exp Y := by
    field_simp [Real.exp_ne_zero a]
  rw [hid] at hm
  have hprod := mul_nonneg (show 0 ≤ c2 * exp a - c1 by linarith)
    (show 0 ≤ Y - a by linarith)
  nlinarith

/-- Source: `tgt:lem:hand` (iii,iv), the source threshold and the envelope
at `Y=3`, with no numerical approximation. -/
theorem flank_lBar_large_lower {c : Band} (hc : BandSide c) {lo lam hi Y : ℝ}
    (hlo : 0 < lo) (hl : lo ≤ lam) (hh : lam ≤ hi) (hY : 3 ≤ Y)
    (hthreshold : log ((1 + gamma c hi) * hi / gamma c lo) ≤ 3) :
    flankLargeL c lo hi ≤ lBar c lam Y := by
  have hhi : 0 < hi := lt_of_lt_of_le hlo (hl.trans hh)
  have hc1 : 0 < 1 + gamma c hi := by linarith [hc.gamma_pos hhi]
  have hc2 : 0 < gamma c lo / hi := div_pos (hc.gamma_pos hlo) hhi
  have hlog : log ((1 + gamma c hi) / (gamma c lo / hi)) ≤ 3 := by
    have hid : (1 + gamma c hi) / (gamma c lo / hi) =
        (1 + gamma c hi) * hi / gamma c lo := by field_simp
    rw [hid]
    exact hthreshold
  have henv := flank_exp_envelope_mono hc1 hc2 hlog hY
  have hL := flank_lBar_exp_lower hc hlo hl hh (show 0 ≤ Y by linarith)
  unfold flankLargeL
  simp only [div_mul_eq_mul_div] at henv
  linarith

/-- Source: `tgt:lem:hand` (iv); a positive endpoint check proves `L̄>0`
throughout the tiny-parent tail. -/
theorem flank_lBar_tiny_pos {c : Band} (hc : BandSide c) {lo lam hi Y : ℝ}
    (hlo : 0 < lo) (hl : lo ≤ lam) (hh : lam ≤ hi)
    (hY : 0 ≤ Y) (hYhi : Y ≤ 1 / 500) (hcheck : 0 < flankTinyL c lo hi) :
    0 < lBar c lam Y := by
  have hhi : 0 < hi := lt_of_lt_of_le hlo (hl.trans hh)
  have hmul := mul_le_mul_of_nonneg_left hYhi
    (show 0 ≤ 1 + gamma c hi by linarith [hc.gamma_pos hhi])
  have hL := flank_lBar_linear_lower hc hlo hl hh hY
  unfold flankTinyL at hcheck
  simp only [mul_one_div] at hmul
  linarith

/-- Source: `tgt:lem:hand` (iv); a positive endpoint check proves `L̄>0`
throughout the large-parent tail. -/
theorem flank_lBar_large_pos {c : Band} (hc : BandSide c) {lo lam hi Y : ℝ}
    (hlo : 0 < lo) (hl : lo ≤ lam) (hh : lam ≤ hi) (hY : 3 ≤ Y)
    (hthreshold : log ((1 + gamma c hi) * hi / gamma c lo) ≤ 3)
    (hcheck : 0 < flankLargeL c lo hi) : 0 < lBar c lam Y :=
  lt_of_lt_of_le hcheck (flank_lBar_large_lower hc hlo hl hh hY hthreshold)

/-- Source: `tgt:lem:hand` (i); the source multipliers make the peak
nonnegative. This sign is needed when replacing the actual child `J` by its cap. -/
theorem flank_peak_nonneg {c : Band} (hc : BandSide c) {lo hi : ℝ}
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (hg9 : (9 : ℝ) ≤ c.gDen) :
    0 ≤ flankC1 c hi * (log (flankC1 c hi / flankC2 c lo hi) - 1) := by
  have hhi : 0 < hi := lt_of_lt_of_le hlo hlohi
  have hg : (0 : ℝ) < c.gDen := by linarith
  have hγlo := hc.gamma_pos hlo
  have hγhi := hc.gamma_pos hhi
  have hγ := flank_gamma_mono hc hlo hlohi
  have hid : (1 + gamma c lo) * lo - 3 * gamma c lo =
      lo / (c.gDen : ℝ) * ((c.gDen : ℝ) - 9 + lo ^ 2) := by
    unfold gamma
    field_simp [hg.ne']
    ring
  have hbase : 3 * gamma c lo ≤ (1 + gamma c lo) * lo := by
    have hgdiff : 0 ≤ (c.gDen : ℝ) - 9 := by linarith
    have hnn : 0 ≤ lo / (c.gDen : ℝ) * ((c.gDen : ℝ) - 9 + lo ^ 2) := by positivity
    linarith
  have hcorner := mul_le_mul (show 1 + gamma c lo ≤ 1 + gamma c hi by linarith)
    hlohi hlo.le (show 0 ≤ 1 + gamma c hi by linarith)
  have hratio : (3 : ℝ) ≤ (1 + gamma c hi) / (gamma c lo / hi) := by
    rw [le_div_iff₀ (div_pos hγlo hhi)]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hhi).mpr
    nlinarith
  have hratpos : 0 < (1 + gamma c hi) / (gamma c lo / hi) := by positivity
  have hlog : 1 ≤ log ((1 + gamma c hi) / (gamma c lo / hi)) :=
    (Real.le_log_iff_exp_le hratpos).mpr (Real.exp_one_lt_three.le.trans hratio)
  unfold flankC1 flankC2
  exact mul_nonneg (show 0 ≤ 1 + gamma c hi by linarith) (by linarith)

/-- Source: Table `mc:tab:curve`; the six source denominators are at least
nine, supplying the peak sign without an added finite-check obligation. -/
theorem segment_gDen_ge_nine (s : Segment) : (9 : ℝ) ≤ s.band.gDen := by
  cases s <;> norm_num [Segment.band]

/-- Source: `tgt:lem:hand` (i–iii), the denominator comparison from a
lower enclosure of `L̄`, retaining the actual child coordinate. -/
theorem flank_zBar_lower {c : Band} {lam Y J Jcap gLo Llo : ℝ}
    (hγ : gLo ≤ gamma c lam) (hL : Llo ≤ lBar c lam Y)
    (hJ0 : 0 ≤ J) (hJcap : J ≤ Jcap) :
    gLo + Jcap * min 0 Llo ≤ zBar c lam Y J := by
  have hm := min_le_left (0 : ℝ) Llo
  have hmL := (min_le_right (0 : ℝ) Llo).trans hL
  have hcap := mul_le_mul_of_nonpos_right hJcap hm
  have hactual := mul_le_mul_of_nonneg_left hmL hJ0
  unfold zBar
  linarith

/-- Source: `tgt:lem:hand` (i), its global `Z̄` enclosure, with the exact
nonnegative peak sign supplied explicitly for a general multiplier profile. -/
theorem flank_zBar_global {c : Band} (hc : BandSide c) {lo lam hi T Y Jcap : ℝ}
    (hlo : 0 < lo) (hl : lo ≤ lam) (hh : lam ≤ hi) (hY : 0 ≤ Y)
    (hT : 0 ≤ T) (hJcap : coefJ lam T ≤ Jcap)
    (hpeak : 0 ≤ flankC1 c hi * (log (flankC1 c hi / flankC2 c lo hi) - 1)) :
    flankGlobalZ c lo hi Jcap ≤ zBar c lam Y (coefJ lam T) := by
  have hlam : 0 < lam := lt_of_lt_of_le hlo hl
  have hhi : 0 < hi := lt_of_lt_of_le hlam hh
  have hc1 : 0 < flankC1 c hi := by
    unfold flankC1
    linarith [hc.gamma_pos hhi]
  have hc2 : 0 < flankC2 c lo hi := div_pos (hc.gamma_pos hlo) hhi
  have henv := flank_lBar_exp_lower hc hlo hl hh hY
  have hmax := flank_exp_peak (Y := Y) hc1 hc2
  have hL : -(flankC1 c hi * (log (flankC1 c hi / flankC2 c lo hi) - 1)) ≤
      lBar c lam Y := by
    unfold flankC1 flankC2 at hmax
    rw [div_mul_eq_mul_div] at hmax
    dsimp [flankC1, flankC2]
    linarith
  have hZ := flank_zBar_lower (flank_gamma_mono hc hlo hl) hL
    (Tails.coefJ_nonneg hlam hT) hJcap
  rw [min_eq_right (neg_nonpos.mpr hpeak)] at hZ
  unfold flankGlobalZ
  nlinarith

/-- Source: `tgt:lem:hand` (i), for every source multiplier segment. -/
theorem segment_flank_zBar_global (s : Segment) {lo lam hi T Y Jcap : ℝ}
    (hlo : 0 < lo) (hl : lo ≤ lam) (hh : lam ≤ hi) (hY : 0 ≤ Y)
    (hT : 0 ≤ T) (hJcap : coefJ lam T ≤ Jcap) :
    flankGlobalZ s.band lo hi Jcap ≤ zBar s.band lam Y (coefJ lam T) := by
  exact flank_zBar_global (segment_bandSide s) hlo hl hh hY hT hJcap
    (flank_peak_nonneg (segment_bandSide s) hlo (hl.trans hh) (segment_gDen_ge_nine s))

/-- Source: `tgt:lem:hand` (ii,iii), its bounded square correction. -/
theorem flank_square_correction_le {c : Band} {lam Y J Jcap Hhi Zlo : ℝ}
    (hJ0 : 0 ≤ J) (hJcap : J ≤ Jcap)
    (hH0 : 0 ≤ hHat c lam Y) (hH : hHat c lam Y ≤ Hhi)
    (hZlo : 0 < Zlo) (hZ : Zlo ≤ zBar c lam Y J) :
    J * hHat c lam Y ^ 2 / zBar c lam Y J ≤ Jcap * Hhi ^ 2 / Zlo := by
  have hJcap0 : 0 ≤ Jcap := hJ0.trans hJcap
  have hHsq : hHat c lam Y ^ 2 ≤ Hhi ^ 2 := by nlinarith
  have hnum := mul_le_mul hJcap hHsq (sq_nonneg _) hJcap0
  have hz : 0 < zBar c lam Y J := lt_of_lt_of_le hZlo hZ
  have hfrac := div_le_div_of_nonneg_right hnum hz.le
  have hden := div_le_div_of_nonneg_left (mul_nonneg hJcap0 (sq_nonneg Hhi)) hZlo hZ
  exact hfrac.trans hden

/-- Source: `tgt:lem:hand` (ii); the parent rectangle supplies its exact
`ĥ` and `N` enclosures from the primitive corners. -/
theorem flank_small_parent_enclosures {c : Band} (hc : BandSide c)
    {lo lam hi Y YL : ℝ} (hlo : 0 < lo) (hl : lo ≤ lam) (hh : lam ≤ hi)
    (hY : 0 ≤ Y) (hYL : Y ≤ YL) :
    hHat c lam Y ≤ flankSmallH c lo hi YL ∧
      flankSmallN c lo hi YL ≤ nTerm c lam Y := by
  have hlam : 0 < lam := lt_of_lt_of_le hlo hl
  have hhi : 0 < hi := lt_of_lt_of_le hlam hh
  obtain ⟨_, hp, _, hk⟩ := primitive_corners hlo hl hh hY hYL
  have hγ := flank_gamma_mono hc hlam hh
  have hγ0 := (hc.gamma_pos hlam).le
  have hkmul := mul_le_mul hγ hk.2 (parentK_pos hlam Y).le (hc.gamma_pos hhi).le
  have hH : hHat c lam Y ≤ flankSmallH c lo hi YL := by
    change 1 - msg lam Y + gamma c lam * parentK lam Y ≤ _
    unfold flankSmallH
    linarith [hp.1]
  have hα := flank_alpha_mono hc hlam hh
  have hdiv1 := div_le_div_of_nonneg_right hα (parentK_pos hlam Y).le
  have hdiv2 := div_le_div_of_nonneg_left (hc.alpha_pos hhi).le
    (parentK_pos hhi 0) hk.1
  have hA := flank_capA_mono hc hlo hl
  refine ⟨hH, ?_⟩
  unfold flankSmallN nTerm
  linarith

/-- Source: `tgt:lem:hand` (ii), the feasible threshold used with the
actual parent denominator `Y`. -/
theorem flank_small_child_threshold {lo lam T Y YL : ℝ}
    (hlo : 0 < lo) (hl : lo ≤ lam) (hT : 0 ≤ T)
    (hTY : lmass lam T ≤ Y) (hYL : Y ≤ YL) :
    flankSmallT lo YL ≤ T := by
  have hlam : 0 < lam := lt_of_lt_of_le hlo hl
  have hY := feasible_parent_pos hlam hTY
  have heY : 0 < exp Y - 1 := by linarith [Real.one_lt_exp_iff.mpr hY]
  have hlogLam := Real.log_le_log hlo hl
  have hlogY := Real.log_le_log heY
    (show exp Y - 1 ≤ exp YL - 1 by linarith [Real.exp_le_exp.mpr hYL])
  have hTlog := feasible_child_log_lower hlam hTY
  unfold flankSmallT
  apply max_le hT
  linarith

/-- Source: `tgt:lem:hand` (ii), its exact small-parent AC lower bound.
The two provisos are the named finite-check hypotheses in the paper. -/
theorem flank_compB_small {c : Band} (hc : BandSide c) {lo lam hi T Y YL Jcap : ℝ}
    (hlo : 0 < lo) (hl : lo ≤ lam) (hh : lam ≤ hi)
    (hT : 0 ≤ T) (hTY : lmass lam T ≤ Y) (hYL : Y ≤ YL)
    (hJcap : coefJ lam T ≤ Jcap)
    (hnumerator : 0 ≤ flankSmallN c lo hi YL + alpha c lo * flankSmallT lo YL)
    (hdenominator : 0 < flankSmallZ c lo hi YL Jcap) :
    flankSmallAC c lo hi YL Jcap ≤ compB c lam T Y / msg lam Y := by
  have hlam : 0 < lam := lt_of_lt_of_le hlo hl
  have hhi : 0 < hi := lt_of_lt_of_le hlam hh
  have hY := feasible_parent_pos hlam hTY
  have hYLpos : 0 < YL := lt_of_lt_of_le hY hYL
  have hJ0 := Tails.coefJ_nonneg hlam hT
  have hαlo := (hc.alpha_pos hlo).le
  have hαlam := (hc.alpha_pos hlam).le
  have hα := flank_alpha_mono hc hlo hl
  obtain ⟨hH, hN⟩ := flank_small_parent_enclosures hc hlo hl hh hY.le hYL
  have hH0 := (flank_hHat_pos hc hlam Y).le
  have hHhi0 : 0 ≤ flankSmallH c lo hi YL := hH0.trans hH
  have he := flank_gamma_parentE_ge hc hlo hl hh (Y := Y)
  have he1 := Real.one_le_exp_iff.mpr hY.le
  have hecorner : 1 / hi ≤ parentE lam Y := by
    have hd := div_le_div_of_nonneg_left (exp_pos Y).le hlam hh
    have hd' := div_le_div_of_nonneg_right he1 hhi.le
    unfold parentE
    exact hd'.trans hd
  have hAE := mul_le_mul hα hecorner (by positivity) hαlam
  have hAE' : alpha c lo / hi ≤ alpha c lam * parentE lam Y := by
    simpa only [mul_one_div] using hAE
  have hLY := mul_le_mul hH hYL hY.le hHhi0
  have hγε : gamma c lo / hi ≤ gamma c lam * parentE lam Y := by
    have hd := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left he1 (hc.gamma_pos hlo).le) hhi.le
    simp only [mul_one] at hd
    exact hd.trans he
  have hL : gamma c lo / hi - flankSmallH c lo hi YL * YL ≤ lBar c lam Y := by
    unfold lBar
    linarith
  have hZ := flank_zBar_lower (flank_gamma_mono hc hlo hl) hL hJ0 hJcap
  change flankSmallZ c lo hi YL Jcap ≤ zBar c lam Y (coefJ lam T) at hZ
  have hz : 0 < zBar c lam Y (coefJ lam T) := lt_of_lt_of_le hdenominator hZ
  have hloss := flank_square_correction_le hJ0 hJcap hH0 hH hdenominator hZ
  have ht := flank_small_child_threshold hlo hl hT hTY hYL
  have hr := childR_ge_div_parent hlam hT hTY
  have htd := div_le_div_of_nonneg_right ht hY.le
  have htr : flankSmallT lo YL / Y ≤ childR lam T := htd.trans hr
  have hr0 : 0 ≤ childR lam T := by
    exact div_nonneg hT (Reserve.Cert.lmass_pos (X := T) hlam).le
  have hrα := mul_le_mul_of_nonneg_left htr hαlo
  have hrα' := mul_le_mul_of_nonneg_right hα hr0
  have hNY := div_le_div_of_nonneg_right hN hY.le
  have hnumY := div_le_div_of_nonneg_left hnumerator hY hYL
  have hlin : (flankSmallN c lo hi YL + alpha c lo * flankSmallT lo YL) / YL ≤
      nTerm c lam Y / Y + alpha c lam * childR lam T := by
    simp only [add_div, mul_div_assoc] at hnumY ⊢
    linarith
  rw [compB_div_msg c hlam T hY hz.ne']
  unfold flankSmallAC vertexA
  linarith

/-- Source: `tgt:lem:hand` (iii), the large-parent enclosure of `N`. -/
theorem flank_large_parent_enclosure {c : Band} (hc : BandSide c)
    {lo lam hi Y : ℝ} (hlo : 0 < lo) (hl : lo ≤ lam) (hh : lam ≤ hi) (hY : 3 ≤ Y) :
    flankLargeN c lo hi ≤ nTerm c lam Y := by
  have hlam : 0 < lam := lt_of_lt_of_le hlo hl
  have hhi : 0 < hi := lt_of_lt_of_le hlam hh
  have hR := (intensity_corners hlo hl hh (Y0 := 3) (Y1 := Y) hY le_rfl).2
  have hk := parentK_le_of_intensity_le hlam hhi hR
  have hα := flank_alpha_mono hc hlam hh
  have hdiv1 := div_le_div_of_nonneg_right hα (parentK_pos hlam Y).le
  have hdiv2 := div_le_div_of_nonneg_left (hc.alpha_pos hhi).le (parentK_pos hhi 3) hk
  have hA := flank_capA_mono hc hlo hl
  have hH := flank_hHat_le hc hlam hh Y
  unfold flankLargeN nTerm
  linarith

/-- Source: `tgt:lem:hand` (iii), its denominator enclosure from the
large-parent exponential envelope. -/
theorem flank_zBar_large {c : Band} (hc : BandSide c) {lo lam hi T Y Jcap : ℝ}
    (hlo : 0 < lo) (hl : lo ≤ lam) (hh : lam ≤ hi) (hY : 3 ≤ Y)
    (hT : 0 ≤ T) (hJcap : coefJ lam T ≤ Jcap)
    (hthreshold : log ((1 + gamma c hi) * hi / gamma c lo) ≤ 3) :
    flankLargeZ c lo hi Jcap ≤ zBar c lam Y (coefJ lam T) := by
  have hlam : 0 < lam := lt_of_lt_of_le hlo hl
  have hZ := flank_zBar_lower (flank_gamma_mono hc hlo hl)
    (flank_lBar_large_lower hc hlo hl hh hY hthreshold)
    (Tails.coefJ_nonneg hlam hT) hJcap
  have hid : min 0 (flankLargeL c lo hi) =
      -max 0 (3 * (1 + gamma c hi) - gamma c lo * exp 3 / hi) := by
    unfold flankLargeL
    by_cases h : 0 ≤ gamma c lo * exp 3 / hi - 3 * (1 + gamma c hi)
    · rw [min_eq_left h, max_eq_left (by linarith)]
      simp
    · rw [min_eq_right (by linarith), max_eq_right (by linarith)]
      ring
  rw [hid] at hZ
  have hmin := min_le_right (gamma c lo)
    (gamma c lo - Jcap * max 0 (3 * (1 + gamma c hi) - gamma c lo * exp 3 / hi))
  unfold flankLargeZ
  nlinarith

/-- Source: `tgt:lem:hand` (iii), its exact large-parent AC lower bound,
with the three named provisos from the finite checker. -/
theorem flank_compB_large {c : Band} (hc : BandSide c) {lo lam hi T Y Jcap : ℝ}
    (hlo : 0 < lo) (hl : lo ≤ lam) (hh : lam ≤ hi) (hY : 3 ≤ Y)
    (hT : 0 ≤ T) (hJcap : coefJ lam T ≤ Jcap)
    (hNneg : flankLargeN c lo hi < 0)
    (hdenominator : 0 < flankLargeZ c lo hi Jcap)
    (hthreshold : log ((1 + gamma c hi) * hi / gamma c lo) ≤ 3) :
    flankLargeAC c lo hi Jcap ≤ compB c lam T Y / msg lam Y := by
  have hlam : 0 < lam := lt_of_lt_of_le hlo hl
  have hhi : 0 < hi := lt_of_lt_of_le hlam hh
  have hYpos : 0 < Y := by linarith
  have hJ0 := Tails.coefJ_nonneg hlam hT
  have hα := flank_alpha_mono hc hlo hl
  have he := (primitive_corners hlo hl hh hY le_rfl).1.1
  have hAE := mul_le_mul hα he (by unfold parentE; positivity) (hc.alpha_pos hlam).le
  have hAE' : alpha c lo * exp 3 / hi ≤ alpha c lam * parentE lam Y := by
    simpa only [parentE, mul_div_assoc] using hAE
  have hN := flank_large_parent_enclosure hc hlo hl hh hY
  have hNY := div_le_div_of_nonneg_right hN hYpos.le
  have hN3 : flankLargeN c lo hi / 3 ≤ flankLargeN c lo hi / Y := by
    rw [div_le_div_iff₀ (by norm_num) hYpos]
    have hprod := mul_nonpos_of_nonpos_of_nonneg hNneg.le (sub_nonneg.mpr hY)
    nlinarith
  have hr0 : 0 ≤ childR lam T := by
    exact div_nonneg hT (Reserve.Cert.lmass_pos (X := T) hlam).le
  have hαr := mul_nonneg (hc.alpha_pos hlam).le hr0
  have hZ := flank_zBar_large hc hlo hl hh hY hT hJcap hthreshold
  have hz : 0 < zBar c lam Y (coefJ lam T) := lt_of_lt_of_le hdenominator hZ
  have hloss := flank_square_correction_le hJ0 hJcap
    (flank_hHat_pos hc hlam Y).le (flank_hHat_le hc hlam hh Y) hdenominator hZ
  rw [compB_div_msg c hlam T hYpos hz.ne']
  unfold flankLargeAC vertexA
  rw [mul_comm ((1 + gamma c hi) ^ 2) Jcap]
  linarith

/-- Source: `tgt:lem:hand` (i); the named global finite check certifies the
actual child denominator on each source segment. -/
theorem segment_flank_zBar_pos (s : Segment) {lo lam hi T Y Jcap : ℝ}
    (hlo : 0 < lo) (hl : lo ≤ lam) (hh : lam ≤ hi) (hY : 0 ≤ Y)
    (hT : 0 ≤ T) (hJcap : coefJ lam T ≤ Jcap)
    (hcheck : 0 < flankGlobalZ s.band lo hi Jcap) :
    0 < zBar s.band lam Y (coefJ lam T) :=
  lt_of_lt_of_le hcheck (segment_flank_zBar_global s hlo hl hh hY hT hJcap)

/-- Source: `tgt:lem:hand` (ii); the named numeric hypotheses imply strict
positivity of AC at the actual feasible pair on the small-parent flank. -/
theorem flank_compB_small_pos {c : Band} (hc : BandSide c) {lo lam hi T Y YL Jcap : ℝ}
    (hlo : 0 < lo) (hl : lo ≤ lam) (hh : lam ≤ hi)
    (hT : 0 ≤ T) (hTY : lmass lam T ≤ Y) (hYL : Y ≤ YL)
    (hJcap : coefJ lam T ≤ Jcap) (hchecks : FlankChecks c lo hi YL Jcap) :
    0 < compB c lam T Y := by
  have hpos := lt_of_lt_of_le hchecks.smallAC_pos
    (flank_compB_small hc hlo hl hh hT hTY hYL hJcap
      hchecks.small_numerator_nonneg hchecks.small_denominator_pos)
  exact (div_pos_iff_of_pos_right (Entropy.msg_pos (lt_of_lt_of_le hlo hl) Y)).mp hpos

/-- Source: `tgt:lem:hand` (iii); the named numeric hypotheses imply strict
positivity of AC at the actual pair on the large-parent flank. -/
theorem flank_compB_large_pos {c : Band} (hc : BandSide c) {lo lam hi T Y YL Jcap : ℝ}
    (hlo : 0 < lo) (hl : lo ≤ lam) (hh : lam ≤ hi) (hY : 3 ≤ Y)
    (hT : 0 ≤ T) (hJcap : coefJ lam T ≤ Jcap)
    (hchecks : FlankChecks c lo hi YL Jcap) : 0 < compB c lam T Y := by
  have hpos := lt_of_lt_of_le hchecks.largeAC_pos
    (flank_compB_large hc hlo hl hh hY hT hJcap hchecks.largeN_neg
      hchecks.large_denominator_pos hchecks.large_threshold)
  exact (div_pos_iff_of_pos_right (Entropy.msg_pos (lt_of_lt_of_le hlo hl) Y)).mp hpos

/-- Source: `tgt:lem:hand` (iv), its nonnegative-`L` CA implication;
the entropy and all actual reserve coordinates are retained. -/
theorem flank_compC_nonneg_of_lBar {c : Band} (hc : BandSide c) {lam T Y : ℝ}
    (hlam : 0 < lam) (hT : 0 ≤ T) (hTY : lmass lam T ≤ Y)
    (hL : 0 ≤ lBar c lam Y) (hZ : 0 < zBar c lam Y (coefJ lam T)) :
    0 ≤ compC c lam T Y := by
  have hE := (Reserve.entropyOK lam T Y hlam hT hTY).1
  have hp := Entropy.msg_pos hlam Y
  have hα := hc.alpha_pos hlam
  have hγ := hc.gamma_pos hlam
  have hLc : 0 ≤ coefL c lam Y := by
    rw [coefL_eq_msg_lBar c hlam Y]
    exact mul_nonneg hp.le hL
  have hZc : 0 < coefZ c lam T Y := by
    rw [coefZ_eq_msg_zBar c hlam T Y]
    exact mul_pos hp hZ
  unfold compC
  exact add_nonneg (mul_nonneg hα.le hE) (by positivity)

end Erdos993Lean.Analytic.HandVariance

#print axioms Erdos993Lean.Analytic.HandVariance.polygonFloor_mix_le
#print axioms Erdos993Lean.Analytic.HandVariance.segment_flank_zBar_global
#print axioms Erdos993Lean.Analytic.HandVariance.flank_compB_small
#print axioms Erdos993Lean.Analytic.HandVariance.flank_compB_large
