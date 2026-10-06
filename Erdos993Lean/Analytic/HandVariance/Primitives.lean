import Erdos993Lean.Analytic.HandVariance.Normalized

/-!
# Exact primitive corner enclosures

Source: `for_tong/TWIN_v1.8/apx_hand.tex`, Lemma `tgt:lem:tr`
(also labelled `mc:lem:ext`), in
`ProofRuns/2026-09-28_analytic_large_n/LEAN`.
The enclosure functions retain the activity and parent log-mass. These are
analytic enclosures, not finite-check verdicts or step-certificate claims.
-/

namespace Erdos993Lean.Analytic.HandVariance

open Real Reserve

/-- Source: `tgt:lem:tr`; the intensity `λ exp(-Y)` is ordered by the two
opposite corners of any positive-activity rectangle. -/
theorem intensity_corners {la lam lb Y0 Y Y1 : ℝ}
    (hla : 0 < la) (hl : la ≤ lam) (hh : lam ≤ lb)
    (hYl : Y0 ≤ Y) (hYh : Y ≤ Y1) :
    la * exp (-Y1) ≤ lam * exp (-Y) ∧
      lam * exp (-Y) ≤ lb * exp (-Y0) := by
  have hlb : 0 ≤ lb := le_trans hla.le (hl.trans hh)
  constructor
  · calc
      la * exp (-Y1) ≤ la * exp (-Y) :=
        mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) hla.le
      _ ≤ lam * exp (-Y) := mul_le_mul_of_nonneg_right hl (exp_pos _).le
  · calc
      lam * exp (-Y) ≤ lb * exp (-Y) :=
        mul_le_mul_of_nonneg_right hh (exp_pos _).le
      _ ≤ lb * exp (-Y0) :=
        mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) hlb

/-- Source: `tgt:lem:tr`; log-mass increases with the actual intensity. -/
theorem lmass_le_of_intensity_le {la lb Ya Yb : ℝ}
    (hla : 0 < la) (hR : la * exp (-Ya) ≤ lb * exp (-Yb)) :
    lmass la Ya ≤ lmass lb Yb := by
  unfold lmass
  apply Real.log_le_log (Reserve.Cert.one_add_pos hla.le)
  linarith

/-- Source: `tgt:lem:tr`; occupation message increases with the intensity. -/
theorem msg_le_of_intensity_le {la lb Ya Yb : ℝ}
    (hla : 0 < la) (hlb : 0 < lb)
    (hR : la * exp (-Ya) ≤ lb * exp (-Yb)) :
    msg la Ya ≤ msg lb Yb := by
  rw [Reserve.Cert.msg_eq (lam := la) (X := Ya) hla.le,
    Reserve.Cert.msg_eq (lam := lb) (X := Yb) hlb.le]
  have h := one_div_le_one_div_of_le
    (Reserve.Cert.one_add_pos (lam := la) (X := Ya) hla.le)
    (show 1 + la * exp (-Ya) ≤ 1 + lb * exp (-Yb) by linarith)
  linarith

/-- Source: `tgt:lem:tr`; `k = phiF(log-mass)` decreases with intensity,
by the already-proved convexity inequality for `phiF`. -/
theorem parentK_le_of_intensity_le {la lb Ya Yb : ℝ}
    (hla : 0 < la) (hlb : 0 < lb)
    (hR : la * exp (-Ya) ≤ lb * exp (-Yb)) :
    parentK lb Yb ≤ parentK la Ya := by
  unfold parentK
  rw [Reserve.Cert.msg_div_lmass (lam := lb) (X := Yb) hlb.le,
    Reserve.Cert.msg_div_lmass (lam := la) (X := Ya) hla.le]
  exact Reserve.Cert.phiF_anti (Reserve.Cert.lmass_pos hla)
    (lmass_le_of_intensity_le hla hR)

/-- Source: `tgt:lem:tr`; exact corner enclosures for `e_λ`, `p`, `φ₀`
and `k`. No upper activity bound or nonnegative parent bound is needed here. -/
theorem primitive_corners {la lam lb Y0 Y Y1 : ℝ}
    (hla : 0 < la) (hl : la ≤ lam) (hh : lam ≤ lb)
    (hYl : Y0 ≤ Y) (hYh : Y ≤ Y1) :
    (parentE lb Y0 ≤ parentE lam Y ∧ parentE lam Y ≤ parentE la Y1) ∧
    (msg la Y1 ≤ msg lam Y ∧ msg lam Y ≤ msg lb Y0) ∧
    (lmass la Y1 ≤ lmass lam Y ∧ lmass lam Y ≤ lmass lb Y0) ∧
    (parentK lb Y0 ≤ parentK lam Y ∧ parentK lam Y ≤ parentK la Y1) := by
  have hlam : 0 < lam := lt_of_lt_of_le hla hl
  have hlb : 0 < lb := lt_of_lt_of_le hlam hh
  obtain ⟨hRlo, hRhi⟩ := intensity_corners hla hl hh hYl hYh
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [parentE_eq_inv hlb, parentE_eq_inv hlam]
    exact one_div_le_one_div_of_le (mul_pos hlam (exp_pos _)) hRhi
  · rw [parentE_eq_inv hlam, parentE_eq_inv hla]
    exact one_div_le_one_div_of_le (mul_pos hla (exp_pos _)) hRlo
  · exact msg_le_of_intensity_le hla hlam hRlo
  · exact msg_le_of_intensity_le hlam hlb hRhi
  · exact lmass_le_of_intensity_le hla hRlo
  · exact lmass_le_of_intensity_le hlam hRhi
  · exact parentK_le_of_intensity_le hlam hlb hRhi
  · exact parentK_le_of_intensity_le hla hlam hRlo

/-- Source: the unrestricted alternative in `tgt:lem:tr`; enclose `ϑ`
by interval addition when monotonic corner evaluation is unavailable. -/
theorem parentTheta_interval_corners {la lam lb Y0 Y Y1 : ℝ}
    (hla : 0 < la) (hl : la ≤ lam) (hh : lam ≤ lb)
    (hYl : Y0 ≤ Y) (hYh : Y ≤ Y1) :
    parentK lb Y0 + msg la Y1 - 1 ≤ parentTheta lam Y ∧
      parentTheta lam Y ≤ parentK la Y1 + msg lb Y0 - 1 := by
  obtain ⟨_, hp, _, hk⟩ := primitive_corners hla hl hh hYl hYh
  unfold parentTheta
  constructor <;> linarith [hp.1, hp.2, hk.1, hk.2]

/-- Source: the exponential comparison in `tgt:lem:tr`.
The explicit exponential-series remainder at degree three proves the same
strict comparison on `(0,1]` as the paper's Taylor remainder. -/
theorem exp_lt_one_add_add_sq {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    exp t < 1 + t + t ^ 2 := by
  have h := Real.exp_bound' ht.le ht1 (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  have ht3 : t ^ 3 ≤ t ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg t) (show 0 ≤ 1 - t by linarith)]
  nlinarith

/-- Source: `tgt:lem:tr`; `ϑ` as a function of the actual mass
`t = φ₀`, with `p = 1-exp(-t)`. -/
noncomputable def thetaFromMass (t : ℝ) : ℝ :=
  Reserve.Cert.phiF t - exp (-t)

/-- Source: `tgt:lem:tr`; exact replacement of `ϑ` by its mass function. -/
theorem parentTheta_eq_thetaFromMass {lam : ℝ} (hlam : 0 < lam) (Y : ℝ) :
    parentTheta lam Y = thetaFromMass (lmass lam Y) := by
  unfold parentTheta parentK thetaFromMass
  rw [Reserve.Cert.msg_div_lmass (lam := lam) (X := Y) hlam.le]
  have h := Reserve.Cert.one_sub_exp_neg_lmass (lam := lam) (X := Y) hlam.le
  linarith

/-- Source: `tgt:lem:tr`; the derivative of the mass-coordinate form of `ϑ`. -/
theorem hasDerivAt_thetaFromMass {t : ℝ} (ht : 0 < t) :
    HasDerivAt thetaFromMass
      ((exp (-t) * (t ^ 2 + t + 1) - 1) / t ^ 2) t := by
  have he : HasDerivAt (fun x : ℝ => exp (-x)) (-exp (-t)) t := by
    convert (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t) using 1
    ring
  have h := (((hasDerivAt_const t (1 : ℝ)).sub he).div
    (hasDerivAt_id t) ht.ne').sub he
  unfold thetaFromMass Reserve.Cert.phiF
  convert h using 1
  dsimp
  field_simp [ht.ne']
  ring

/-- Source: `tgt:lem:tr`; positivity of the `ϑ` mass derivative on `(0,1]`. -/
theorem thetaFromMass_derivative_pos {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    0 < (exp (-t) * (t ^ 2 + t + 1) - 1) / t ^ 2 := by
  apply div_pos _ (sq_pos_of_pos ht)
  have h := mul_lt_mul_of_pos_left (exp_lt_one_add_add_sq ht ht1) (exp_pos (-t))
  have he : exp (-t) * exp t = 1 := by rw [← exp_add]; simp
  rw [he] at h
  nlinarith

/-- Source: `tgt:lem:tr`; `ϑ` increases with its mass on `(0,1]`,
and consequently decreases with `x = Y-log λ` there. -/
theorem thetaFromMass_monotoneOn : MonotoneOn thetaFromMass (Set.Ioc 0 1) := by
  have hs : StrictMonoOn thetaFromMass (Set.Ioc 0 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioc (0 : ℝ) 1)
    · intro t ht
      exact (hasDerivAt_thetaFromMass ht.1).continuousAt.continuousWithinAt
    · intro t ht
      have hti : t ∈ Set.Ioc (0 : ℝ) 1 := interior_subset ht
      rw [(hasDerivAt_thetaFromMass hti.1).deriv]
      exact thetaFromMass_derivative_pos hti.1 hti.2
  exact hs.monotoneOn

/-- Source: the restricted activity premise of `tgt:lem:tr`.
For nonnegative parent mass and `λ≤263/200`, `φ₀≤1`. The elementary
lower exponential sum `8/3≤exp 1` suffices for this exact comparison. -/
theorem lmass_le_one_of_activity_le {lam Y : ℝ} (hlam : 0 < lam)
    (hY : 0 ≤ Y) (hlamHi : lam ≤ 263 / 200) : lmass lam Y ≤ 1 := by
  have heY : exp (-Y) ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have hR : lam * exp (-Y) ≤ lam := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left heY hlam.le
  have he := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at he
  unfold lmass
  rw [Real.log_le_iff_le_exp (Reserve.Cert.one_add_pos hlam.le)]
  linarith

/-- Source: the restricted monotonic corner enclosure in `tgt:lem:tr`.
Unlike the interval-addition enclosure, this uses `Y0≥0` and `lb≤263/200`. -/
theorem parentTheta_corners {la lam lb Y0 Y Y1 : ℝ}
    (hla : 0 < la) (hl : la ≤ lam) (hh : lam ≤ lb)
    (hY0 : 0 ≤ Y0) (hYl : Y0 ≤ Y) (hYh : Y ≤ Y1)
    (hlbHi : lb ≤ 263 / 200) :
    parentTheta la Y1 ≤ parentTheta lam Y ∧
      parentTheta lam Y ≤ parentTheta lb Y0 := by
  have hlam : 0 < lam := lt_of_lt_of_le hla hl
  have hlb : 0 < lb := lt_of_lt_of_le hlam hh
  obtain ⟨_, _, hphi, _⟩ := primitive_corners hla hl hh hYl hYh
  have hmax : lmass lb Y0 ≤ 1 := lmass_le_one_of_activity_le hlb hY0 hlbHi
  have hmid : lmass lam Y ≤ 1 := hphi.2.trans hmax
  have hmin : lmass la Y1 ≤ 1 := hphi.1.trans hmid
  rw [parentTheta_eq_thetaFromMass hla, parentTheta_eq_thetaFromMass hlam,
    parentTheta_eq_thetaFromMass hlb]
  exact ⟨thetaFromMass_monotoneOn ⟨Reserve.Cert.lmass_pos hla, hmin⟩
      ⟨Reserve.Cert.lmass_pos hlam, hmid⟩ hphi.1,
    thetaFromMass_monotoneOn ⟨Reserve.Cert.lmass_pos hlam, hmid⟩
      ⟨Reserve.Cert.lmass_pos hlb, hmax⟩ hphi.2⟩

end Erdos993Lean.Analytic.HandVariance
