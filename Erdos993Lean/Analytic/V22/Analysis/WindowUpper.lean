import Erdos993Lean.Analytic.V22.Analysis.WindowMinorant
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Source: frozen note Lemmas 5.12--5.13. The derivative formula uses the
explicit real-valued bonus expression, not an interpolation of the native
parity amplitude. The final upper recipe evaluates a proved endpoint lower
bound for `phiR`; its sole persistence premise is the source derivative guard.
All integer-fiber consumers retain the actual amplitude and offset. Parent
owns compilation; this drafting subagent runs no Lean or lake. -/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set Filter
open scoped Topology

noncomputable def windowUpperRadius (r N : ℝ) : ℝ := Real.sqrt (N + r ^ 2 * (N - 1) ^ 2)

noncomputable def windowPhiExplicit (r m : ℝ) : ℝ :=
  (71 / 20) / m + r ^ 2 / 2 * (m - 4 + 4 / m) -
    (2 * r / m + V22.aHat r) * windowUpperRadius r (m - 1) - m * V22.cr r +
      2 * r ^ 2 / m + 2 * r * V22.aHat r + (V22.aHat r) ^ 2 * m / 2

noncomputable def windowPhiDerivative (r m : ℝ) : ℝ :=
  -(71 / 20) / m ^ 2 + r ^ 2 / 2 * (1 - 4 / m ^ 2) +
    2 * r / m ^ 2 * windowUpperRadius r (m - 1) -
    (2 * r / m + V22.aHat r) *
      ((1 + 2 * r ^ 2 * (m - 2)) / (2 * windowUpperRadius r (m - 1))) -
    V22.cr r - 2 * r ^ 2 / m ^ 2 + (V22.aHat r) ^ 2 / 2

theorem windowUpperRadius_pos {r N : ℝ} (hN : 0 < N) : 0 < windowUpperRadius r N := by
  unfold windowUpperRadius
  apply Real.sqrt_pos.2
  positivity

theorem window_gamma_radius {r N : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hN : 1 < N) :
    V22.gamma r N = (windowUpperRadius r N) ^ 2 / ((1 - r ^ 2) * N) := by
  have hd := shared_one_sub_sq_pos (by linarith : -1 < r) hr1
  have hn : 0 < N := by linarith
  unfold windowUpperRadius
  rw [Real.sq_sqrt (by positivity : 0 ≤ N + r ^ 2 * (N - 1) ^ 2)]
  unfold V22.gamma V22.Delta
  field_simp [hd.ne', hn.ne'] <;> ring

/-- The exact combined epsilon term, retaining the actual bonus radius. -/
theorem window_epsilon_radius {r N : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hN : 1 < N) :
    V22.epsilonPrime r N * Real.sqrt (V22.gamma r N) =
      2 * V22.yTilde r N * windowUpperRadius r N / (N + 1) := by
  have hn : 0 < N := by linarith
  have hv := shared_varianceR_pos hr0 hr1
  have hR := windowUpperRadius_pos (r := r) hn
  have hgamma : 0 < V22.gamma r N := by
    unfold V22.gamma
    have hD := delta_nonneg (by linarith : 1 ≤ N) (by linarith [shared_one_sub_sq_pos (by linarith : -1 < r) hr1] : r ^ 2 < 1)
    linarith
  have hs := shared_sN_sq hr0 hr1 hn
  have hsN : 0 ≤ V22.sN r N := by
    unfold V22.sN
    exact Real.sqrt_nonneg _
  have hsq := Real.sq_sqrt hgamma.le
  have hprod : (2 * V22.sN r N * Real.sqrt (V22.gamma r N)) ^ 2 = (windowUpperRadius r N) ^ 2 := by
    rw [mul_pow, mul_pow, hs, hsq, window_gamma_radius hr0 hr1 hN]
    unfold V22.varianceR
    field_simp [(shared_one_sub_sq_pos (by linarith : -1 < r) hr1).ne', hn.ne'] <;> ring
  have he : 2 * V22.sN r N * Real.sqrt (V22.gamma r N) = windowUpperRadius r N :=
    (sq_eq_sq₀ (by positivity) hR.le).1 hprod
  unfold V22.epsilonPrime
  calc
    (4 * V22.yTilde r N * V22.sN r N / (N + 1)) * Real.sqrt (V22.gamma r N) =
        2 * V22.yTilde r N * (2 * V22.sN r N * Real.sqrt (V22.gamma r N)) / (N + 1) := by ring
    _ = _ := by rw [he]

/-- Lemma 5.12's explicit expression, on its analytic real domain. -/
theorem window_phiR_formula {r N : ℝ} (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hN : 1 < N) :
    V22.phiR r N = windowPhiExplicit r (N + 1) := by
  have hr1 : r < 1 := by linarith
  have hd := shared_one_sub_sq_pos (by linarith : -1 < r) hr1
  have hn : 0 < N := by linarith
  have hD := delta_nonneg (by linarith : 1 ≤ N) (by nlinarith : r ^ 2 < 1)
  have hg : 0 < V22.gamma r N := by unfold V22.gamma; linarith
  have hs := Real.sqrt_pos.2 hg
  have hsq := Real.sq_sqrt hg.le
  have heps := window_epsilon_radius hr0 hr1 hN
  have hN1 : 0 < N + 1 := by linarith
  have hdeltaSq : V22.Delta r N = (Real.sqrt (V22.gamma r N)) ^ 2 - 1 := by
    rw [hsq]
    unfold V22.gamma
    ring
  have hEpsilonCancel :
      (V22.epsilonPrime r N / Real.sqrt (V22.gamma r N)) / 2 * V22.Delta r N +
        V22.epsilonPrime r N / 2 *
          (Real.sqrt (V22.gamma r N) + 1 / Real.sqrt (V22.gamma r N)) =
      V22.epsilonPrime r N * Real.sqrt (V22.gamma r N) := by
    rw [hdeltaSq]
    field_simp [hs.ne'] <;> ring
  have hQuadraticCancel :
      ((1 - r ^ 2) * V22.rho N) / 2 * V22.Delta r N - r ^ 2 * V22.rho N / 2 =
        r ^ 2 * (N - 1) ^ 2 / (2 * (N + 1)) := by
    unfold V22.rho V22.Delta
    field_simp [hd.ne', hn.ne', hN1.ne'] <;> ring
  have hbase : V22.phiR r N = (71 / 20 : ℝ) / (N + 1) +
      r ^ 2 * (N - 1) ^ 2 / (2 * (N + 1)) - V22.epsilonPrime r N * Real.sqrt (V22.gamma r N) -
        (N + 1) * V22.cr r + 2 * (V22.yTilde r N) ^ 2 / (N + 1) := by
    calc
      V22.phiR r N = (71 / 20 : ℝ) / (N + 1) +
          (((1 - r ^ 2) * V22.rho N) / 2 * V22.Delta r N - r ^ 2 * V22.rho N / 2) -
          ((V22.epsilonPrime r N / Real.sqrt (V22.gamma r N)) / 2 * V22.Delta r N +
            V22.epsilonPrime r N / 2 *
              (Real.sqrt (V22.gamma r N) + 1 / Real.sqrt (V22.gamma r N))) -
          (N + 1) * V22.cr r + 2 * (V22.yTilde r N) ^ 2 / (N + 1) := by
        unfold V22.phiR V22.rhoU V22.eU V22.c0Prime
        ring
      _ = _ := by rw [hQuadraticCancel, hEpsilonCancel]
  rw [hbase, heps]
  unfold windowPhiExplicit V22.yTilde
  norm_num only [add_sub_cancel_right]
  field_simp [ne_of_gt (by linarith : 0 < N + 1)] <;> ring

/-- The native amplitude keeps the `3.55/(N+1)` shift; no template assumption. -/
theorem window_lambdaU_lower {M : ℕ} (hN : 10 ≤ M + 2) {r mu : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hmu : 0 < mu) :
    activityOneLambda_t ((M : ℝ) / mu) + V22.phiR r ((M : ℝ) + 2) ≤ threeRangeLambdaU r mu M := by
  have hs := activityOneLambda_shift (M := M) (by omega : 1 ≤ M) hmu .U
  have hk := (activityOneK_bounds (by omega : 8 ≤ M) .U).1
  have hb := div_le_div_of_nonneg_right hk (show 0 ≤ (M : ℝ) + 3 by positivity)
  rw [threeRanges_lambdaU_eq hN hr0 hrh hmu]
  unfold V22.phiR
  simp only [activityOneLambda, activityOnePrefactor] at hs
  rw [hs]
  norm_num only [add_assoc]
  linarith

theorem hasDerivAt_windowUpperRadius {r m : ℝ} (hm : 2 < m) :
    HasDerivAt (fun x : ℝ => windowUpperRadius r (x - 1))
      ((1 + 2 * r ^ 2 * (m - 2)) / (2 * windowUpperRadius r (m - 1))) m := by
  have hm1 : 0 < m - 1 := by linarith
  have hrad : 0 < m - 1 + r ^ 2 * (m - 2) ^ 2 := by positivity
  have hquad := ((hasDerivAt_id m).sub_const 2).pow 2
  have hquadR := hquad.const_mul (r ^ 2)
  have hsum := ((hasDerivAt_id m).sub_const 1).add hquadR
  have hsqrt := hsum.sqrt hrad.ne'
  refine (hsqrt.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun x => by
      simp only [windowUpperRadius, id_eq, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]
      congr 1
      ring)
  · norm_num only [windowUpperRadius, id_eq, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, sub_sub]
    ring

theorem hasDerivAt_windowPhiExplicit {r m : ℝ} (hm : 2 < m) :
    HasDerivAt (windowPhiExplicit r) (windowPhiDerivative r m) m := by
  have hmne : m ≠ 0 := ne_of_gt (by linarith : 0 < m)
  have ha := (hasDerivAt_const m (71 / 20 : ℝ)).div (hasDerivAt_id m) hmne
  have hb := (((hasDerivAt_id m).sub_const 4).add
    ((hasDerivAt_const m (4 : ℝ)).div (hasDerivAt_id m) hmne)).const_mul (r ^ 2 / 2)
  have hc := (((hasDerivAt_const m (2 * r)).div (hasDerivAt_id m) hmne).add_const (V22.aHat r)).mul
    (hasDerivAt_windowUpperRadius (r := r) hm)
  have hd := (hasDerivAt_id m).const_mul (V22.cr r)
  have he := (hasDerivAt_const m (2 * r ^ 2)).div (hasDerivAt_id m) hmne
  have hf := hasDerivAt_const m (2 * r * V22.aHat r)
  have hg := (hasDerivAt_id m).const_mul ((V22.aHat r) ^ 2 / 2)
  have hfull := (((((ha.add hb).sub hc).sub hd).add he).add hf).add hg
  refine (hfull.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun x => by
      simp only [windowPhiExplicit, id_eq, Pi.add_apply, Pi.sub_apply,
        Pi.mul_apply, Pi.div_apply]
      ring)
  · simp only [windowPhiDerivative, id_eq, Pi.add_apply, Pi.sub_apply,
      Pi.mul_apply, Pi.div_apply]
    ring

theorem window_radius_derivative_upper {r m : ℝ} (hr : 0 < r) (hm : 2 < m) :
    (1 + 2 * r ^ 2 * (m - 2)) / (2 * windowUpperRadius r (m - 1)) ≤
      r + 1 / (2 * r * (m - 2)) := by
  have hm1 : 0 < m - 1 := by linarith
  have hm2 : 0 < m - 2 := by linarith
  have hR := windowUpperRadius_pos (r := r) hm1
  have hsq : windowUpperRadius r (m - 1) ^ 2 = m - 1 + r ^ 2 * (m - 2) ^ 2 := by
    unfold windowUpperRadius
    norm_num only [sub_sub]
    exact Real.sq_sqrt (by positivity)
  have hRlo : r * (m - 2) ≤ windowUpperRadius r (m - 1) := by
    have hnonneg : 0 ≤ r * (m - 2) := by positivity
    nlinarith
  have h := div_le_div_of_nonneg_left (show 0 ≤ 1 + 2 * r ^ 2 * (m - 2) by positivity)
    (show 0 < 2 * r * (m - 2) by positivity) (show 2 * r * (m - 2) ≤ 2 * windowUpperRadius r (m - 1) by linarith)
  convert h using 1 <;> field_simp [hr.ne', ne_of_gt (by linarith : 0 < m - 2)] <;> ring

/-- Lemma 5.12's derivative lower bound, for every source `m>2`. -/
theorem window_phi_derivative_lower {r m : ℝ} (hr : 0 < r) (hrh : r ≤ 1 / 2) (hm : 2 < m) :
    V22.uMonoDerivative r (m - 1) ≤ windowPhiDerivative r m := by
  have ha := (sharedAHat_bounds hr.le (by linarith : r < 1)).1
  have hcoef : 0 ≤ 2 * r / m + V22.aHat r := by positivity
  have hcap := mul_nonneg hcoef (sub_nonneg.mpr (window_radius_derivative_upper hr hm))
  have hdrop : 0 ≤ 2 * r / m ^ 2 * windowUpperRadius r (m - 1) + (V22.aHat r) ^ 2 / 2 := by
    have hR := windowUpperRadius_pos (r := r) (by linarith : 0 < m - 1)
    positivity
  have hid : windowPhiDerivative r m - V22.uMonoDerivative r (m - 1) =
      2 * r / m ^ 2 * windowUpperRadius r (m - 1) + (V22.aHat r) ^ 2 / 2 +
      (2 * r / m + V22.aHat r) * (r + 1 / (2 * r * (m - 2)) -
        (1 + 2 * r ^ 2 * (m - 2)) / (2 * windowUpperRadius r (m - 1))) := by
    unfold windowPhiDerivative V22.uMonoDerivative
    norm_num only [sub_add_cancel]
    field_simp [hr.ne', ne_of_gt (by linarith : 0 < m), ne_of_gt (by linarith : 0 < m - 2)] <;> ring
  linarith

theorem hasDerivAt_windowPhiR {r N : ℝ} (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hN : 1 < N) :
    HasDerivAt (V22.phiR r) (windowPhiDerivative r (N + 1)) N := by
  have h := (hasDerivAt_windowPhiExplicit (r := r) (by linarith : 2 < N + 1)).comp N
    ((hasDerivAt_id N).add_const 1)
  have heq : V22.phiR r =ᶠ[𝓝 N] (fun x : ℝ => windowPhiExplicit r (x + 1)) := by
    filter_upwards [eventually_gt_nhds hN] with x hx
    exact window_phiR_formula hr0 hrh hx
  simpa only [mul_one] using h.congr_of_eventuallyEq heq

theorem window_phiR_deriv_lower {r N : ℝ} (hr : 0 < r) (hrh : r ≤ 1 / 2) (hN : 1 < N) :
    V22.uMonoDerivative r N ≤ deriv (V22.phiR r) N := by
  rw [(hasDerivAt_windowPhiR hr.le hrh hN).deriv]
  simpa only [add_sub_cancel_right] using window_phi_derivative_lower hr hrh (by linarith : 2 < N + 1)

/-- Every subtracted term of the source derivative guard decreases in `N`. -/
theorem window_derivative_guard_monotone {r Na N : ℝ} (hr : 0 < r) (hrh : r ≤ 1 / 2)
    (ha : 1 < Na) (haN : Na ≤ N) : V22.uMonoDerivative r Na ≤ V22.uMonoDerivative r N := by
  have hn : 1 < N := ha.trans_le haN
  have ha1 : 0 < Na - 1 := by linarith
  have haPlus : 0 < Na + 1 := by linarith
  have hn2 : N + 1 - 2 = N - 1 := by ring
  have ha2 : Na + 1 - 2 = Na - 1 := by ring
  have hhat := (sharedAHat_bounds hr.le (by linarith : r < 1)).1
  have ht1 := div_le_div_of_nonneg_left (show 0 ≤ 2 * r ^ 2 by positivity)
    (show 0 < Na + 1 by linarith) (show Na + 1 ≤ N + 1 by linarith)
  have hs : (Na + 1) ^ 2 ≤ (N + 1) ^ 2 := by nlinarith
  have ht2 := div_le_div_of_nonneg_left (show 0 ≤ 4 * r ^ 2 by positivity) (by positivity : 0 < (Na + 1) ^ 2) hs
  have ht3 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
    (show 0 < (Na + 1) * (Na - 1) by positivity)
    (show (Na + 1) * (Na - 1) ≤ (N + 1) * (N - 1) by nlinarith)
  have ht4 := div_le_div_of_nonneg_left hhat (show 0 < 2 * r * (Na - 1) by positivity)
    (show 2 * r * (Na - 1) ≤ 2 * r * (N - 1) by nlinarith)
  have ht5 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 71 / 20)
    (by positivity : 0 < (Na + 1) ^ 2) hs
  unfold V22.uMonoDerivative
  dsimp only
  rw [hn2, ha2]
  linarith only [ht1, ht2, ht3, ht4, ht5]

/-- Lemma 5.12's persistence theorem under exactly its starting derivative guard. -/
theorem window_phiR_strictMonoOn {r N1 : ℝ} (hr : 0 < r) (hrh : r ≤ 1 / 2)
    (hN1 : 10 ≤ N1) (hguard : 0 < V22.uMonoDerivative r N1) : StrictMonoOn (V22.phiR r) (Ici N1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro N hN
    have hNge : N1 ≤ N := hN
    exact (hasDerivAt_windowPhiR hr.le hrh (by linarith : 1 < N)).continuousAt.continuousWithinAt
  · intro N hN
    have hNIci : N ∈ Ici N1 := interior_subset hN
    have hNge : N1 ≤ N := hNIci
    have hg := window_derivative_guard_monotone hr hrh (by linarith : 1 < N1) hNge
    exact (hguard.trans_le hg).trans_le (window_phiR_deriv_lower hr hrh (by linarith : 1 < N))

theorem window_aHat_monotone {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) : V22.aHat a ≤ V22.aHat b := by
  have hd : ∀ x ∈ Icc a b, HasDerivAt V22.aHat (x ^ 2 / (1 - x ^ 2)) x := by
    intro x hx
    have hx0 : 0 ≤ x := ha.trans hx.1
    have hx1 : x < 1 := hx.2.trans_lt hb
    have hraw : HasDerivAt V22.aHat (1 / (1 - x ^ 2) - 1) x := by
      simpa only [V22.aHat, id_eq, Pi.sub_apply] using
        (hasDerivAt_sharedArtanh (by linarith : -1 < x) hx1).sub (hasDerivAt_id x)
    apply hraw.congr_deriv
    field_simp [(shared_one_sub_sq_pos (by linarith : -1 < x) hx1).ne'] <;> ring
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => by
      have hx' : x ∈ Icc a b := interior_subset hx
      exact div_nonneg (sq_nonneg _)
        (shared_one_sub_sq_pos (by linarith [ha.trans hx'.1]) (hx'.2.trans_lt hb)).le)
  exact hm ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

theorem window_cr_monotone {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) : V22.cr a ≤ V22.cr b := by
  have hd : ∀ x ∈ Icc a b, HasDerivAt V22.cr (V22.aHat x / (1 - x ^ 2)) x := by
    intro x hx
    exact hasDerivAt_sharedCr (by linarith [ha.trans hx.1]) (hx.2.trans_lt hb)
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => by
      have hx' : x ∈ Icc a b := interior_subset hx
      exact div_nonneg (sharedAHat_bounds (ha.trans hx'.1) (hx'.2.trans_lt hb)).1
        (shared_one_sub_sq_pos (by linarith [ha.trans hx'.1]) (hx'.2.trans_lt hb)).le)
  exact hm ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

theorem window_delta_r_monotone {a b N : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 2) (hN : 1 ≤ N) :
    V22.Delta a N ≤ V22.Delta b N := by
  have hn : 0 < N := by linarith
  have hda := shared_one_sub_sq_pos (by linarith : -1 < a) (by linarith : a < 1)
  have hdb := shared_one_sub_sq_pos (by linarith : -1 < b) (by linarith : b < 1)
  have hs : a ^ 2 ≤ b ^ 2 := by nlinarith
  have hp : 0 ≤ N ^ 2 - N + 1 := by nlinarith [sq_nonneg (N - 1)]
  unfold V22.Delta
  apply (div_le_div_iff₀ (mul_pos hda hn) (mul_pos hdb hn)).2
  have h := mul_nonneg (sub_nonneg.mpr hs) (mul_nonneg hp hn.le)
  nlinarith

theorem window_delta_N_monotone {r Na N : ℝ} (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (ha : 1 ≤ Na) (haN : Na ≤ N) :
    V22.Delta r Na ≤ V22.Delta r N := by
  have hd := shared_one_sub_sq_pos (by linarith : -1 < r) (by linarith : r < 1)
  have han : 0 < Na := by linarith
  have hn : 0 < N := by linarith
  unfold V22.Delta
  apply (div_le_div_iff₀ (mul_pos hd han) (mul_pos hd hn)).2
  have hpay := mul_nonneg (show 0 ≤ (N - Na) * (N * Na - 1) by
    exact mul_nonneg (sub_nonneg.mpr haN) (by nlinarith)) (mul_nonneg (sq_nonneg r) hd.le)
  nlinarith

/-- The actual same-N endpoint lower bound, with the negative c0Prime dropped
only by its proved sign. This is the source interval Phi used by Lemma 5.13. -/
theorem window_phiR_block_lower {ra r rb N : ℝ} (hN : 10 ≤ N)
    (hra : 0 ≤ ra) (har : ra ≤ r) (hrrb : r ≤ rb) (hrb : rb ≤ 1 / 2) :
    V22.phiRBlockLower ra rb N N ≤ V22.phiR r N := by
  have hr0 := hra.trans har
  have hrb0 := hr0.trans hrrb
  have hn : 0 < N := by linarith
  have hn1 : 0 < N + 1 := by linarith
  have hrho : 0 < V22.rho N := by unfold V22.rho; positivity
  have hstar : 0 < V22.rhoStar N rb := by linarith [linearized_rhoStar_lower hN hrb0 hrb]
  have hU := linearized_rhoU_lower hN hr0 hrrb hrb
  have hD := window_delta_r_monotone hra har (by linarith : r ≤ 1 / 2) (by linarith : 1 ≤ N)
  have hDa := delta_nonneg (by linarith : 1 ≤ N) (by nlinarith : ra ^ 2 < 1)
  have hterm := mul_le_mul hU hD hDa (hstar.le.trans hU)
  have hr2 : r ^ 2 ≤ rb ^ 2 := by nlinarith
  have hfirst := mul_le_mul_of_nonneg_right hr2 hrho.le
  have hhat := window_aHat_monotone hr0 hrrb (by linarith : rb < 1)
  have hy : V22.yTilde r N ≤ V22.yTilde rb N := by
    have h := mul_le_mul_of_nonneg_right hhat hn1.le
    unfold V22.yTilde
    linarith
  have hy0 := shared_yTilde_nonneg hr0 (by linarith : r < 1) hn
  have hyb0 := shared_yTilde_nonneg hrb0 (by linarith : rb < 1) hn
  have hR : windowUpperRadius r N ≤ windowUpperRadius rb N := by
    unfold windowUpperRadius
    exact Real.sqrt_le_sqrt (by nlinarith [mul_nonneg (sub_nonneg.mpr hr2) (sq_nonneg (N - 1))])
  have hprod := mul_le_mul hy hR (windowUpperRadius_pos (r := r) hn).le hyb0
  have heps := linearized_epsilon_over_gamma_bound hN hr0 hrrb hrb
  have hepsR := window_epsilon_radius hr0 (by linarith : r < 1) (by linarith : 1 < N)
  have hsC : 0 < Real.sqrt (V22.cCoef N) :=
    Real.sqrt_pos.2 (by linarith [linearized_cCoef_lower hN])
  have hrbDen : 0 < 1 - rb ^ 2 :=
    shared_one_sub_sq_pos (by linarith : -1 < rb) (by linarith : rb < 1)
  have hepsHalf : V22.epsilonPrime r N / Real.sqrt (V22.gamma r N) / 2 ≤
      1 / ((N + 1) * Real.sqrt (V22.cCoef N)) +
        rb ^ 2 / (6 * (1 - rb ^ 2) * Real.sqrt (V22.cCoef N)) := by
    calc
      V22.epsilonPrime r N / Real.sqrt (V22.gamma r N) / 2 ≤
          (2 / ((N + 1) * Real.sqrt (V22.cCoef N)) +
            rb ^ 2 / (3 * (1 - rb ^ 2) * Real.sqrt (V22.cCoef N))) / 2 :=
        div_le_div_of_nonneg_right heps (by norm_num : (0 : ℝ) ≤ 2)
      _ = _ := by field_simp [hn1.ne', hsC.ne', hrbDen.ne'] <;> ring
  have hfirstHalf : r ^ 2 * V22.rho N / 2 ≤ rb ^ 2 * V22.rho N / 2 :=
    div_le_div_of_nonneg_right hfirst (by norm_num : (0 : ℝ) ≤ 2)
  have hcr := mul_le_mul_of_nonneg_left (window_cr_monotone hr0 hrrb (by linarith : rb < 1)) hn1.le
  have hc0 : 0 ≤ V22.c0Prime r N := by unfold V22.c0Prime; positivity
  have hE : V22.eU r N ≤ rb ^ 2 * V22.rho N / 2 + V22.yTilde rb N * windowUpperRadius rb N / (N + 1) +
      (1 / ((N + 1) * Real.sqrt (V22.cCoef N)) + rb ^ 2 / (6 * (1 - rb ^ 2) * Real.sqrt (V22.cCoef N))) +
        (N + 1) * V22.cr rb := by
    unfold V22.eU
    have hdiv := div_le_div_of_nonneg_right hprod hn1.le
    have hsplit : V22.epsilonPrime r N / 2 * (Real.sqrt (V22.gamma r N) + 1 / Real.sqrt (V22.gamma r N)) =
        V22.yTilde r N * windowUpperRadius r N / (N + 1) + V22.epsilonPrime r N / Real.sqrt (V22.gamma r N) / 2 := by
      calc
        V22.epsilonPrime r N / 2 * (Real.sqrt (V22.gamma r N) + 1 / Real.sqrt (V22.gamma r N)) =
            (V22.epsilonPrime r N * Real.sqrt (V22.gamma r N)) / 2 +
              V22.epsilonPrime r N / Real.sqrt (V22.gamma r N) / 2 := by ring
        _ = (2 * V22.yTilde r N * windowUpperRadius r N / (N + 1)) / 2 +
              V22.epsilonPrime r N / Real.sqrt (V22.gamma r N) / 2 := by rw [hepsR]
        _ = V22.yTilde r N * windowUpperRadius r N / (N + 1) +
              V22.epsilonPrime r N / Real.sqrt (V22.gamma r N) / 2 := by ring
    rw [hsplit]
    have hsum := add_le_add (add_le_add hfirstHalf (add_le_add hdiv hepsHalf)) hcr
    linarith only [hsum, hc0]
  unfold V22.phiRBlockLower V22.phiR windowUpperRadius at *
  linarith

/-- Lemma 5.13's complete native upper range, with the exact source derivative
guard on the r interval and the proved endpoint Phi bound. -/
theorem window_upper_exact {M : ℕ} {r ra rb mu N1 N0 : ℝ}
    (hra : 0 < ra) (har : ra ≤ r) (hrrb : r ≤ rb) (hrb : rb ≤ 1 / 2)
    (hN1 : 10 ≤ N1) (h10 : N1 ≤ N0) (hN0 : N0 ≤ (M : ℝ) + 2) (hmu : 0 < mu)
    (hguard : ∀ a ∈ Icc ra rb, 0 < V22.uMonoDerivative a N1)
    (w : ℝ) (hw : V22.gamma r ((M : ℝ) + 2) ≤ w) :
    (((M : ℝ) + 2) / mu) * (1 + V22.Delta ra N0 - 2 / V22.rhoStar N0 rb *
      rootG (min 0 (activityOneLambda_t ((M : ℝ) / mu) + V22.phiRBlockLower ra rb N0 N0))) ≤
      rootMinorant (threeRangePU r mu M) (((M : ℝ) + 2) / mu) (V22.rhoU r ((M : ℝ) + 2))
        (V22.gamma r ((M : ℝ) + 2)) w := by
  have hr : 0 < r := hra.trans_le har
  have hr0 := hr.le
  have hrh : r ≤ 1 / 2 := hrrb.trans hrb
  have hrb0 : 0 ≤ rb := hr0.trans hrrb
  have hNa : 10 ≤ N0 := hN1.trans h10
  have hNr : (10 : ℝ) ≤ (M : ℝ) + 2 := hNa.trans hN0
  have hN : 10 ≤ M + 2 := by exact_mod_cast hNr
  have hb : 0 < ((M : ℝ) + 2) / mu := by positivity
  have hphi := (window_phiR_strictMonoOn hr hrh hN1 (hguard r ⟨har, hrrb⟩)).monotoneOn
    h10 (h10.trans hN0) hN0
  have hphib := window_phiR_block_lower hNa hra.le har hrrb hrb
  have hlam := window_lambdaU_lower hN hr0 hrh hmu
  have hlow : min 0 (activityOneLambda_t ((M : ℝ) / mu) + V22.phiRBlockLower ra rb N0 N0) ≤
      threeRangeLambdaU r mu M := by linarith [min_le_right (0 : ℝ) (activityOneLambda_t ((M : ℝ) / mu) + V22.phiRBlockLower ra rb N0 N0)]
  have hD1 := window_delta_r_monotone hra.le har hrh (by linarith : 1 ≤ N0)
  have hD2 := window_delta_N_monotone hr0 hrh (by linarith : 1 ≤ N0) hN0
  have hD : V22.Delta ra N0 ≤ V22.Delta r ((M : ℝ) + 2) := hD1.trans hD2
  have hstar : 0 < V22.rhoStar N0 rb := by linarith [linearized_rhoStar_lower hNa hrb0 hrb]
  have hstarN := coefficient_rhoStar_monotone hNa hN0 hrb0 hrb
  have hU := linearized_rhoU_lower hNr hr0 hrrb hrb
  have hUstar : V22.rhoStar N0 rb ≤ V22.rhoU r ((M : ℝ) + 2) := hstarN.trans hU
  have hu := hstar.trans_le hUstar
  by_cases hl : 0 ≤ threeRangeLambdaU r mu M
  · have hmin := bonusRange_upper_nonneg (threeRangePU_pos hmu r M) hb hu
      (threeRange_gamma_ge_one hr0 (by linarith : r < 1) M) hl w hw
    have hG := rootG_nonneg (min 0 (activityOneLambda_t ((M : ℝ) / mu) + V22.phiRBlockLower ra rb N0 N0))
    have hcoef : 0 ≤ 2 / V22.rhoStar N0 rb * rootG (min 0 (activityOneLambda_t ((M : ℝ) / mu) + V22.phiRBlockLower ra rb N0 N0)) := by positivity
    have h := mul_le_mul_of_nonneg_left (show 1 + V22.Delta ra N0 - 2 / V22.rhoStar N0 rb *
        rootG (min 0 (activityOneLambda_t ((M : ℝ) / mu) + V22.phiRBlockLower ra rb N0 N0)) ≤
      V22.gamma r ((M : ℝ) + 2) by unfold V22.gamma; linarith) hb.le
    exact h.trans hmin
  · have hlneg : threeRangeLambdaU r mu M < 0 := by linarith
    have hminNonpos : min 0 (activityOneLambda_t ((M : ℝ) / mu) +
        V22.phiRBlockLower ra rb N0 N0) ∈ Iic (0 : ℝ) :=
      min_le_left 0 (activityOneLambda_t ((M : ℝ) / mu) + V22.phiRBlockLower ra rb N0 N0)
    have hactualNonpos : threeRangeLambdaU r mu M ∈ Iic (0 : ℝ) := hlneg.le
    have hG := rootG_antitoneOn_nonpos hminNonpos hactualNonpos hlow
    have hi := one_div_le_one_div_of_le hstar hUstar
    have hprod := mul_le_mul hi hG (rootG_nonneg _) (by positivity : 0 ≤ 1 / V22.rhoStar N0 rb)
    have hscaled : 2 / V22.rhoU r ((M : ℝ) + 2) * rootG (threeRangeLambdaU r mu M) ≤
        2 / V22.rhoStar N0 rb * rootG (min 0 (activityOneLambda_t ((M : ℝ) / mu) + V22.phiRBlockLower ra rb N0 N0)) := by
      convert mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
    have hcmp : 1 + V22.Delta ra N0 - 2 / V22.rhoStar N0 rb *
        rootG (min 0 (activityOneLambda_t ((M : ℝ) / mu) + V22.phiRBlockLower ra rb N0 N0)) ≤
      V22.gamma r ((M : ℝ) + 2) - 2 / V22.rhoU r ((M : ℝ) + 2) * rootG (threeRangeLambdaU r mu M) := by
      unfold V22.gamma
      linarith only [hD, hscaled]
    exact (mul_le_mul_of_nonneg_left hcmp hb.le).trans
      (rootMinorant_lower_bound (threeRangePU_pos hmu r M) hb hu _ w)

/-- Every actual upper-range atom consumes the exact window recipe. -/
theorem window_upper_fiber {M : ℕ} {r ra rb mu N1 N0 : ℝ}
    (hra : 0 < ra) (har : ra ≤ r) (hrrb : r ≤ rb) (hrb : rb ≤ 1 / 2)
    (hN1 : 10 ≤ N1) (h10 : N1 ≤ N0) (hN0 : N0 ≤ (M : ℝ) + 2) (hmu : 0 < mu)
    (hguard : ∀ a ∈ Icc ra rb, 0 < V22.uMonoDerivative a N1) (j : ℤ)
    (hw : V22.gamma r ((M : ℝ) + 2) ≤ threeRangeW r M j) :
    (((M : ℝ) + 2) / mu) * (1 + V22.Delta ra N0 - 2 / V22.rhoStar N0 rb *
      V22.G (min 0 (V22.lambdaT ((M : ℝ) / mu) + V22.phiRBlockLower ra rb N0 N0))) ≤
        V22.fiberFunction ((1 + r) / 2) mu M j := by
  have hN : 10 ≤ M + 2 := by exact_mod_cast hN1.trans (h10.trans hN0)
  have h := window_upper_exact hra har hrrb hrb hN1 h10 hN0 hmu hguard (threeRangeW r M j) hw
  rw [shared_G_eq, shared_lambdaT_eq]
  exact h.trans (threeRanges_upper hN (hra.trans_le har).le (hrrb.trans hrb) hmu j hw)

end Erdos993Lean.Analytic.V22.Analysis
