import Erdos993Lean.Analytic.V22.Analysis.WindowUpper
import Erdos993Lean.Analytic.V22.Checks.EarlyStatements

/-! Source: note Corollary 5.15, its last paragraph and Lemmas 7.8--7.9.
The varying-size block lower bound for Phi_R uses the actual H derivative
and retains both ends of every r,N block. Parent owns Lean verification. -/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

noncomputable def windowRadiusCost (r N : ℝ) : ℝ := V22.yTilde r N * windowUpperRadius r N / (N + 1)

theorem hasDerivAt_windowH {r N : ℝ} (hN : 3 ≤ N) :
    HasDerivAt (V22.windowH r)
      (2 * V22.aHat r * r ^ 2 + 2 * r * (1 - 4 * r ^ 2) * (N - 3) / (N + 1) ^ 3) N := by
  have hn : N + 1 ≠ 0 := by linarith
  have h := (((((hasDerivAt_id N).sub_const 1).const_mul (2 * r ^ 2)).const_add 1).const_mul (V22.aHat r)).sub
    ((((hasDerivAt_id N).sub_const 1).const_mul (2 * r * (1 - 4 * r ^ 2))).div
      (((hasDerivAt_id N).add_const 1).pow 2) (pow_ne_zero 2 hn))
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun x => by
      simp only [V22.windowH, id_eq, Pi.add_apply, Pi.sub_apply,
        Pi.div_apply, Pi.mul_apply, Pi.pow_apply] <;> ring)
  · norm_num only [id_eq, Pi.add_apply, Pi.sub_apply, Pi.div_apply,
      Pi.mul_apply, Pi.pow_apply]
    field_simp [hn] <;> ring

theorem windowH_monotoneOn {r : ℝ} (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) :
    MonotoneOn (V22.windowH r) (Ici 3) := by
  have hhat := (sharedAHat_bounds hr0 (by linarith : r < 1)).1
  have hc : 0 ≤ 1 - 4 * r ^ 2 := by nlinarith
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 3)
  · intro N hN
    exact (hasDerivAt_windowH hN).continuousAt.continuousWithinAt
  · intro N hN
    have hNIci : N ∈ Ici 3 := interior_subset hN
    exact (hasDerivAt_windowH hNIci).hasDerivWithinAt
  · intro N hN
    have hNIci : N ∈ Ici 3 := interior_subset hN
    have hNge : (3 : ℝ) ≤ N := hNIci
    have hn3 : 0 ≤ N - 3 := by linarith
    positivity

theorem hasDerivAt_windowRadiusCost {r N : ℝ} (hN : 1 < N) :
    HasDerivAt (windowRadiusCost r) (V22.windowH r N / (4 * windowUpperRadius r N)) N := by
  have hR := windowUpperRadius_pos (r := r) (by linarith : 0 < N)
  have hRsq : (windowUpperRadius r N) ^ 2 = N + r ^ 2 * (N - 1) ^ 2 := by
    unfold windowUpperRadius
    exact Real.sq_sqrt (by positivity)
  have hn : N + 1 ≠ 0 := by linarith
  have hrad : 0 < N + r ^ 2 * (N - 1) ^ 2 := by positivity
  have hdR : HasDerivAt (windowUpperRadius r)
      ((1 + 2 * r ^ 2 * (N - 1)) / (2 * windowUpperRadius r N)) N := by
    have hraw := ((hasDerivAt_id N).add
      ((((hasDerivAt_id N).sub_const 1).pow 2).const_mul (r ^ 2))).sqrt hrad.ne'
    refine (hraw.congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall (fun x => by
        simp only [windowUpperRadius, id_eq, Pi.add_apply, Pi.sub_apply, Pi.pow_apply])
    · norm_num only [windowUpperRadius, id_eq, Pi.add_apply, Pi.sub_apply, Pi.pow_apply] <;> ring
  have hdy : HasDerivAt (V22.yTilde r) (V22.aHat r / 2) N := by
    have hraw := ((((hasDerivAt_id N).add_const 1).const_mul (V22.aHat r)).div_const 2).const_add r
    refine (hraw.congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall (fun x => by
        simp only [V22.yTilde, id_eq, Pi.add_apply])
    · simp only [mul_one]
  have hfull := (hdy.mul hdR).div ((hasDerivAt_id N).add_const 1) hn
  refine (hfull.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun x => by
      simp only [windowRadiusCost, id_eq, Pi.add_apply, Pi.mul_apply, Pi.div_apply])
  · simp only [V22.windowH, V22.yTilde, id_eq, Pi.add_apply, Pi.mul_apply, Pi.div_apply]
    field_simp [hR.ne', hn]
    ring_nf
    simp only [hRsq] <;> ring

theorem windowRadiusCost_strictMonoOn (hA4m : V22.Checks.lemma_7_9) {r : ℝ}
    (hrlo : (3793 / 10000 : ℝ) ≤ r) (hrh : r ≤ 1 / 2) :
    StrictMonoOn (windowRadiusCost r) (Ici (229 / 20)) := by
  have hr0 : 0 ≤ r := by linarith
  have hH0 := hA4m r ⟨hrlo, hrh⟩
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro N hN
    have hNlo : (229 / 20 : ℝ) ≤ N := hN
    exact (hasDerivAt_windowRadiusCost (by linarith : 1 < N)).continuousAt.continuousWithinAt
  · intro N hN
    have hNlo : (229 / 20 : ℝ) ≤ N := by
      have hm : N ∈ Ici (229 / 20 : ℝ) := interior_subset hN
      exact hm
    have hH := windowH_monotoneOn hr0 hrh (by norm_num : (229 / 20 : ℝ) ∈ Ici 3)
      (show N ∈ Ici 3 from by simp only [mem_Ici]; linarith) hNlo
    rw [(hasDerivAt_windowRadiusCost (by linarith : 1 < N)).deriv]
    exact div_pos (by linarith) (mul_pos (by norm_num) (windowUpperRadius_pos (by linarith : 0 < N)))

theorem windowRadiusCost_r_monotone {a b N : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 1 / 2) (hN : 10 ≤ N) : windowRadiusCost a N ≤ windowRadiusCost b N := by
  have hhat := window_aHat_monotone ha hab (by linarith : b < 1)
  have hy : V22.yTilde a N ≤ V22.yTilde b N := by
    have hm := mul_le_mul_of_nonneg_right hhat (show 0 ≤ N + 1 from by linarith)
    unfold V22.yTilde
    linarith
  have hyb := shared_yTilde_nonneg (ha.trans hab) (by linarith : b < 1) (by linarith : 0 < N)
  have hsq := (sq_le_sq₀ ha (ha.trans hab)).2 hab
  have hR : windowUpperRadius a N ≤ windowUpperRadius b N := by
    unfold windowUpperRadius
    apply Real.sqrt_le_sqrt
    nlinarith [mul_nonneg (sub_nonneg.mpr hsq) (sq_nonneg (N - 1))]
  unfold windowRadiusCost
  exact div_le_div_of_nonneg_right (mul_le_mul hy hR
    (windowUpperRadius_pos (by linarith : 0 < N)).le hyb) (by linarith)

/-- Corollary 5.15's varying-N, varying-r worst-end enclosure. The finite
A4m derivative numerator is used exactly on its original activity range. -/
theorem window_phiR_rectangular_lower (hA4m : V22.Checks.lemma_7_9)
    {ra r rb Na N Nb : ℝ} (hra : (3793 / 10000 : ℝ) ≤ ra)
    (har : ra ≤ r) (hrrb : r ≤ rb) (hrb : rb ≤ 1 / 2)
    (ha : (229 / 20 : ℝ) ≤ Na) (haN : Na ≤ N) (hNb : N ≤ Nb) :
    V22.phiRBlockLower ra rb Na Nb ≤ V22.phiR r N := by
  have hra0 : 0 ≤ ra := by linarith
  have hr0 := hra0.trans har
  have hrh := hrrb.trans hrb
  have hrb0 := hr0.trans hrrb
  have hNa : 10 ≤ Na := by linarith
  have hN : 10 ≤ N := hNa.trans haN
  have hNb10 := hN.trans hNb
  have hn : 0 < N := by linarith
  have hbn : 0 < Nb + 1 := by linarith
  have hshift := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 71 / 20)
    (show 0 < N + 1 from by linarith) (show N + 1 ≤ Nb + 1 from by linarith)
  have hstar := coefficient_rhoStar_pos hNa hrb0 hrb
  have hU := (coefficient_rhoStar_monotone hNa haN hrb0 hrb).trans
    (linearized_rhoU_lower hN hr0 hrrb hrb)
  have hD := (window_delta_r_monotone hra0 har hrh (by linarith : 1 ≤ Na)).trans
    (window_delta_N_monotone hr0 hrh (by linarith : 1 ≤ Na) haN)
  have hD0 := delta_nonneg (r := ra) (N := Na) (by linarith : 1 ≤ Na)
    (by nlinarith [coefficient_one_sub_rm_sq_pos hra0 (har.trans hrh)])
  have hprod := mul_le_mul hU hD hD0 (hstar.le.trans hU)
  have hsq := (sq_le_sq₀ hr0 hrb0).2 hrrb
  have hrho := coefficient_rho_monotone hN hNb
  have hrho0 : 0 ≤ V22.rho N := by unfold V22.rho; positivity
  have hfirst := mul_le_mul hsq hrho hrho0 (sq_nonneg rb)
  have hcostR := windowRadiusCost_r_monotone hr0 hrrb hrb hN
  have hcostN := (windowRadiusCost_strictMonoOn hA4m (hra.trans (har.trans hrrb)) hrb).monotoneOn
    (ha.trans haN) (ha.trans (haN.trans hNb)) hNb
  have hcost := hcostR.trans hcostN
  have hcmono := coefficient_cCoef_monotone hNa haN
  have hsmono := Real.sqrt_le_sqrt hcmono
  have hsa : 0 < Real.sqrt (V22.cCoef Na) := by
    have hc := (coefficient_cCoef_bounds hNa).1
    apply Real.sqrt_pos.2
    linarith
  have hden := mul_le_mul (show Na + 1 ≤ N + 1 from by linarith) hsmono
    (Real.sqrt_nonneg _) (show 0 ≤ N + 1 from by linarith)
  have he1 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (by positivity) hden
  have hd := coefficient_one_sub_rm_sq_pos hrb0 hrb
  have he2 := div_le_div_of_nonneg_left (sq_nonneg rb) (by positivity : 0 < 6 * (1 - rb ^ 2) * Real.sqrt (V22.cCoef Na))
    (mul_le_mul_of_nonneg_left hsmono (by positivity : 0 ≤ 6 * (1 - rb ^ 2)))
  have heps := linearized_epsilon_over_gamma_bound hN hr0 hrrb hrb
  have hn1 : 0 < N + 1 := by linarith
  have hsN : 0 < Real.sqrt (V22.cCoef N) := by
    apply Real.sqrt_pos.2
    linarith [linearized_cCoef_lower hN]
  have hepsHalf : V22.epsilonPrime r N / Real.sqrt (V22.gamma r N) / 2 ≤
      1 / ((N + 1) * Real.sqrt (V22.cCoef N)) + rb ^ 2 / (6 * (1 - rb ^ 2) * Real.sqrt (V22.cCoef N)) := by
    calc
      _ ≤ (2 / ((N + 1) * Real.sqrt (V22.cCoef N)) +
          rb ^ 2 / (3 * (1 - rb ^ 2) * Real.sqrt (V22.cCoef N))) / 2 :=
        div_le_div_of_nonneg_right heps (by norm_num : (0 : ℝ) ≤ 2)
      _ = _ := by field_simp [hn1.ne', hsN.ne', hd.ne'] <;> ring
  have hepscap : V22.epsilonPrime r N / Real.sqrt (V22.gamma r N) / 2 ≤
      1 / ((Na + 1) * Real.sqrt (V22.cCoef Na)) + rb ^ 2 / (6 * (1 - rb ^ 2) * Real.sqrt (V22.cCoef Na)) :=
    hepsHalf.trans (add_le_add he1 he2)
  have hcr := window_cr_monotone hr0 hrrb (by linarith : rb < 1)
  have hcr0 := shared_cr_nonneg hr0 (by linarith : r < 1)
  have hcrprod := mul_le_mul (show N + 1 ≤ Nb + 1 from by linarith) hcr hcr0 (by linarith : 0 ≤ Nb + 1)
  have hepsR := window_epsilon_radius hr0 (by linarith : r < 1) (by linarith : 1 < N)
  have hc0 : 0 ≤ V22.c0Prime r N := by unfold V22.c0Prime; positivity
  have hcosteq : windowRadiusCost r N =
      V22.epsilonPrime r N * Real.sqrt (V22.gamma r N) / 2 := by
    unfold windowRadiusCost
    calc
      _ = (2 * V22.yTilde r N * windowUpperRadius r N / (N + 1)) / 2 := by ring
      _ = _ := congrArg (fun x : ℝ => x / 2) hepsR.symm
  have hsplit : V22.epsilonPrime r N / 2 * (Real.sqrt (V22.gamma r N) + 1 / Real.sqrt (V22.gamma r N)) =
      windowRadiusCost r N + V22.epsilonPrime r N / Real.sqrt (V22.gamma r N) / 2 := by
    rw [hcosteq]
    ring
  have hprodHalf : V22.rhoStar Na rb * V22.Delta ra Na / 2 ≤
      V22.rhoU r N / 2 * V22.Delta r N := by
    convert div_le_div_of_nonneg_right hprod (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
  have hfirstHalf : r ^ 2 * V22.rho N / 2 ≤ rb ^ 2 * V22.rho Nb / 2 :=
    div_le_div_of_nonneg_right hfirst (by norm_num : (0 : ℝ) ≤ 2)
  have herror : V22.eU r N ≤ rb ^ 2 * V22.rho Nb / 2 + windowRadiusCost rb Nb +
      (1 / ((Na + 1) * Real.sqrt (V22.cCoef Na)) +
        rb ^ 2 / (6 * (1 - rb ^ 2) * Real.sqrt (V22.cCoef Na))) +
      (Nb + 1) * V22.cr rb := by
    unfold V22.eU
    rw [hsplit]
    have hsum := add_le_add (add_le_add hfirstHalf (add_le_add hcost hepscap)) hcrprod
    linarith only [hsum, hc0]
  unfold V22.phiRBlockLower V22.phiR
  dsimp only
  change (71 / 20 : ℝ) / (Nb + 1) + V22.rhoStar Na rb * V22.Delta ra Na / 2 -
      (rb ^ 2 * V22.rho Nb / 2 + windowRadiusCost rb Nb +
        (1 / ((Na + 1) * Real.sqrt (V22.cCoef Na)) +
          rb ^ 2 / (6 * (1 - rb ^ 2) * Real.sqrt (V22.cCoef Na))) +
        (Nb + 1) * V22.cr rb) ≤
    (71 / 20 : ℝ) / (N + 1) + V22.rhoU r N / 2 * V22.Delta r N - V22.eU r N
  exact sub_le_sub (add_le_add hshift hprodHalf) herror

end Erdos993Lean.Analytic.V22.Analysis
