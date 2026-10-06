import Erdos993Lean.Analytic.V22.Analysis.SpikeRayBounds
import Erdos993Lean.Analytic.V22.Analysis.OuterLowerError
import Erdos993Lean.Analytic.V22.Analysis.BetaMonotonicity

/-!
# Paper v2.2 Lemma5.7: the retained signed wing bonus

The actual indexed native fiber remains throughout. The first inequality of
Lemma4.7(b) is used before its bonus is split into positive-part remainders.
The general source wing function uses real M0 and N; a later exact adapter
identifies it with Checks.wingW. Positivity of beta_e is proved from the
original quarter-activity domain, rather than added to the source premises.
The parent lane exclusively owns Lean verification.
-/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

noncomputable section

theorem wing_rhoStar_lower {N rb : ℝ} (hN : 10 ≤ N) (hr0 : 0 ≤ rb) (hrb : rb ≤ 1 / 4) :
    (3 / 5 : ℝ) ≤ V22.rhoStar N rb := by
  have hn : 0 < N := by linarith
  have hn1 : 0 < N + 1 := by linarith
  have hrsq : rb ^ 2 ≤ (1 / 16 : ℝ) := by nlinarith
  have hd : (15 / 16 : ℝ) ≤ 1 - rb ^ 2 := by linarith
  have hs := (coefficient_sqrt_cCoef_bounds hN).1
  have hrho : (10 / 11 : ℝ) ≤ V22.rho N := by
    unfold V22.rho
    apply (le_div_iff₀ hn1).2
    linarith
  have hmain : (75 / 88 : ℝ) ≤ (1 - rb ^ 2) * V22.rho N := by
    have h := mul_le_mul hd hrho (by norm_num : (0 : ℝ) ≤ 10 / 11) (by linarith : 0 ≤ 1 - rb ^ 2)
    norm_num at h ⊢
    exact h
  have hden1 : (99 / 10 : ℝ) ≤ (N + 1) * Real.sqrt (V22.cCoef N) := by
    have h := mul_le_mul (show (11 : ℝ) ≤ N + 1 by linarith) hs
      (by norm_num : (0 : ℝ) ≤ 9 / 10) hn1.le
    norm_num at h
    exact h
  have hterm1 : 2 / ((N + 1) * Real.sqrt (V22.cCoef N)) ≤ (20 / 99 : ℝ) := by
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (0 : ℝ) < 99 / 10) hden1
    norm_num at h
    exact h
  have hden2 : (81 / 32 : ℝ) ≤ 3 * (1 - rb ^ 2) * Real.sqrt (V22.cCoef N) := by
    have h := mul_le_mul (mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 3)) hs
      (by norm_num : (0 : ℝ) ≤ 9 / 10) (by linarith : 0 ≤ 3 * (1 - rb ^ 2))
    norm_num at h
    exact h
  have hterm2 : rb ^ 2 / (3 * (1 - rb ^ 2) * Real.sqrt (V22.cCoef N)) ≤ (2 / 81 : ℝ) := by
    calc
      _ ≤ (1 / 16 : ℝ) / (3 * (1 - rb ^ 2) * Real.sqrt (V22.cCoef N)) :=
        div_le_div_of_nonneg_right hrsq (by positivity)
      _ ≤ (1 / 16 : ℝ) / (81 / 32) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden2
      _ = _ := by norm_num
  unfold V22.rhoStar
  linarith

/-- A deliberately coarse analytic estimate proving denominator positivity
on the complete quarter-activity domain, including both cap regimes. -/
theorem wing_E2_capped_bound {N rb : ℝ} (hN : 10 ≤ N) (hr0 : 0 ≤ rb) (hrb : rb ≤ 1 / 4) :
    V22.E2 N rb (cappedNu rb N) ≤ N / 5 := by
  let nm := cappedNu rb N
  let d := 1 - rb ^ 2
  have hn : 0 < N := by linarith
  have hnm : 0 ≤ nm := cappedNu_nonneg (N := N) hr0
  have hnm6 : nm ≤ 6 := min_le_left _ _
  have hnmRoot : nm ≤ Real.sqrt N / 4 := by
    have h1 : nm ≤ rb * Real.sqrt N := min_le_right _ _
    have h2 := mul_le_mul_of_nonneg_right hrb (Real.sqrt_nonneg N)
    linarith
  have hsqrt : Real.sqrt N ≤ N / 3 := by
    have hs := Real.sq_sqrt hn.le
    have hs0 := Real.sqrt_nonneg N
    have hs3 : (3 : ℝ) ≤ Real.sqrt N := by
      have h := Real.sqrt_le_sqrt (show (9 : ℝ) ≤ N by linarith)
      have h9 : Real.sqrt (9 : ℝ) = 3 := by norm_num
      simpa only [h9] using h
    have hprod := mul_nonneg hs0 (sub_nonneg.mpr hs3)
    nlinarith only [hs, hprod]
  have hnmLinear : nm ≤ N / 12 := by linarith
  have hnmSq : nm ^ 2 ≤ N / 16 := by
    have hsq := (sq_le_sq₀ hnm (by positivity : 0 ≤ Real.sqrt N / 4)).2 hnmRoot
    have hs := Real.sq_sqrt hn.le
    nlinarith
  have hnmCube : nm ^ 3 ≤ 3 * N / 8 := by
    have h1 := mul_le_mul_of_nonneg_right hnm6 (sq_nonneg nm)
    nlinarith
  have hd : (15 / 16 : ℝ) ≤ d := by dsimp [d]; nlinarith
  have hd0 : 0 < d := by linarith
  have hdsq : (225 / 256 : ℝ) ≤ d ^ 2 := by nlinarith
  have he3 : V22.e3 rb ≤ (8 / 9 : ℝ) := by
    change (5 : ℝ) / (6 * d) ≤ 8 / 9
    apply (div_le_iff₀ (by positivity : 0 < 6 * d)).2
    linarith
  have he4 : V22.e4 N rb ≤ (352 / 3375 : ℝ) := by
    change (N + 1) / (12 * N * d ^ 2) ≤ 352 / 3375
    apply (div_le_iff₀ (by positivity : 0 < 12 * N * d ^ 2)).2
    have h := mul_le_mul_of_nonneg_left hdsq hn.le
    nlinarith
  have he5 : V22.e5 rb ≤ (64 / 675 : ℝ) := by
    change (1 : ℝ) / (12 * d ^ 2) ≤ 64 / 675
    apply (div_le_iff₀ (by positivity : 0 < 12 * d ^ 2)).2
    linarith
  have h3 := mul_le_mul he3 hnmLinear hnm (by norm_num : (0 : ℝ) ≤ 8 / 9)
  have h4 := mul_le_mul he4 hnmSq (sq_nonneg nm) (by norm_num : (0 : ℝ) ≤ 352 / 3375)
  have h5 := mul_le_mul he5 hnmCube (by positivity : 0 ≤ nm ^ 3) (by norm_num : (0 : ℝ) ≤ 64 / 675)
  unfold V22.E2 V22.e2
  change (1 / 2 : ℝ) + V22.e3 rb * nm + V22.e4 N rb * nm ^ 2 + V22.e5 rb * nm ^ 3 ≤ N / 5
  linarith

theorem wing_cappedBeta_pos {N rb : ℝ} (hN : 10 ≤ N) (hr0 : 0 ≤ rb) (hrb : rb ≤ 1 / 4) :
    0 < V22.betaE N rb (cappedNu rb N) := by
  have hrs := wing_rhoStar_lower hN hr0 hrb
  have hrs0 : 0 < V22.rhoStar N rb := by linarith
  have hE := wing_E2_capped_bound hN hr0 hrb
  have hn : 0 < N := by linarith
  have hprod : 2 / V22.rhoStar N rb * V22.E2 N rb (cappedNu rb N) ≤ 2 * N / 3 := by
    have h1 : (2 : ℝ) / V22.rhoStar N rb ≤ 10 / 3 := by
      have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
        (by norm_num : (0 : ℝ) < 3 / 5) hrs
      norm_num at h
      exact h
    have h2 := mul_le_mul_of_nonneg_left hE (show 0 ≤ 2 / V22.rhoStar N rb by positivity)
    have h3 := mul_le_mul_of_nonneg_right h1 (show 0 ≤ N / 5 by positivity)
    nlinarith
  unfold V22.betaE
  linarith

noncomputable def wingKPrime (t M0 rb : ℝ) : ℝ :=
  V22.kappaA (M0 + 2) rb * V22.Ghat t M0 / V22.rhoStar (M0 + 2) rb

noncomputable def wingBPrime (t M0 rb : ℝ) : ℝ :=
  4 * V22.Ghat t M0 / V22.rhoStar (M0 + 2) rb

noncomputable def wingC (t M0 ra rb N : ℝ) : ℝ := (N - 1) / (1 - ra ^ 2) - wingKPrime t M0 rb

noncomputable def wingDe (M0 rb : ℝ) : ℝ :=
  4 / ((V22.rhoStar (M0 + 2) rb) ^ 2 * V22.betaE (M0 + 2) rb (cappedNu rb (M0 + 2)))

noncomputable def wingTau1 (t M0 : ℝ) : ℝ :=
  2 - 6 * V22.G (V22.lambdaT t) + (71 / 10 : ℝ) * |V22.G1 (V22.lambdaT t)| -
    (V22.kbar M0) ^ 2 * V22.G2 (V22.lambdaT t) / (M0 + 3)

noncomputable def wingW (t M0 ra rb N : ℝ) : ℝ :=
  (N - 2) * V22.gaussianSlack t + wingTau1 t M0 + wingC t M0 ra rb N * ra ^ 2 * N -
    wingBPrime t M0 rb * ra * Real.sqrt N - |V22.G1 (V22.lambdaT t)| * wingDe M0 rb

theorem wingC_monotone {t M0 ra rb N0 N : ℝ} (hra : ra ^ 2 < 1) (hN : N0 ≤ N) :
    wingC t M0 ra rb N0 ≤ wingC t M0 ra rb N := by
  have h := div_le_div_of_nonneg_right (show N0 - 1 ≤ N - 1 by linarith) (by linarith : 0 ≤ 1 - ra ^ 2)
  unfold wingC
  linarith

/-- The full source real wing function is convex on its starting half-line. -/
theorem source_wingW_convex {t M0 ra rb : ℝ} (hM0 : 8 ≤ M0)
    (hra : 0 ≤ ra) (hrar : ra ≤ rb) (hrb : rb ≤ 1 / 4) :
    ConvexOn ℝ (Ici (M0 + 2)) (wingW t M0 ra rb) := by
  have hN0 : 10 ≤ M0 + 2 := by linarith
  have hrs := coefficient_rhoStar_pos hN0 (hra.trans hrar) (by linarith : rb ≤ 1 / 2)
  have hGh : 0 ≤ V22.Ghat t M0 := by
    unfold V22.Ghat
    exact (shared_G_nonneg (V22.lambdaT t)).trans (le_max_left _ _)
  have hrap : 1 - ra ^ 2 > 0 := by nlinarith
  let A := ra ^ 2 / (1 - ra ^ 2)
  let B := V22.gaussianSlack t - A - wingKPrime t M0 rb * ra ^ 2
  let C := wingTau1 t M0 - 2 * V22.gaussianSlack t - |V22.G1 (V22.lambdaT t)| * wingDe M0 rb
  let K := wingBPrime t M0 rb * ra
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hK : 0 ≤ K := by dsimp [K, wingBPrime]; positivity
  have he : ∀ N : ℝ, wingW t M0 ra rb N = A * N ^ 2 + B * N + C - K * Real.sqrt N := by
    intro N
    dsimp [wingW, wingC, A, B, C, K]
    ring
  refine ⟨convex_Ici _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx0 : x ∈ Ici (0 : ℝ) := by
    change 0 ≤ x
    have h := hx
    change M0 + 2 ≤ x at h
    linarith only [h, hM0]
  have hy0 : y ∈ Ici (0 : ℝ) := by
    change 0 ≤ y
    have h := hy
    change M0 + 2 ≤ y at h
    linarith only [h, hM0]
  have hsq := (convexOn_pow (𝕜 := ℝ) 2).2 hx0 hy0 ha hb hab
  have hsqrt := Real.strictConcaveOn_sqrt.concaveOn.2 hx0 hy0 ha hb hab
  simp only [smul_eq_mul] at hsq hsqrt ⊢
  have hsqA := mul_le_mul_of_nonneg_left hsq hA
  have hsqrtK := mul_le_mul_of_nonneg_left hsqrt hK
  rw [he, he, he]
  have hC : a * C + b * C = C := by
    calc
      a * C + b * C = (a + b) * C := by ring
      _ = C := by rw [hab, one_mul]
  nlinarith only [hsqA, hsqrtK, hC]

/-- The native template keeps the signed first derivative on t<=1. -/
theorem wing_template_lower {M : ℕ} {mu M0 : ℝ} (hM0 : 8 ≤ M0) (hM : M0 ≤ (M : ℝ))
    (hmu : 0 < mu) (ht : (M : ℝ) / mu ≤ 1) :
    (M : ℝ) * V22.gaussianSlack ((M : ℝ) / mu) + wingTau1 ((M : ℝ) / mu) M0 ≤
      activityOneT ((M : ℝ) / mu) M := by
  let t := (M : ℝ) / mu
  have hM0p : 0 < M0 := by linarith
  have hMp : 0 < (M : ℝ) := hM0p.trans_le hM
  have ht0 : 0 < t := div_pos hMp hmu
  have hl : V22.lambdaT t ≤ 0 := by
    unfold V22.lambdaT
    have hlog := Real.log_nonpos ht0.le ht
    nlinarith
  have hG1 : V22.G1 (V22.lambdaT t) ≤ 0 := by
    have h := shared_G1_monotone hl
    simpa only [shared_G1_zero] using h
  have hkbar := template_kbar_antitone hM0p hM
  have hk0 := template_kbar_ge_lower hM0p
  have hG2 := (shared_G2_pos (V22.lambdaT t)).le
  have hAt : ∀ k : ℝ, (71 / 20 : ℝ) ≤ k → k ≤ V22.kbar M0 →
      (M : ℝ) * V22.gaussianSlack t + wingTau1 t M0 ≤ activityOneEndpointValue t M k := by
    intro k hklo hkhi
    have hkpos : 0 ≤ k := by linarith
    have hkbar0 : 0 ≤ V22.kbar M0 := by unfold V22.kbar; positivity
    have hsquare := (sq_le_sq₀ hkpos hkbar0).2 hkhi
    have hquad := div_le_div₀ (mul_nonneg (sq_nonneg (V22.kbar M0)) hG2)
      (mul_le_mul_of_nonneg_right hsquare hG2) (show 0 < M0 + 3 by linarith) (show M0 + 3 ≤ (M : ℝ) + 3 by linarith)
    have hlinear := mul_le_mul_of_nonneg_right hklo (show 0 ≤ -2 * V22.G1 (V22.lambdaT t) by linarith)
    unfold activityOneEndpointValue wingTau1
    simp only [← shared_gaussianSlack_eq, activityOneG0, activityOneG1, activityOneG2,
      ← shared_G_eq, ← shared_G1_eq, ← shared_G2_eq, ← shared_lambdaT_eq, abs_of_nonpos hG1]
    linarith
  unfold activityOneT
  apply le_min
  · exact hAt _ le_rfl (by simpa only [V22.kbar] using hk0)
  · exact hAt _ (template_kbar_ge_lower hMp) (by simpa only [V22.kbar] using hkbar)

/-- The second signed loss is bounded by its vertex value at the retained
starting N0. The actual growing cap is preserved in the beta comparison. -/
theorem wing_second_loss_bound {r rb N M0 : ℝ} (hM0 : 8 ≤ M0) (hN0 : M0 + 2 ≤ N)
    (hr0 : 0 ≤ r) (hrrb : r ≤ rb) (hrb : rb ≤ 1 / 4) (hnu6 : activityNu r N ≤ 6)
    (hBeta : MonotoneOn (V22.Checks.cappedBeta rb) (Ici (M0 + 2))) :
    2 * N / V22.rhoU r N * V22.eU r N - N * V22.Delta r N ≤ wingDe M0 rb := by
  let nu := activityNu r N
  let nm := cappedNu rb N
  let rs := V22.rhoStar N rb
  let beta := V22.betaE N rb nm
  have hNstart : 10 ≤ M0 + 2 := by linarith
  have hN : 10 ≤ N := hNstart.trans hN0
  have hrb0 := hr0.trans hrrb
  have hrh : r ≤ 1 / 2 := by linarith
  have hrbh : rb ≤ 1 / 2 := by linarith
  have hrs : 0 < rs := coefficient_rhoStar_pos hN hrb0 hrbh
  have hrs0 := coefficient_rhoStar_pos hNstart hrb0 hrbh
  have hrhoU := bonusRange_rhoU_pos hN hr0 hrh
  have hrsU := linearized_rhoU_lower hN hr0 hrrb hrbh
  have hnu : 0 ≤ nu := activityNu_nonneg hr0
  have hcap : nu ≤ nm := le_min hnu6 (mul_le_mul_of_nonneg_right hrrb (Real.sqrt_nonneg N))
  have hbonus : (N - 1) * nu ^ 2 ≤ N * V22.Delta r N :=
    scaled_delta_lower hN (by nlinarith : r ^ 2 < 1)
  have hE : 0 ≤ V22.E N rb nu := by
    have hd := coefficient_one_sub_rm_sq_pos hrb0 hrbh
    unfold V22.E V22.e2 V22.e3 V22.e4 V22.e5
    positivity
  have hEU := linearized_eU_upper hN hr0 hrrb hrbh
  have hEcap := closed_E_capped hN hrb0 hrbh hnu hcap
  have hLoss : 2 * N / V22.rhoU r N * V22.eU r N - N * V22.Delta r N ≤
      (4 / rs) * nu - beta * nu ^ 2 := by
    have h1 : 2 * N / V22.rhoU r N * V22.eU r N ≤
        2 / V22.rhoU r N * V22.E N rb nu := by
      calc
        _ = 2 / V22.rhoU r N * (N * V22.eU r N) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hEU (by positivity)
    have h2 : 2 / V22.rhoU r N * V22.E N rb nu ≤ 2 / rs * V22.E N rb nu := by
      calc
        _ = 2 * V22.E N rb nu / V22.rhoU r N := by ring
        _ ≤ 2 * V22.E N rb nu / rs :=
          div_le_div_of_nonneg_left (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hE) hrs hrsU
        _ = _ := by ring
    have h3 : 2 / rs * V22.E N rb nu ≤
        2 / rs * (2 * nu + V22.E2 N rb nm * nu ^ 2) :=
      mul_le_mul_of_nonneg_left hEcap (by positivity)
    have hChain := h1.trans (h2.trans h3)
    have heq : 2 / rs * (2 * nu + V22.E2 N rb nm * nu ^ 2) - (N - 1) * nu ^ 2 =
        (4 / rs) * nu - beta * nu ^ 2 := by dsimp [beta]; unfold V22.betaE; ring
    rw [← heq]
    linarith only [hChain, hbonus]
  have hbeta : 0 < beta := wing_cappedBeta_pos hN hrb0 hrb
  have hbeta0 := wing_cappedBeta_pos hNstart hrb0 hrb
  have hVertex := quadratic_le_vertex (a := 4 / rs) (nu := nu) hbeta
  have hVertexEq : (4 / rs) ^ 2 / (4 * beta) = 4 / (rs ^ 2 * beta) := by
    field_simp [hrs.ne', hbeta.ne'] <;> ring
  rw [hVertexEq] at hVertex
  have hbetaMono : V22.betaE (M0 + 2) rb (cappedNu rb (M0 + 2)) ≤ beta := by
    have h := hBeta (show M0 + 2 ∈ Ici (M0 + 2) from by simp only [mem_Ici]; exact le_rfl)
      (show N ∈ Ici (M0 + 2) by exact hN0) hN0
    simpa only [V22.Checks.cappedBeta, cappedNu] using h
  have hrsMono := coefficient_rhoStar_monotone hNstart hN0 hrb0 hrbh
  have hsq := (sq_le_sq₀ hrs0.le hrs.le).2 hrsMono
  have hden := mul_le_mul hsq hbetaMono hbeta0.le (sq_nonneg rs)
  have hcost : 4 / (rs ^ 2 * beta) ≤ wingDe M0 rb := by
    exact div_le_div_of_nonneg_left (by norm_num)
      (mul_pos (sq_pos_of_pos hrs0) hbeta0) hden
  exact hLoss.trans (hVertex.trans hcost)

theorem wing_quadratic_increasing {c b u nu : ℝ} (hc : 0 ≤ c) (hun : u ≤ nu)
    (hvertex : b ≤ 2 * c * u) : c * u ^ 2 - b * u ≤ c * nu ^ 2 - b * nu := by
  have hlinear : 0 ≤ c * (nu + u) - b := by
    have h := mul_nonneg hc (sub_nonneg.mpr hun)
    nlinarith
  have h := mul_nonneg (sub_nonneg.mpr hun) hlinear
  nlinarith only [h]

/-- Source Lemma5.7, its complete signed upper-range inequality. The only
finite input is the source's quarter-activity log-ratio license. -/
theorem source_wing_upper (hBonus : V22.Checks.lemma_7_7)
    {M : ℕ} {r ra rb mu M0 : ℝ} (hM0 : 8 ≤ M0) (hM : M0 ≤ (M : ℝ))
    (hra : 0 < ra) (hrar : ra ≤ r) (hrrb : r ≤ rb) (hrb : rb ≤ 1 / 4)
    (hmu : 0 < mu) (ht0 : (387 / 2500 : ℝ) ≤ (M : ℝ) / mu) (ht1 : (M : ℝ) / mu ≤ 3 / 5)
    (hBeta : MonotoneOn (V22.Checks.cappedBeta rb) (Ici (M0 + 2)))
    (hC : 0 < wingC ((M : ℝ) / mu) M0 ra rb (M0 + 2))
    (hvertex : wingBPrime ((M : ℝ) / mu) M0 rb /
        (2 * wingC ((M : ℝ) / mu) M0 ra rb (M0 + 2)) ≤ ra * Real.sqrt (M0 + 2))
    (j : ℤ) (hw : V22.gamma r ((M : ℝ) + 2) ≤ threeRangeW r M j) :
    min 2 (wingW ((M : ℝ) / mu) M0 ra rb ((M : ℝ) + 2)) ≤
      mu * (V22.fiberFunction ((1 + r) / 2) mu M j - V22.psi ((M : ℝ) / mu)) := by
  let N : ℝ := (M : ℝ) + 2
  let N0 := M0 + 2
  let t := (M : ℝ) / mu
  let nu := activityNu r N
  let c := wingC t M0 ra rb N
  let b := wingBPrime t M0 rb
  let Gh := V22.Ghat t M0
  have hN0 : 10 ≤ N0 := by dsimp [N0]; linarith
  have hNN : N0 ≤ N := by dsimp [N0, N]; linarith
  have hN : 10 ≤ N := hN0.trans hNN
  have hMnat : 8 ≤ M := by exact_mod_cast (hM0.trans hM)
  have hNnat : 10 ≤ M + 2 := by omega
  have hr0 := hra.le.trans hrar
  have hrb0 := hr0.trans hrrb
  have hrh : r ≤ 1 / 2 := by linarith
  have hrbh : rb ≤ 1 / 2 := by linarith
  have hrs0 := coefficient_rhoStar_pos hN0 hrb0 hrbh
  have hrs := coefficient_rhoStar_pos hN hrb0 hrbh
  have hGh : 0 ≤ Gh := by
    dsimp only [Gh, V22.Ghat]
    exact (shared_G_nonneg (V22.lambdaT t)).trans (le_max_left _ _)
  have hka0 := (coefficient_remaining_nonneg hN0 hrb0 hrbh).1
  have hnu : 0 ≤ nu := activityNu_nonneg hr0
  by_cases hl : 0 ≤ threeRangeLambdaU r mu M
  · have h := bonusRange_upper_nonnegative_fiber hNnat hr0 hrh hmu hl j hw
    rw [← shared_psi_eq] at h
    exact (min_le_left _ _).trans h
  have hneg : threeRangeLambdaU r mu M < 0 := lt_of_not_ge hl
  have hnu6 : nu ≤ 6 := by
    by_contra hlarge
    have hpos := (largeNu_upper_positive hNnat hr0 hrh (by linarith) hmu ht0 le_rfl).2
    linarith
  have hPaid := bonusRange_upper_negative_payment_fiber hNnat hr0 hrh hmu hneg j hw
  rw [← shared_psi_eq] at hPaid
  have hRecip := linearized_reciprocal_loss hN hr0 hrrb hrbh
  have hG := closed_template_G_upper hMnat hmu hM0 hM .U
  have hG0 := rootG_nonneg (activityOneLambda M mu .U)
  have hka := coefficient_kappaA_antitone hN0 hNN hrb0 hrbh
  have hrsMono := coefficient_rhoStar_monotone hN0 hNN hrb0 hrbh
  have hCoeff : (4 * nu + V22.kappaA N rb * nu ^ 2) / V22.rhoStar N rb ≤
      (4 * nu + V22.kappaA N0 rb * nu ^ 2) / V22.rhoStar N0 rb :=
    div_le_div₀ (by positivity)
      (by have h := mul_le_mul_of_nonneg_right hka (sq_nonneg nu); linarith only [h]) hrs0 hrsMono
  have hFirst : 2 * N * (1 / V22.rhoU r N - 1 / V22.rho N) * rootG (activityOneLambda M mu .U) ≤
      (4 * nu + V22.kappaA N0 rb * nu ^ 2) / V22.rhoStar N0 rb * Gh := by
    have h1 := mul_le_mul_of_nonneg_right hRecip hG0
    have h2 := mul_le_mul_of_nonneg_right hCoeff hG0
    have h3 := mul_le_mul_of_nonneg_left hG
      (show 0 ≤ (4 * nu + V22.kappaA N0 rb * nu ^ 2) / V22.rhoStar N0 rb by positivity)
    exact h1.trans (h2.trans h3)
  have hBonusLower : (N - 1) * nu ^ 2 / (1 - ra ^ 2) ≤ N * V22.Delta r N :=
    scaled_delta_lower_activity hN hra.le hrar (by nlinarith : r ^ 2 < 1)
  have hFirstNet : c * nu ^ 2 - b * nu ≤ N * V22.Delta r N -
      2 * N * (1 / V22.rhoU r N - 1 / V22.rho N) * rootG (activityOneLambda M mu .U) := by
    have hid : c * nu ^ 2 - b * nu =
        (N - 1) * nu ^ 2 / (1 - ra ^ 2) -
          (4 * nu + V22.kappaA N0 rb * nu ^ 2) / V22.rhoStar N0 rb * Gh := by
      dsimp [c, b, wingC, wingKPrime, wingBPrime, N0, Gh]
      ring
    rw [hid]
    linarith only [hBonusLower, hFirst]
  have hCs := wingC_monotone (t := t) (M0 := M0) (rb := rb)
    (by nlinarith : ra ^ 2 < 1) hNN
  have hc : 0 < c := hC.trans_le hCs
  have hu0 : 0 ≤ ra * Real.sqrt N0 := by positivity
  have hu : ra * Real.sqrt N0 ≤ ra * Real.sqrt N :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hNN) hra.le
  have hUnu : ra * Real.sqrt N ≤ nu := mul_le_mul_of_nonneg_right hrar (Real.sqrt_nonneg _)
  have hbVertex : b ≤ 2 * c * (ra * Real.sqrt N) := by
    have h0 := (div_le_iff₀ (show 0 < 2 * wingC t M0 ra rb N0 by positivity)).1 hvertex
    have h1 := mul_le_mul hCs hu hu0 (by positivity : 0 ≤ c)
    nlinarith only [h0, h1]
  have hQ := wing_quadratic_increasing hc.le hUnu hbVertex
  have hBaseSq : (ra * Real.sqrt N) ^ 2 = ra ^ 2 * N := by
    rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ N)]
  rw [hBaseSq] at hQ
  have hLast := wing_second_loss_bound hM0 hNN hr0 hrrb hrb hnu6 hBeta
  have hQuarter : V22.Checks.bonusConditions (1 / 4 : ℝ) 10 := by
    convert hBonus (1 / 4, 10) (by norm_num [V22.Checks.bonusPairs]) using 1 <;> norm_num
  have hSigma := lambdaBonus_sigma_bound hQuarter
    (by norm_num) (by norm_num) (by norm_num) (by linarith : (10 : ℝ) ≤ N)
    hr0 (by linarith : r ≤ 1 / 4) hmu hneg
  have hDe0 : 0 ≤ wingDe M0 rb := by
    have hBeta0 := wing_cappedBeta_pos hN0 hrb0 hrb
    unfold wingDe
    positivity
  have hLastScaled : |rootGPrime (threeRangeLambdaU r mu M)| *
      (2 * N / V22.rhoU r N * V22.eU r N - N * V22.Delta r N) ≤
      |V22.G1 (V22.lambdaT t)| * wingDe M0 rb := by
    have h1 := mul_le_mul_of_nonneg_left hLast (abs_nonneg (rootGPrime (threeRangeLambdaU r mu M)))
    have h2 := mul_le_mul_of_nonneg_right hSigma hDe0
    linarith only [h1, h2]
  have hTemplate := wing_template_lower hM0 hM hmu (by linarith : (M : ℝ) / mu ≤ 1)
  have hW : wingW t M0 ra rb N ≤ mu * (V22.fiberFunction ((1 + r) / 2) mu M j - V22.psi t) := by
    unfold wingW
    dsimp only [c, b, N0, Gh, N, t] at hPaid hFirstNet hQ hLastScaled hTemplate ⊢
    nlinarith only [hPaid, hFirstNet, hQ, hLastScaled, hTemplate]
  exact (min_le_right _ _).trans hW

end

end Erdos993Lean.Analytic.V22.Analysis
