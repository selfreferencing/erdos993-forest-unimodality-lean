import Erdos993Lean.Analytic.V22.Analysis.LinearizedBounds

/-!
# Section 4: the exact linearized lower-range error

Source: frozen note Lemma 4.10(a). The two source psi identities retain
the actual activity r; their coefficients are then bounded at the retained
cap rm. Consumer: the three-range lower minorant remainder. Coefficient
monotonicity in N is owned by the separate lane worker. Root compiles.
-/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

theorem linearized_phiM_eq {r N : ℝ} (hN : 0 < N) : V22.phiM N r = monotonePhi r N := by
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  unfold V22.phiM monotonePhi activityNu
  field_simp [hN.ne', hs.ne']
  nlinarith [congrArg (fun t : ℝ => 2 * r * t) (Real.sq_sqrt hN.le)]

theorem linearized_psiL_identity {r N : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hN : 10 ≤ N) :
    monotonePsiL r N - 1 =
      (((monotonePhi r N) ^ 2 - 1) *
        (1 + (monotonePhi r N) ^ 2 / (1 - (V22.Z0 N) ^ 2 * (monotonePhi r N) ^ 2)) + r ^ 2) /
        (1 - r ^ 2) := by
  have hn : 0 < N := by linarith
  obtain ⟨_, _, _, hp0, hp1, _, _⟩ := monotone_quartic_domains hr0 hrh hN
  have hdr := (shared_one_sub_sq_pos (by linarith : -1 < r) (by linarith : r < 1)).ne'
  have hdp : 1 - (V22.Z0 N) ^ 2 * (monotonePhi r N) ^ 2 ≠ 0 := by
    rw [← mul_pow]
    exact (shared_one_sub_sq_pos (by linarith : -1 < V22.Z0 N * monotonePhi r N) hp1).ne'
  unfold monotonePsiL
  rw [activityNu_quotient hn]
  have hdp' : 1 - (monotonePhi r N) ^ 2 * (V22.Z0 N) ^ 2 ≠ 0 := by
    convert hdp using 1 <;> ring
  field_simp [hdr, hdp] <;> ring_nf <;> field_simp [hdp'] <;> ring

theorem linearized_psiR_identity {r N : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hN : 10 ≤ N) :
    monotonePsiR r N - 1 =
      ((activityNu r N ^ 2 / N + 2 * activityNu r N / (N + 1)) /
        (1 - (r + V22.Z0 N) ^ 2) + activityNu r N ^ 2 / N) / (1 - r ^ 2) := by
  have hn : 0 < N := by linarith
  have hn1 : N + 1 ≠ 0 := ne_of_gt (by linarith)
  obtain ⟨_, _, _, _, _, hrt0, hrt1⟩ := monotone_quartic_domains hr0 hrh hN
  have hdr := (shared_one_sub_sq_pos (by linarith : -1 < r) (by linarith : r < 1)).ne'
  have hdt := (shared_one_sub_sq_pos (by linarith : -1 < r + V22.Z0 N) hrt1).ne'
  unfold monotonePsiR
  rw [activityNu_quotient hn]
  have he : 2 * activityNu r N / (N + 1) = 2 * r * V22.Z0 N := by
    unfold activityNu V22.Z0
    ring
  rw [he]
  field_simp [hdr, hdt] <;> ring

theorem linearized_KL_comparison {r rm N : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hrmh : rm ≤ 1 / 2) :
    1 + (monotonePhi r N) ^ 2 / (1 - (V22.Z0 N) ^ 2 * (monotonePhi r N) ^ 2) ≤ V22.KL N rm := by
  have hn : 0 < N := by linarith
  have hrm0 : 0 ≤ rm := hr0.trans hrrm
  have hrh : r ≤ 1 / 2 := hrrm.trans hrmh
  obtain ⟨_, _, hph0, hp0, hp1, _, _⟩ := monotone_quartic_domains hr0 hrh hN
  obtain ⟨_, _, hpm0, hpmul0, hpmul1, _, _⟩ := monotone_quartic_domains hrm0 hrmh hN
  have hph : monotonePhi r N ≤ monotonePhi rm N := by
    unfold monotonePhi activityNu
    gcongr
  have hphsq : (monotonePhi r N) ^ 2 ≤ (monotonePhi rm N) ^ 2 := (sq_le_sq₀ hph0.le hpm0.le).2 hph
  have hdr : 0 < 1 - (V22.Z0 N) ^ 2 * (monotonePhi r N) ^ 2 := by
    rw [← mul_pow]
    exact shared_one_sub_sq_pos (by linarith) hp1
  have hdm : 0 < 1 - (V22.Z0 N) ^ 2 * (monotonePhi rm N) ^ 2 := by
    rw [← mul_pow]
    exact shared_one_sub_sq_pos (by linarith) hpmul1
  unfold V22.KL
  rw [linearized_phiM_eq hn]
  apply add_le_add le_rfl
  calc
    _ ≤ (monotonePhi rm N) ^ 2 / (1 - (V22.Z0 N) ^ 2 * (monotonePhi r N) ^ 2) :=
      div_le_div_of_nonneg_right hphsq hdr.le
    _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg _) hdm
      (by nlinarith [mul_le_mul_of_nonneg_left hphsq (sq_nonneg (V22.Z0 N))])

theorem linearized_KR_comparison {r rm N : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hrmh : rm ≤ 1 / 2) :
    1 / (1 - (r + V22.Z0 N) ^ 2) ≤ V22.KR N rm := by
  have hrm0 : 0 ≤ rm := hr0.trans hrrm
  obtain ⟨hZ0, _, _, _, _, hm0, hm1⟩ := monotone_quartic_domains hrm0 hrmh hN
  have hdm := shared_one_sub_sq_pos (by linarith : -1 < rm + V22.Z0 N) hm1
  unfold V22.KR
  apply one_div_le_one_div_of_le hdm
  nlinarith

theorem linearized_KL_nonneg {rm N : ℝ} (hN : 10 ≤ N) (hrm0 : 0 ≤ rm) (hrmh : rm ≤ 1 / 2) :
    0 ≤ V22.KL N rm := by
  have hn : 0 < N := by linarith
  obtain ⟨_, _, _, hm0, hm1, _, _⟩ := monotone_quartic_domains hrm0 hrmh hN
  have hden : 0 < 1 - (V22.Z0 N) ^ 2 * (monotonePhi rm N) ^ 2 := by
    rw [← mul_pow]
    exact shared_one_sub_sq_pos (by linarith) hm1
  unfold V22.KL
  rw [linearized_phiM_eq hn]
  exact add_nonneg (by norm_num) (div_nonneg (sq_nonneg _) hden.le)

theorem linearized_KR_nonneg {rm N : ℝ} (hN : 10 ≤ N) (hrm0 : 0 ≤ rm) (hrmh : rm ≤ 1 / 2) :
    0 ≤ V22.KR N rm := by
  obtain ⟨_, _, _, _, _, hm0, hm1⟩ := monotone_quartic_domains hrm0 hrmh hN
  unfold V22.KR
  exact div_nonneg (by norm_num) (shared_one_sub_sq_pos (by linarith) hm1).le

theorem linearized_psiL_upper {r rm N : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hrmh : rm ≤ 1 / 2) :
    monotonePsiL r N - 1 ≤ V22.cL1 N rm * activityNu r N + V22.cL2 N rm * activityNu r N ^ 2 := by
  have hn : 0 < N := by linarith
  have hrm0 : 0 ≤ rm := hr0.trans hrrm
  have hrh : r ≤ 1 / 2 := hrrm.trans hrmh
  have hdr := shared_one_sub_sq_pos (by linarith : -1 < r) (by linarith : r < 1)
  have hdm := shared_one_sub_sq_pos (by linarith : -1 < rm) (by linarith : rm < 1)
  have hsq : r ^ 2 ≤ rm ^ 2 := (sq_le_sq₀ hr0 hrm0).2 hrrm
  have hnu := activityNu_nonneg (N := N) hr0
  have hph : 1 ≤ monotonePhi r N := by
    unfold monotonePhi
    have ha : 0 ≤ 2 * activityNu r N / N := by positivity
    linarith
  have hphdiff : 0 ≤ (monotonePhi r N) ^ 2 - 1 := by nlinarith
  have hK := linearized_KL_comparison hN hr0 hrrm hrmh
  have hKn := linearized_KL_nonneg hN hrm0 hrmh
  rw [linearized_psiL_identity hr0 hrh hN]
  have hnum := add_le_add (mul_le_mul_of_nonneg_left hK hphdiff) (le_refl (r ^ 2))
  have hnumNonneg : 0 ≤ ((monotonePhi r N) ^ 2 - 1) * V22.KL N rm + r ^ 2 :=
    add_nonneg (mul_nonneg hphdiff hKn) (sq_nonneg r)
  calc
    _ ≤ (((monotonePhi r N) ^ 2 - 1) * V22.KL N rm + r ^ 2) / (1 - r ^ 2) :=
      div_le_div_of_nonneg_right hnum hdr.le
    _ ≤ (((monotonePhi r N) ^ 2 - 1) * V22.KL N rm + r ^ 2) / (1 - rm ^ 2) :=
      div_le_div_of_nonneg_left hnumNonneg hdm (by linarith)
    _ = _ := by
      have hphiEq : (monotonePhi r N) ^ 2 - 1 =
          4 * activityNu r N / N + 4 * activityNu r N ^ 2 / N ^ 2 := by
        unfold monotonePhi
        ring
      rw [hphiEq, ← activityNu_quotient (r := r) hn]
      unfold V22.cL1 V22.cL2
      field_simp [hn.ne', hdm.ne'] <;> ring

theorem linearized_psiR_upper {r rm N : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hrmh : rm ≤ 1 / 2) :
    monotonePsiR r N - 1 ≤ V22.cR1 N rm * activityNu r N + V22.cR2 N rm * activityNu r N ^ 2 := by
  have hn : 0 < N := by linarith
  have hn1 : 0 < N + 1 := by linarith
  have hrm0 : 0 ≤ rm := hr0.trans hrrm
  have hrh : r ≤ 1 / 2 := hrrm.trans hrmh
  have hdr := shared_one_sub_sq_pos (by linarith : -1 < r) (by linarith : r < 1)
  have hdm := shared_one_sub_sq_pos (by linarith : -1 < rm) (by linarith : rm < 1)
  have hsq : r ^ 2 ≤ rm ^ 2 := (sq_le_sq₀ hr0 hrm0).2 hrrm
  have hnu := activityNu_nonneg (N := N) hr0
  have hK := linearized_KR_comparison hN hr0 hrrm hrmh
  have hKn := linearized_KR_nonneg hN hrm0 hrmh
  have hcoef : 0 ≤ activityNu r N ^ 2 / N + 2 * activityNu r N / (N + 1) := by positivity
  rw [linearized_psiR_identity hr0 hrh hN]
  have hprod := mul_le_mul_of_nonneg_left hK hcoef
  have hnum : (activityNu r N ^ 2 / N + 2 * activityNu r N / (N + 1)) /
      (1 - (r + V22.Z0 N) ^ 2) + activityNu r N ^ 2 / N ≤
      (activityNu r N ^ 2 / N + 2 * activityNu r N / (N + 1)) * V22.KR N rm + activityNu r N ^ 2 / N := by
    simpa only [div_eq_mul_inv, one_mul] using add_le_add hprod (le_refl (activityNu r N ^ 2 / N))
  have hnumNonneg : 0 ≤ (activityNu r N ^ 2 / N + 2 * activityNu r N / (N + 1)) * V22.KR N rm + activityNu r N ^ 2 / N := by positivity
  calc
    _ ≤ ((activityNu r N ^ 2 / N + 2 * activityNu r N / (N + 1)) * V22.KR N rm + activityNu r N ^ 2 / N) / (1 - r ^ 2) :=
      div_le_div_of_nonneg_right hnum hdr.le
    _ ≤ ((activityNu r N ^ 2 / N + 2 * activityNu r N / (N + 1)) * V22.KR N rm + activityNu r N ^ 2 / N) / (1 - rm ^ 2) :=
      div_le_div_of_nonneg_left hnumNonneg hdm (by linarith)
    _ = _ := by
      unfold V22.cR1 V22.cR2
      field_simp [hn.ne', hn1.ne', hdm.ne'] <;> ring

theorem linearized_psi_max_upper {r rm N : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hrmh : rm ≤ 1 / 2) :
    max (monotonePsiL r N) (monotonePsiR r N) - 1 ≤
      max (V22.cL1 N rm) (V22.cR1 N rm) * activityNu r N +
        max (V22.cL2 N rm) (V22.cR2 N rm) * activityNu r N ^ 2 := by
  have hnu := activityNu_nonneg (N := N) hr0
  have hL := linearized_psiL_upper hN hr0 hrrm hrmh
  have hR := linearized_psiR_upper hN hr0 hrrm hrmh
  have hL1 := mul_le_mul_of_nonneg_right (le_max_left (V22.cL1 N rm) (V22.cR1 N rm)) hnu
  have hL2 := mul_le_mul_of_nonneg_right (le_max_left (V22.cL2 N rm) (V22.cR2 N rm)) (sq_nonneg (activityNu r N))
  have hR1 := mul_le_mul_of_nonneg_right (le_max_right (V22.cL1 N rm) (V22.cR1 N rm)) hnu
  have hR2 := mul_le_mul_of_nonneg_right (le_max_right (V22.cL2 N rm) (V22.cR2 N rm)) (sq_nonneg (activityNu r N))
  have hmax : max (monotonePsiL r N) (monotonePsiR r N) ≤ 1 +
      max (V22.cL1 N rm) (V22.cR1 N rm) * activityNu r N +
        max (V22.cL2 N rm) (V22.cR2 N rm) * activityNu r N ^ 2 := by
    apply max_le <;> linarith
  linarith

/-- Exact source Lemma 4.10(a), with the shared coefficient definitions. -/
theorem linearized_eL_upper {r rm N : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ r) (hrrm : r ≤ rm) (hrmh : rm ≤ 1 / 2) :
    (N + 1) * V22.eL r N ≤ V22.alpha1 N rm * activityNu r N + V22.alpha2 N rm * activityNu r N ^ 2 := by
  have hn : 0 < N := by linarith
  have hrm0 : 0 ≤ rm := hr0.trans hrrm
  have hrh : r ≤ 1 / 2 := hrrm.trans hrmh
  have hdr := shared_one_sub_sq_pos (by linarith : -1 < r) (by linarith : r < 1)
  have hdm := shared_one_sub_sq_pos (by linarith : -1 < rm) (by linarith : rm < 1)
  have hsq : r ^ 2 ≤ rm ^ 2 := (sq_le_sq₀ hr0 hrm0).2 hrrm
  have hnu := activityNu_nonneg (N := N) hr0
  have h := monotone_eL_upper hr0 hrh hN
  have hquad : 2 * activityNu r N ^ 2 / (N - activityNu r N ^ 2) ≤
      2 * activityNu r N ^ 2 / (N * (1 - rm ^ 2)) := by
    rw [activityNu_gap hn]
    exact div_le_div_of_nonneg_left (by positivity) (mul_pos hn hdm)
      (mul_le_mul_of_nonneg_left (by linarith : 1 - rm ^ 2 ≤ 1 - r ^ 2) hn.le)
  have hlin : 2 * activityNu r N / Real.sqrt (1 - activityNu r N ^ 2 / N) ≤
      2 * activityNu r N / Real.sqrt (1 - rm ^ 2) := by
    rw [activityNu_quotient hn]
    exact div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.2 hdm)
      (Real.sqrt_le_sqrt (by linarith))
  have hpsi := linearized_psi_max_upper hN hr0 hrrm hrmh
  have hpsiScaled := mul_le_mul_of_nonneg_left hpsi (by norm_num : (0 : ℝ) ≤ 1 / 12)
  unfold V22.alpha1 V22.alpha2
  simp only [div_eq_mul_inv] at *
  nlinarith

end Erdos993Lean.Analytic.V22.Analysis
