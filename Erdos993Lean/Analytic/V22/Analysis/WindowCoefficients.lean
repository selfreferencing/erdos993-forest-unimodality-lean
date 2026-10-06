import Erdos993Lean.Analytic.V22.Analysis.WindowUpper
import Erdos993Lean.Analytic.V22.Analysis.TemplateMonotonicity

/-! Source: the real-size transfer in the proof of note Theorem 5.14.
The error is the actual width-three error at the actual activity. Its
antitonicity includes the factor N+1 multiplying each quartic radius.
No central-amplitude interpolation is used. Parent owns Lean verification. -/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

theorem window_epsilon_antitone {r Na N : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : 10 ≤ Na) (haN : Na ≤ N) : V22.epsilon r N ≤ V22.epsilon r Na := by
  have hv := shared_varianceR_pos hr0 hr1
  have hz := coefficient_Z0_antitone ha haN
  have hm := mul_le_mul_of_nonneg_left hz (show 0 ≤ r / Real.sqrt (V22.varianceR r) from by positivity)
  have hs : 0 < Real.sqrt (V22.varianceR r) := Real.sqrt_pos.2 hv
  have ha1 : 0 < Na + 1 := by linarith
  have hn1 : 0 < N + 1 := by linarith
  unfold V22.epsilon V22.Z0 at *
  convert hm using 1 <;> field_simp [hs.ne', ha1.ne', hn1.ne'] <;> ring

theorem window_c0_antitone {r Na N : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : 10 ≤ Na) (haN : Na ≤ N) : V22.c0 r N ≤ V22.c0 r Na := by
  have hv := shared_varianceR_pos hr0 hr1
  unfold V22.c0
  apply div_le_div_of_nonneg_left (sq_nonneg r) (by positivity)
  exact mul_le_mul_of_nonneg_left (by linarith : Na + 1 ≤ N + 1) (by positivity)

private theorem window_quartic_scale_antitone {Na N : ℝ} (ha : 10 ≤ Na) (haN : Na ≤ N) :
    N ^ 2 / (N + 1) ^ 3 ≤ Na ^ 2 / (Na + 1) ^ 3 := by
  have hn : 10 ≤ N := ha.trans haN
  have hd : 0 ≤ Na ^ 2 * N ^ 2 - 3 * Na * N - Na - N := by
    have hap : 0 ≤ Na * N - 4 := by nlinarith
    have hprod := mul_nonneg hap (show 0 ≤ Na * N from by positivity)
    have hlinear : Na + N ≤ Na * N := by
      nlinarith [mul_nonneg (show 0 ≤ Na - 2 from by linarith) (show 0 ≤ N - 2 from by linarith)]
    nlinarith
  have hmul := mul_nonneg (sub_nonneg.mpr haN) hd
  apply (div_le_div_iff₀ (by positivity : 0 < (N + 1) ^ 3)
    (by positivity : 0 < (Na + 1) ^ 3)).2
  nlinarith [hmul]

private theorem window_radius_quartic_scaled {r N : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hN : 10 ≤ N) :
    (N + 1) * (V22.ZL r N 3) ^ 4 =
      16 * (Real.sqrt 3 * Real.sqrt (V22.varianceR r)) ^ 4 *
        (N ^ 2 / (N + 1) ^ 3) *
        (1 + r / (Real.sqrt 3 * Real.sqrt (V22.varianceR r) * Real.sqrt N)) ^ 4 ∧
    (N + 1) * (V22.ZR r N 3) ^ 4 =
      16 * (Real.sqrt 3 * Real.sqrt (V22.varianceR r)) ^ 4 * (N ^ 2 / (N + 1) ^ 3) := by
  have hv := shared_varianceR_pos hr0 hr1
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 (by linarith)
  have hs3 : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hsv := Real.sqrt_pos.2 hv
  have hsq := Real.sq_sqrt (show 0 ≤ N from by linarith)
  have hfour : (Real.sqrt N) ^ 4 = N ^ 2 := by
    calc
      (Real.sqrt N) ^ 4 = ((Real.sqrt N) ^ 2) ^ 2 := by ring
      _ = N ^ 2 := by rw [hsq]
  have hsN : V22.sN r N = Real.sqrt (V22.varianceR r) * Real.sqrt N := by
    unfold V22.sN
    exact Real.sqrt_mul hv.le N
  have hfactorL : V22.ZL r N 3 =
      (2 * (Real.sqrt 3 * Real.sqrt (V22.varianceR r)) * Real.sqrt N / (N + 1)) *
        (1 + r / (Real.sqrt 3 * Real.sqrt (V22.varianceR r) * Real.sqrt N)) := by
    unfold V22.ZL
    rw [hsN]
    field_simp [hs.ne', hs3.ne', hsv.ne', (show 0 < N + 1 from by linarith).ne'] <;> ring
  have hfactorR : V22.ZR r N 3 =
      2 * (Real.sqrt 3 * Real.sqrt (V22.varianceR r)) * Real.sqrt N / (N + 1) := by
    unfold V22.ZR
    rw [hsN]
    ring
  constructor
  · rw [hfactorL]
    simp only [mul_pow, div_pow]
    rw [hfour]
    field_simp [hs.ne', hs3.ne', hsv.ne', (show 0 < N + 1 from by linarith).ne'] <;> ring
  · rw [hfactorR]
    simp only [mul_pow, div_pow]
    rw [hfour]
    field_simp [hs.ne', hs3.ne', hsv.ne', (show 0 < N + 1 from by linarith).ne'] <;> ring

theorem window_quartic_numerators_antitone {r Na N : ℝ} (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2)
    (ha : 10 ≤ Na) (haN : Na ≤ N) :
    (N + 1) * (V22.ZL r N 3) ^ 4 ≤ (Na + 1) * (V22.ZL r Na 3) ^ 4 ∧
    (N + 1) * (V22.ZR r N 3) ^ 4 ≤ (Na + 1) * (V22.ZR r Na 3) ^ 4 := by
  have hr1 : r < 1 := by linarith
  have hn := ha.trans haN
  have hscale := window_quartic_scale_antitone ha haN
  have hv := shared_varianceR_pos hr0 hr1
  have haS : 0 < Real.sqrt 3 * Real.sqrt (V22.varianceR r) * Real.sqrt Na := by positivity
  have hsden : Real.sqrt 3 * Real.sqrt (V22.varianceR r) * Real.sqrt Na ≤
      Real.sqrt 3 * Real.sqrt (V22.varianceR r) * Real.sqrt N :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt haN) (by positivity)
  have hfrac := div_le_div_of_nonneg_left hr0 haS hsden
  have hbase : 1 + r / (Real.sqrt 3 * Real.sqrt (V22.varianceR r) * Real.sqrt N) ≤
      1 + r / (Real.sqrt 3 * Real.sqrt (V22.varianceR r) * Real.sqrt Na) := by linarith
  have hpow := pow_le_pow_left₀ (show 0 ≤ 1 + r /
    (Real.sqrt 3 * Real.sqrt (V22.varianceR r) * Real.sqrt N) from by positivity) hbase 4
  have hprod := mul_le_mul hscale hpow (by positivity) (by positivity)
  have hscaled := mul_le_mul_of_nonneg_left hprod
    (show 0 ≤ 16 * (Real.sqrt 3 * Real.sqrt (V22.varianceR r)) ^ 4 from by positivity)
  rw [(window_radius_quartic_scaled hr0 hr1 hn).1,
    (window_radius_quartic_scaled hr0 hr1 ha).1]
  refine ⟨by simpa only [mul_assoc] using hscaled, ?_⟩
  rw [(window_radius_quartic_scaled hr0 hr1 hn).2,
    (window_radius_quartic_scaled hr0 hr1 ha).2]
  exact mul_le_mul_of_nonneg_left hscale (by positivity)

theorem window_quarticError_antitone {r Na N : ℝ} (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2)
    (ha : 10 ≤ Na) (haN : Na ≤ N) (hc : V22.persistentWindowConditions r Na) :
    V22.quarticError r N 3 ≤ V22.quarticError r Na 3 := by
  have hr1 : r < 1 := by linarith
  have hd := shared_one_sub_sq_pos (by linarith : -1 < r) hr1
  have hrad := window_radii_antitone hr0 hrh ha haN
  have hnum := window_quartic_numerators_antitone hr0 hrh ha haN
  have hsNa : 0 ≤ V22.sN r Na := by unfold V22.sN; exact Real.sqrt_nonneg _
  have hsN : 0 ≤ V22.sN r N := by unfold V22.sN; exact Real.sqrt_nonneg _
  have ha0 : 0 < Na := by linarith
  have hn0 : 0 < N := by linarith
  have hZa : 0 ≤ V22.ZL r Na 3 := by unfold V22.ZL; positivity
  have hZn : 0 ≤ V22.ZL r N 3 := by unfold V22.ZL; positivity
  have hRa : 0 ≤ r + V22.ZR r Na 3 := by unfold V22.ZR; positivity
  have hRn : 0 ≤ r + V22.ZR r N 3 := by unfold V22.ZR; positivity
  have hDLa := shared_one_sub_sq_pos (by linarith : -1 < V22.ZL r Na 3) hc.1
  have hDRa := shared_one_sub_sq_pos (by linarith : -1 < r + V22.ZR r Na 3) hc.2.1
  have hsqL := (sq_le_sq₀ hZn hZa).2 hrad.1
  have hsqR := (sq_le_sq₀ hRn hRa).2 (show r + V22.ZR r N 3 ≤ r + V22.ZR r Na 3 from by linarith)
  have hdenL : 12 * (1 - (V22.ZL r Na 3) ^ 2) * (1 - r ^ 2) ≤
      12 * (1 - (V22.ZL r N 3) ^ 2) * (1 - r ^ 2) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith :
        1 - (V22.ZL r Na 3) ^ 2 ≤ 1 - (V22.ZL r N 3) ^ 2) (by norm_num)) hd.le
  have hdenR : 12 * (1 - (r + V22.ZR r Na 3) ^ 2) * (1 - r ^ 2) ≤
      12 * (1 - (r + V22.ZR r N 3) ^ 2) * (1 - r ^ 2) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith :
        1 - (r + V22.ZR r Na 3) ^ 2 ≤ 1 - (r + V22.ZR r N 3) ^ 2) (by norm_num)) hd.le
  unfold V22.quarticError
  apply max_le_max
  · exact div_le_div₀ (by positivity) hnum.1 (by positivity) hdenL
  · exact div_le_div₀ (by positivity) hnum.2 (by positivity) hdenR

theorem windowEL_antitone {r Na N : ℝ} (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2)
    (ha : 10 ≤ Na) (haN : Na ≤ N) (hc : V22.persistentWindowConditions r Na) :
    V22.windowEL r N ≤ V22.windowEL r Na := by
  have hc0 := window_c0_antitone hr0 (by linarith : r < 1) ha haN
  have hquart := window_quarticError_antitone hr0 hrh ha haN hc
  have heps := mul_le_mul_of_nonneg_right
    (window_epsilon_antitone hr0 (by linarith : r < 1) ha haN)
    (show 0 ≤ Real.sqrt 3 / 2 + 1 / (2 * Real.sqrt 3) from by positivity)
  unfold V22.windowEL
  linarith

theorem windowRhoLbar_antitone {r Na N : ℝ} (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2)
    (ha : 10 ≤ Na) (haN : Na ≤ N) : V22.windowRhoLbar r N ≤ V22.windowRhoLbar r Na := by
  have h := div_le_div_of_nonneg_right (window_epsilon_antitone hr0 (by linarith : r < 1) ha haN)
    (Real.sqrt_nonneg (3 : ℝ))
  unfold V22.windowRhoLbar
  linarith

theorem window_hbar_antitone {Ma M : ℝ} (ha : 0 < Ma) (haM : Ma ≤ M) : V22.hbar M ≤ V22.hbar Ma := by
  have hm : 0 < M := ha.trans_le haM
  have hk := template_kbar_antitone ha haM
  have hk0 : 0 ≤ (77 / 20 : ℝ) + 10 / Ma := by positivity
  unfold V22.hbar V22.kbar
  exact (div_le_div_of_nonneg_right hk (by positivity : 0 ≤ M + 3)).trans
    (div_le_div_of_nonneg_left hk0 (by linarith : 0 < Ma + 3) (by linarith : Ma + 3 ≤ M + 3))

end Erdos993Lean.Analytic.V22.Analysis
