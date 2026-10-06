import Erdos993Lean.Analytic.V22.Functions

/-!
# Transport of the retained window shape conditions

Source: repaired note Lemma 5.10, and the endpoint checks in Lemmas 7.17
and 7.18. The activity `r` remains fixed, while the real size parameter `N`
increases. The stronger condition `(c3')` is retained at the starting point;
the weaker `(c3)` is obtained using `0 < ρ < 1`.

These are analytic transports of explicit endpoint facts. This module does
not assert that any finite class endpoint check has passed.
-/

namespace Erdos993Lean.Analytic.V22

noncomputable section

/-- The common square-root ratio in both window radii decreases from `N=1`. -/
theorem sqrt_div_add_one_antitone {N N0 : ℝ} (hN0 : 1 ≤ N0) (hN : N0 ≤ N) :
    Real.sqrt N / (N + 1) ≤ Real.sqrt N0 / (N0 + 1) := by
  have hN0nonneg : 0 ≤ N0 := by linarith
  have hNnonneg : 0 ≤ N := by linarith
  have hN0den : 0 < N0 + 1 := by linarith
  have hNden : 0 < N + 1 := by linarith
  have hproduct : 1 ≤ N0 * N := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ N0 - 1) (by linarith : 0 ≤ N - 1)]
  have hgap : 0 ≤ (N - N0) * (N0 * N - 1) :=
    mul_nonneg (sub_nonneg.mpr hN) (sub_nonneg.mpr hproduct)
  have hsquare :
      (Real.sqrt N * (N0 + 1)) ^ 2 ≤ (Real.sqrt N0 * (N + 1)) ^ 2 := by
    calc
      _ = N * (N0 + 1) ^ 2 := by rw [mul_pow, Real.sq_sqrt hNnonneg]
      _ ≤ N0 * (N + 1) ^ 2 := by nlinarith
      _ = _ := by rw [mul_pow, Real.sq_sqrt hN0nonneg]
  have hcross : Real.sqrt N * (N0 + 1) ≤ Real.sqrt N0 * (N + 1) :=
    (sq_le_sq₀
      (mul_nonneg (Real.sqrt_nonneg N) hN0den.le)
      (mul_nonneg (Real.sqrt_nonneg N0) hNden.le)).mp hsquare
  exact (div_le_div_iff₀ hNden hN0den).mpr hcross

/-- The retained binomial variance is nonnegative on the activity range. -/
theorem varianceR_nonneg_of_activity {r : ℝ} (hr : 0 ≤ r) (hrhi : r ≤ 1 / 2) :
    0 ≤ varianceR r := by
  dsimp [varianceR]
  nlinarith [mul_nonneg hr (sub_nonneg.mpr hrhi)]

/-- The right radius decreases in the real size parameter; the activity
and the window width remain exactly the same. -/
theorem ZR_antitone_parameter {r N N0 W : ℝ}
    (hr : 0 ≤ r) (hrhi : r ≤ 1 / 2) (hN0 : 1 ≤ N0) (hN : N0 ≤ N) :
    ZR r N W ≤ ZR r N0 W := by
  have hvar := varianceR_nonneg_of_activity hr hrhi
  have hratio := sqrt_div_add_one_antitone hN0 hN
  have hfactor : 0 ≤ 2 * Real.sqrt W * Real.sqrt (varianceR r) := by positivity
  calc
    ZR r N W = (2 * Real.sqrt W * Real.sqrt (varianceR r)) *
        (Real.sqrt N / (N + 1)) := by
      dsimp [ZR, sN]
      rw [Real.sqrt_mul hvar]
      ring
    _ ≤ (2 * Real.sqrt W * Real.sqrt (varianceR r)) *
        (Real.sqrt N0 / (N0 + 1)) := mul_le_mul_of_nonneg_left hratio hfactor
    _ = ZR r N0 W := by
      dsimp [ZR, sN]
      rw [Real.sqrt_mul hvar]
      ring

/-- The left radius is the decreasing right radius plus `2r/(N+1)`. -/
theorem ZL_antitone_parameter {r N N0 W : ℝ}
    (hr : 0 ≤ r) (hrhi : r ≤ 1 / 2) (hN0 : 1 ≤ N0) (hN : N0 ≤ N) :
    ZL r N W ≤ ZL r N0 W := by
  have hright := ZR_antitone_parameter (W := W) hr hrhi hN0 hN
  have hN0den : 0 < N0 + 1 := by linarith
  have hquot : 2 * r / (N + 1) ≤ 2 * r / (N0 + 1) :=
    div_le_div_of_nonneg_left (by positivity) hN0den (add_le_add hN (le_refl 1))
  calc
    ZL r N W = ZR r N W + 2 * r / (N + 1) := by dsimp [ZL, ZR]; ring
    _ ≤ ZR r N0 W + 2 * r / (N0 + 1) := add_le_add hright hquot
    _ = ZL r N0 W := by dsimp [ZL, ZR]; ring

/-- The stronger right-window condition improves with the size parameter. -/
theorem windowC3Prime_monotone_parameter {r N N0 : ℝ}
    (hr : 0 ≤ r) (hrhi : r ≤ 1 / 2) (hN0 : 1 ≤ N0) (hN : N0 ≤ N) :
    12 * (1 - (r + ZR r N0 3) ^ 2) / (1 - r ^ 2) ≤
      12 * (1 - (r + ZR r N 3) ^ 2) / (1 - r ^ 2) := by
  have hden : 0 < 1 - r ^ 2 := by
    nlinarith [mul_nonneg hr (sub_nonneg.mpr hrhi)]
  have hN0den : 0 ≤ N0 + 1 := by linarith
  have hNden : 0 ≤ N + 1 := by linarith
  have hright := ZR_antitone_parameter (W := 3) hr hrhi hN0 hN
  have hright0 : 0 ≤ ZR r N0 3 :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg 3))
      (Real.sqrt_nonneg (varianceR r*N0))) hN0den
  have hrightN : 0 ≤ ZR r N 3 :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg 3))
      (Real.sqrt_nonneg (varianceR r*N))) hNden
  have hsquare : (r + ZR r N 3) ^ 2 ≤ (r + ZR r N0 3) ^ 2 :=
    (sq_le_sq₀ (add_nonneg hr hrightN) (add_nonneg hr hright0)).mpr
      (add_le_add (le_refl r) hright)
  exact div_le_div_of_nonneg_right (by nlinarith) hden.le

/-- The actual size coefficient lies strictly between zero and one. -/
theorem rho_pos_lt_one {N : ℝ} (hN : 0 < N) : 0 < rho N ∧ rho N < 1 := by
  have hden : 0 < N + 1 := by linarith
  constructor
  · exact div_pos hN hden
  · exact (div_lt_one hden).mpr (by linarith)

/-- The persistent condition `(c3')` implies `(c3)` with its actual `ρ`. -/
theorem windowC3Prime_implies_c3 {r N : ℝ}
    (hr : 0 ≤ r) (hrhi : r ≤ 1 / 2) (hN : 0 < N)
    (hprime : 3 ≤ 12 * (1 - (r + ZR r N 3) ^ 2) / (1 - r ^ 2)) :
    3 ≤ 12 * (1 - (r + ZR r N 3) ^ 2) / ((1 - r ^ 2) * rho N) := by
  have hden : 0 < 1 - r ^ 2 := by
    nlinarith [mul_nonneg hr (sub_nonneg.mpr hrhi)]
  have hrho := rho_pos_lt_one hN
  have hnum : 0 ≤ 12 * (1 - (r + ZR r N 3) ^ 2) := by
    have hcleared := (le_div_iff₀ hden).mp hprime
    linarith
  have htotal : 0 < (1 - r ^ 2) * rho N := mul_pos hden hrho.1
  have hdenorder : (1 - r ^ 2) * rho N ≤ 1 - r ^ 2 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hrho.2.le hden.le
  exact hprime.trans (div_le_div_of_nonneg_left hnum htotal hdenorder)

/-- A checked starting `(c1),(c2),(c3')` packet persists at every larger
real size, keeping its activity fixed. -/
theorem persistentWindowConditions_transport {r N N0 : ℝ}
    (hr : 0 ≤ r) (hrhi : r ≤ 1 / 2) (hN0 : 1 ≤ N0) (hN : N0 ≤ N)
    (hstart : persistentWindowConditions r N0) :
    persistentWindowConditions r N := by
  refine ⟨(ZL_antitone_parameter hr hrhi hN0 hN).trans_lt hstart.1,
    (add_le_add (le_refl r) (ZR_antitone_parameter hr hrhi hN0 hN)).trans_lt hstart.2.1,
    hstart.2.2.trans (windowC3Prime_monotone_parameter hr hrhi hN0 hN)⟩

/-- The endpoint packet used by Lemma 7.18 supplies the complete original
shape conditions for every larger real size. -/
theorem windowConditions_of_persistent_start {r N N0 : ℝ}
    (hr : 0 ≤ r) (hrhi : r ≤ 1 / 2) (hN0 : 1 ≤ N0) (hN : N0 ≤ N)
    (hstart : persistentWindowConditions r N0) : windowConditions r N := by
  have htransport := persistentWindowConditions_transport hr hrhi hN0 hN hstart
  exact ⟨htransport.1, htransport.2.1,
    windowC3Prime_implies_c3 hr hrhi (by linarith) htransport.2.2⟩

end

end Erdos993Lean.Analytic.V22
