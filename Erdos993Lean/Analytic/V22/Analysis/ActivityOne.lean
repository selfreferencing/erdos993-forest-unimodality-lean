import Erdos993Lean.Analytic.V22.Analysis.AmplitudeShift
import Erdos993Lean.Analytic.V22.Analysis.RootGTaylor
import Mathlib.Tactic

/-!
# Paper v2.2: Gaussian slack and the activity-one bound

Source: Definition 3.10 and Proposition 3.11. The exact upper/lower
prefactors and Lemma 3.9 supply the shift and k bounds; the public theorem
has only the original `M >= 8`, `mu > 0` and choice `X in {U,L}`.
Consumer: E4's activity-dependent fiber decomposition and E5's deficits.

Independent proof draft; root lane owns Lean compilation. No Lean/lake
process is run by the drafting agent.
-/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

inductive ActivityOneSide where
  | U
  | L
  deriving DecidableEq

noncomputable def activityOnePrefactor (side : ActivityOneSide) (N : ℕ) : ℝ :=
  match side with
  | .U => symmetricUpperPrefactor N
  | .L => symmetricLowerPrefactor N

noncomputable def activityOneAmplitude (side : ActivityOneSide) (N : ℕ) : ℝ :=
  match side with
  | .U => upperAmplitude N
  | .L => lowerAmplitude N

noncomputable def activityOneK (M : ℕ) (side : ActivityOneSide) : ℝ :=
  logShiftKValue (M : ℝ) (Real.log (activityOneAmplitude side (M + 2)))

noncomputable def activityOneLambda (M : ℕ) (mu : ℝ) (side : ActivityOneSide) : ℝ :=
  shapeTemplateLambda mu ((M : ℝ) + 2) (activityOnePrefactor side (M + 2))

/-- Definition 3.10: `lambda_t`. -/
noncomputable def activityOneLambda_t (t : ℝ) : ℝ := (5 / 2 : ℝ) * Real.log t

noncomputable def activityOneG0 (t : ℝ) : ℝ := rootG (activityOneLambda_t t)
noncomputable def activityOneG1 (t : ℝ) : ℝ := rootGPrime (activityOneLambda_t t)
noncomputable def activityOneG2 (t : ℝ) : ℝ := rootGSecond (activityOneLambda_t t)

/-- Definition 3.10: the exact Gaussian slack. -/
noncomputable def activityOneS (t : ℝ) : ℝ :=
  (9 / 2 : ℝ) * ((t - 1) ^ 2 / t) - 2 * activityOneG0 t

noncomputable def activityOneEndpointValue (t M k : ℝ) : ℝ :=
  M * activityOneS t + 2 - 6 * activityOneG0 t -
    2 * k * activityOneG1 t - k ^ 2 * activityOneG2 t / (M + 3)

/-- Definition 3.10: the minimum of the two exact endpoint values. -/
noncomputable def activityOneT (t M : ℝ) : ℝ :=
  min (activityOneEndpointValue t M (71 / 20))
    (activityOneEndpointValue t M ((77 / 20) + 10 / M))

noncomputable def activityOnePsi (t : ℝ) : ℝ := t - (9 / 2 : ℝ) * (t - 1) ^ 2

/-- Definition 3.10's alternate coordinate, used only on `s>-1`. -/
noncomputable def activityOneCoordinate (s : ℝ) : ℝ :=
  (Real.exp s * (1 + s)) ^ (2 / 5 : ℝ)

theorem activityOneCoordinate_pos {s : ℝ} (hs : -1 < s) : 0 < activityOneCoordinate s := by
  unfold activityOneCoordinate
  exact Real.rpow_pos_of_pos (mul_pos (Real.exp_pos s) (by linarith)) _

theorem activityOneCoordinate_lambda {s : ℝ} (hs : -1 < s) :
    activityOneLambda_t (activityOneCoordinate s) = rootEquation s := by
  unfold activityOneLambda_t activityOneCoordinate rootEquation
  rw [Real.log_rpow (mul_pos (Real.exp_pos s) (by linarith)),
    Real.log_mul (Real.exp_pos s).ne' (by linarith : 1 + s ≠ 0), Real.log_exp]
  ring

theorem activityOneCoordinate_strictMonoOn : StrictMonoOn activityOneCoordinate (Ioi (-1)) := by
  intro s hs t ht hst
  have hs' : -1 < s := by simpa only [mem_Ioi] using hs
  have hprod : Real.exp s * (1 + s) < Real.exp t * (1 + t) :=
    mul_lt_mul (Real.exp_lt_exp.mpr hst) (by linarith) (by linarith) (Real.exp_pos t).le
  unfold activityOneCoordinate
  exact Real.rpow_lt_rpow (mul_pos (Real.exp_pos s) (by linarith)).le hprod (by norm_num)

theorem activityOneCoordinate_root {s : ℝ} (hs : -1 < s) :
    rootMap (activityOneLambda_t (activityOneCoordinate s)) = s :=
  rootMap_eq_of_equation hs (activityOneCoordinate_lambda hs).symm

theorem activityOnePrefactor_pos (side : ActivityOneSide) {N : ℕ} (hN : 2 ≤ N) :
    0 < activityOnePrefactor side N := by
  cases side with
  | U => exact symmetricUpperPrefactor_pos N
  | L => exact symmetricLowerPrefactor_pos hN

theorem activityOneK_bounds {M : ℕ} (hM : 8 ≤ M) (side : ActivityOneSide) :
    (71 / 20 : ℝ) ≤ activityOneK M side ∧
      activityOneK M side ≤ (77 / 20 : ℝ) + 10 / (M : ℝ) := by
  cases side with
  | U => exact (amplitude_k_bounds hM).1
  | L => exact (amplitude_k_bounds hM).2

theorem activityOneLambda_shift {M : ℕ} {mu : ℝ} (hM : 1 ≤ M) (hmu : 0 < mu)
    (side : ActivityOneSide) :
    activityOneLambda M mu side = activityOneLambda_t ((M : ℝ) / mu) +
      activityOneK M side / ((M : ℝ) + 3) := by
  have hMr : 0 < (M : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℕ) < 1) hM)
  have hx : 0 < activityOnePrefactor side (M + 2) := activityOnePrefactor_pos side (by omega)
  have hamp : shapeAmplitude ((M : ℝ) + 2) (activityOnePrefactor side (M + 2)) =
      activityOneAmplitude side (M + 2) := by
    cases side <;> simp [activityOnePrefactor, activityOneAmplitude, upperAmplitude,
      lowerAmplitude, Nat.cast_add]
  have he := shapeTemplateLambda_shift hmu hMr hx
  rw [hamp] at he
  exact he

/-- A concave quadratic on a closed interval is bounded below by its smaller
endpoint value. The interpolation gap is retained exactly. -/
theorem concaveQuadratic_endpoint_min (A d c a b k : ℝ) (hc : 0 ≤ c)
    (hak : a ≤ k) (hkb : k ≤ b) :
    min (A - d * a - c * a ^ 2) (A - d * b - c * b ^ 2) ≤ A - d * k - c * k ^ 2 := by
  let Q : ℝ → ℝ := fun x => A - d * x - c * x ^ 2
  have hab : a ≤ b := hak.trans hkb
  by_cases heq : a = b
  · have hka : k = a := le_antisymm (by simpa [heq] using hkb) hak
    simp [hka, heq]
  · have hba : 0 < b - a := sub_pos.mpr (lt_of_le_of_ne hab heq)
    have hlin : (b - a) * min (Q a) (Q b) ≤ (b - k) * Q a + (k - a) * Q b := by
      calc
        (b - a) * min (Q a) (Q b) =
            (b - k) * min (Q a) (Q b) + (k - a) * min (Q a) (Q b) := by ring
        _ ≤ (b - k) * Q a + (k - a) * Q b :=
          add_le_add (mul_le_mul_of_nonneg_left (min_le_left _ _) (sub_nonneg.mpr hkb))
            (mul_le_mul_of_nonneg_left (min_le_right _ _) (sub_nonneg.mpr hak))
    have hgap : (b - a) * Q k - ((b - k) * Q a + (k - a) * Q b) =
        c * (b - a) * (k - a) * (b - k) := by dsimp [Q]; ring
    have hn : 0 ≤ (b - a) * Q k - ((b - k) * Q a + (k - a) * Q b) := by
      rw [hgap]
      exact mul_nonneg (mul_nonneg (mul_nonneg hc hba.le) (sub_nonneg.mpr hak)) (sub_nonneg.mpr hkb)
    have he := hlin.trans (sub_nonneg.mp hn)
    exact (mul_le_mul_iff_right₀ hba).mp he

theorem activityOneT_le_at_k {t M k : ℝ} (hM : 0 < M)
    (hkl : (71 / 20 : ℝ) ≤ k) (hku : k ≤ (77 / 20 : ℝ) + 10 / M) :
    activityOneT t M ≤ activityOneEndpointValue t M k := by
  let A := M * activityOneS t + 2 - 6 * activityOneG0 t
  let d := 2 * activityOneG1 t
  let c := activityOneG2 t / (M + 3)
  have hc : 0 ≤ c := div_nonneg (rootGSecond_pos _).le (by linarith)
  have hf : ∀ x, activityOneEndpointValue t M x = A - d * x - c * x ^ 2 := by
    intro x
    dsimp [activityOneEndpointValue, A, d, c]
    ring
  unfold activityOneT
  rw [hf, hf, hf]
  exact concaveQuadratic_endpoint_min A d c (71 / 20) ((77 / 20) + 10 / M) k hc hkl hku

/-- The exact identity printed in Proposition 3.11. -/
theorem activityOne_exact_identity {M mu lambda : ℝ} (hM : 0 < M) (hmu : 0 < mu) :
    mu * ((M + 2) / mu * (1 - 2 / ((M + 2) / (M + 3)) * rootG lambda) -
      activityOnePsi (M / mu)) =
    M + 2 - mu * activityOnePsi (M / mu) - 2 * (M + 3) * rootG lambda := by
  have hM2 : M + 2 ≠ 0 := ne_of_gt (by linarith)
  have hM3 : M + 3 ≠ 0 := ne_of_gt (by linarith)
  field_simp [hmu.ne', hM2, hM3] <;> ring

private theorem activityOne_bound_from_shift {M mu lambda k : ℝ} (hM : 0 < M) (hmu : 0 < mu)
    (hlambda : lambda = activityOneLambda_t (M / mu) + k / (M + 3))
    (hkl : (71 / 20 : ℝ) ≤ k) (hku : k ≤ (77 / 20 : ℝ) + 10 / M) :
    activityOneT (M / mu) M ≤
      mu * ((M + 2) / mu * (1 - 2 / ((M + 2) / (M + 3)) * rootG lambda) -
        activityOnePsi (M / mu)) := by
  have hM3 : 0 < M + 3 := by linarith
  have ht : 0 < M / mu := div_pos hM hmu
  have hkh : 0 ≤ k / (M + 3) := div_nonneg (by linarith) hM3.le
  have hTaylor := rootG_taylor_shift_upper (activityOneLambda_t (M / mu)) (k / (M + 3)) hkh
  have hscaled := mul_le_mul_of_nonneg_left hTaylor (show (0 : ℝ) ≤ 2 * (M + 3) by positivity)
  have hG : 2 * (M + 3) * rootG lambda ≤
      2 * (M + 3) * activityOneG0 (M / mu) + 2 * k * activityOneG1 (M / mu) +
        k ^ 2 * activityOneG2 (M / mu) / (M + 3) := by
    rw [hlambda]
    convert hscaled using 1 <;>
      dsimp [activityOneG0, activityOneG1, activityOneG2] <;>
      field_simp [hM3.ne'] <;> ring
  have hbase : M + 2 - mu * activityOnePsi (M / mu) =
      2 + (9 / 2 : ℝ) * M * ((M / mu - 1) ^ 2 / (M / mu)) := by
    unfold activityOnePsi
    field_simp [hM.ne', hmu.ne'] <;> ring
  have he : activityOneEndpointValue (M / mu) M k ≤
      M + 2 - mu * activityOnePsi (M / mu) - 2 * (M + 3) * rootG lambda := by
    rw [hbase]
    dsimp [activityOneEndpointValue, activityOneS]
    nlinarith
  rw [activityOne_exact_identity hM hmu]
  exact (activityOneT_le_at_k hM hkl hku).trans he

/-- Proposition 3.11, with exactly the original assumptions and native
upper/lower choice. Both the displayed identity and lower bound are retained. -/
theorem activityOne_bound (M : ℕ) (mu : ℝ) (side : ActivityOneSide) (hM : 8 ≤ M) (hmu : 0 < mu) :
    let t := (M : ℝ) / mu
    let B := ((M : ℝ) + 2) / mu
    let rho := ((M : ℝ) + 2) / ((M : ℝ) + 3)
    let lambda := activityOneLambda M mu side
    mu * (B * (1 - 2 / rho * rootG lambda) - activityOnePsi t) =
      (M : ℝ) + 2 - mu * activityOnePsi t - 2 * ((M : ℝ) + 3) * rootG lambda ∧
    activityOneT t (M : ℝ) ≤ mu * (B * (1 - 2 / rho * rootG lambda) - activityOnePsi t) := by
  have hMr : 0 < (M : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℕ) < 8) hM)
  have hshift := activityOneLambda_shift (by omega : 1 ≤ M) hmu side
  have hk := activityOneK_bounds hM side
  dsimp only
  exact ⟨activityOne_exact_identity hMr hmu, activityOne_bound_from_shift hMr hmu hshift hk.1 hk.2⟩

end Erdos993Lean.Analytic.V22.Analysis
