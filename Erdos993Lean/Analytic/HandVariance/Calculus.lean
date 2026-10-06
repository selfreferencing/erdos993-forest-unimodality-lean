import Erdos993Lean.Analytic.Reserve.Step

/-!
# Primitive derivatives for the hand variance bound

Source: `for_tong/TWIN_v1.8/apx_hand.tex`, Lemmas `tgt:lem:dY` and
`tgt:lem:tr`, in `ProofRuns/2026-09-28_analytic_large_n/LEAN`.
The parameters are the actual parent or child log-masses of the reserve.
-/

namespace Erdos993Lean.Analytic.HandVariance

open Real Reserve

/-- Source: `tgt:lem:dY`, the derivative of the downward message in log-mass. -/
theorem hasDerivAt_msg_Y {lam Y : ℝ} (hlam : 0 < lam) :
    HasDerivAt (msg lam) (-msg lam Y * (1 - msg lam Y)) Y := by
  let R : ℝ := lam * exp (-Y)
  have hR : HasDerivAt (fun x : ℝ => lam * exp (-x)) (-R) Y := by
    convert ((Real.hasDerivAt_exp (-Y)).comp Y (hasDerivAt_neg Y)).const_mul lam using 1
    simp [R]
  have hd : 1 + R ≠ 0 := by
    have : 0 < R := mul_pos hlam (exp_pos _)
    linarith
  convert hR.div ((hasDerivAt_const Y (1 : ℝ)).add hR) hd using 1
  dsimp [msg, R]
  field_simp
  ring

/-- Source: `tgt:lem:dY`, the derivative of the log-mass. -/
theorem hasDerivAt_lmass_Y {lam Y : ℝ} (hlam : 0 < lam) :
    HasDerivAt (lmass lam) (-msg lam Y) Y := by
  let R : ℝ := lam * exp (-Y)
  have hR : HasDerivAt (fun x : ℝ => lam * exp (-x)) (-R) Y := by
    convert ((Real.hasDerivAt_exp (-Y)).comp Y (hasDerivAt_neg Y)).const_mul lam using 1
    simp [R]
  have hd : 1 + R ≠ 0 := by
    have : 0 < R := mul_pos hlam (exp_pos _)
    linarith
  convert (((hasDerivAt_const Y (1 : ℝ)).add hR).log hd) using 1
  dsimp [msg, R]
  ring

/-- Source: `tgt:lem:tr`, the message derivative in `mu = log activity`. -/
theorem hasDerivAt_msg_mu (Y mu : ℝ) :
    HasDerivAt (fun x : ℝ => msg (exp x) Y)
      (msg (exp mu) Y * (1 - msg (exp mu) Y)) mu := by
  let R : ℝ := exp mu * exp (-Y)
  have hR : HasDerivAt (fun x : ℝ => exp x * exp (-Y)) R mu :=
    (Real.hasDerivAt_exp mu).mul_const _
  have hd : 1 + R ≠ 0 := by
    have : 0 < R := mul_pos (exp_pos _) (exp_pos _)
    linarith
  convert hR.div ((hasDerivAt_const mu (1 : ℝ)).add hR) hd using 1
  dsimp [msg, R]
  field_simp
  ring

/-- Source: `tgt:lem:tr`, the log-mass derivative in `mu = log activity`. -/
theorem hasDerivAt_lmass_mu (Y mu : ℝ) :
    HasDerivAt (fun x : ℝ => lmass (exp x) Y) (msg (exp mu) Y) mu := by
  let R : ℝ := exp mu * exp (-Y)
  have hR : HasDerivAt (fun x : ℝ => exp x * exp (-Y)) R mu :=
    (Real.hasDerivAt_exp mu).mul_const _
  have hd : 1 + R ≠ 0 := by
    have : 0 < R := mul_pos (exp_pos _) (exp_pos _)
    linarith
  convert (((hasDerivAt_const mu (1 : ℝ)).add hR).log hd) using 1
  dsimp [msg, R]
  rw [zero_add]

end Erdos993Lean.Analytic.HandVariance
