import Erdos993Lean.Analytic.V22.Analysis.QuadraticBounds

/-!
# The lower-range bonus payment

Source: the last displayed comparison in Proposition 4.6. This algebraic
helper retains the numerator, its actual root denominator and the signed
bonus. The root comparison and the native lower minorant are supplied by the
analytic range theorem; this helper does not assert a fiber theorem by itself.
-/

namespace Erdos993Lean.Analytic.V22.Analysis

theorem lower_bonus_loss {N rhoL Delta e s s0 : ℝ} (hN : 0 < N)
    (hrho : 0 < rhoL) (hrhoN : N / (N + 1) ≤ rhoL)
    (hDelta : 0 ≤ Delta) (he : 0 ≤ e) (hs : 0 ≤ s)
    (hsbar : s ≤ s0 + rhoL / 2 * Delta) :
    -max (2 * (N + 1) * e * max s0 0 - N * Delta * (1 - e)) 0 ≤
      N * (Delta - 2 / rhoL * e * s) / (1 + s) := by
  let bar := s0 + rhoL / 2 * Delta
  let c := 2 * N / rhoL * e
  have hb : 0 ≤ bar := hs.trans hsbar
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hN1 : 0 < N + 1 := by linarith
  have hcoef : 2 * N / rhoL ≤ 2 * (N + 1) := by
    have hmul := (div_le_iff₀ hN1).1 hrhoN
    apply (div_le_iff₀ hrho).2
    nlinarith
  have hce : c ≤ 2 * (N + 1) * e := by
    dsimp [c]
    exact mul_le_mul_of_nonneg_right hcoef he
  have hsmax : s0 ≤ max s0 0 := le_max_left _ _
  have hcs : c * s0 ≤ 2 * (N + 1) * e * max s0 0 :=
    (mul_le_mul_of_nonneg_left hsmax hc).trans
      (mul_le_mul_of_nonneg_right hce (le_max_right _ _))
  have hnum : N * Delta * (1 - e) - 2 * (N + 1) * e * max s0 0 ≤
      N * Delta - c * bar := by
    have heq : N * Delta - c * bar = N * Delta * (1 - e) - c * s0 := by
      dsimp [c, bar]
      field_simp [hrho.ne']
      ring
    rw [heq]
    linarith
  have hdiv : (N * Delta - c * bar) / (1 + bar) ≤
      (N * Delta - c * s) / (1 + s) := by
    apply (div_le_div_iff₀ (by linarith : 0 < 1 + bar) (by linarith : 0 < 1 + s)).2
    have hpay : 0 ≤ (N * Delta + c) * (bar - s) :=
      mul_nonneg (add_nonneg (mul_nonneg hN.le hDelta) hc) (sub_nonneg.mpr hsbar)
    nlinarith
  have hfirst := lowerRemainder_div_bound
    (2 * (N + 1) * e * max s0 0) (N * Delta * (1 - e)) bar hb
  have hsecond := div_le_div_of_nonneg_right hnum (show 0 ≤ 1 + bar by linarith)
  have h := (hfirst.trans hsecond).trans hdiv
  convert h using 1
  dsimp [c]
  ring

end Erdos993Lean.Analytic.V22.Analysis
