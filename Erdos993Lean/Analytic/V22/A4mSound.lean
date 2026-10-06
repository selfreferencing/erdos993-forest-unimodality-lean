import Erdos993Lean.Analytic.V22.Compute.A4m
import Erdos993Lean.Analytic.V22.GridSound
import Erdos993Lean.Analytic.V22.WindowExprsSound
import Erdos993Lean.Analytic.V22.Checks.EarlyStatements

/-! A4m pure-enclosure soundness for every actual r in the closed range. -/

namespace Erdos993Lean.Analytic.V22.Compute.A4m

theorem check_sound (h : check = true) : Checks.lemma_7_9 := by
  simp only [check, Bool.and_eq_true] at h
  intro r hr
  have hr' : ((3793/10000 : Rat) : ℝ) ≤ r ∧ r ≤ ((1/2 : Rat) : ℝ) := by
    simpa [Checks.inCell] using hr
  have hh := nonnegativeOn_sound h.1 h.2 hr'
  norm_num [recipe, Expr.evalR, realSpanEnv] at hh
  linarith

end Erdos993Lean.Analytic.V22.Compute.A4m
