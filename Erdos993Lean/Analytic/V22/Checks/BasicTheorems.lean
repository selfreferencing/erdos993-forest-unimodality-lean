import Erdos993Lean.Analytic.V22.Checks.EvaluatedBasic
import Erdos993Lean.Analytic.V22.A0D0Sound
import Erdos993Lean.Analytic.V22.A1Sound
import Erdos993Lean.Analytic.V22.B1Sound

/-! Repaired note Lemmas 7.1, 7.2, 7.12 and 7.16, from actual compiled
Boolean checks and the independently proved real soundness consumers. -/
namespace Erdos993Lean.Analytic.V22.Checked

theorem lemma_7_1 : Checks.lemma_7_1 := lemma_7_1_of_pass Checks.Evaluated.a0

theorem lemma_7_2 : Checks.lemma_7_2 := A1Sound.check_sound Checks.Evaluated.a1

theorem lemma_7_12 : Checks.lemma_7_12 := B1Sound.check_sound Checks.Evaluated.b1

theorem lemma_7_16 : Checks.lemma_7_16 :=
  lemma_7_16_of_pass (List.all_eq_true.mp Checks.Evaluated.d0)

end Erdos993Lean.Analytic.V22.Checked
