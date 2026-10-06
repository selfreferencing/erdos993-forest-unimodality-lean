import Erdos993Lean.Analytic.V22.Checks.EvaluatedCoefficients
import Erdos993Lean.Analytic.V22.CoefficientChecksSound
import Erdos993Lean.Analytic.V22.A4dSound
import Erdos993Lean.Analytic.V22.A4mSound
import Erdos993Lean.Analytic.V22.LargeTSound
import Erdos993Lean.Analytic.V22.SpikeLowerChecksSound
import Erdos993Lean.Analytic.V22.WindowChecksSound

/-! Exact consumers of the repaired source statements. These wrappers retain
the complete real hypotheses and ranges. Their numerical dependencies and
the wrappers themselves must pass the lane's serial Lean verification queue.
-/

namespace Erdos993Lean.Analytic.V22.Checked

theorem lemma_7_4 : Checks.lemma_7_4 :=
  Compute.CoefficientChecks.a3OK_sound Checks.Evaluated.a3

theorem lemma_7_5 : Checks.lemma_7_5 :=
  Compute.CoefficientChecks.a3PrimeOK_sound Checks.Evaluated.a3Prime

theorem lemma_7_6 : Checks.lemma_7_6 :=
  Compute.CoefficientChecks.a4OK_sound Checks.Evaluated.a4

theorem lemma_7_7 : Checks.lemma_7_7 :=
  Compute.CoefficientChecks.a4PrimeOK_sound Checks.Evaluated.a4Prime

theorem lemma_7_8 : Checks.lemma_7_8 :=
  Compute.A4d.check_sound Checks.Evaluated.a4d

theorem lemma_7_9 : Checks.lemma_7_9 :=
  Compute.A4m.check_sound Checks.Evaluated.a4m

theorem lemma_7_10 : Checks.lemma_7_10 :=
  Compute.LargeT.a5Check_sound Checks.Evaluated.a5

theorem lemma_7_11 : Checks.lemma_7_11 :=
  Compute.LargeT.d4Check_sound Checks.Evaluated.d4

theorem lemma_7_13 : Checks.lemma_7_13 :=
  Compute.SpikeLowerChecks.b2OK_sound Checks.Evaluated.b2

theorem lemma_7_17 : Checks.lemma_7_17 :=
  Compute.WindowChecks.d1AllOK_sound Checks.Evaluated.d1

theorem lemma_7_18 : Checks.lemma_7_18 :=
  Compute.WindowChecks.d1PrimeAllOK_sound Checks.Evaluated.d1Prime

theorem lemma_7_19 : Checks.lemma_7_19 :=
  Compute.WindowChecks.d2AllOK_sound Checks.Evaluated.d2

end Erdos993Lean.Analytic.V22.Checked
