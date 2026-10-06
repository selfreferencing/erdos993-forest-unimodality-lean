import Erdos993Lean.Analytic.V22.Checks.EvaluatedGenerated
import Erdos993Lean.Analytic.V22.A2Sound
import Erdos993Lean.Analytic.V22.WingChecksSound
import Erdos993Lean.Analytic.V22.WindowCellChecksSound
import Erdos993Lean.Analytic.V22.RayChecksSound
import Erdos993Lean.Analytic.V22.RowsSound

/-! Exact consumers of generated finite certificates. Numerical declarations
and these wrappers remain subject to the lane's serial Lean verification.
The B3 wrapper is explicitly restricted to the source's nonwindow cells.
-/

namespace Erdos993Lean.Analytic.V22.Checked

theorem lemma_7_3 : Checks.lemma_7_3 :=
  A2Sound.check_sound Checks.Evaluated.a2

theorem lemma_7_15 : Checks.lemma_7_15 :=
  Compute.WingChecks.allOK_sound Checks.Evaluated.c1

theorem lemma_7_20 : Checks.lemma_7_20 :=
  Compute.WindowCellChecks.check_sound Checks.Evaluated.d3

theorem lemma_7_21 : Checks.lemma_7_21 :=
  RowsSound.check_sound Checks.Evaluated.rows

theorem lemma_7_14_nonwindow : Checks.lemma_7_14_nonwindow :=
  Compute.RayChecks.generatedNonwindowOK_sound Checks.Evaluated.b3Nonwindow

end Erdos993Lean.Analytic.V22.Checked
