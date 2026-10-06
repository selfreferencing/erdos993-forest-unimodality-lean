import Erdos993Lean.Analytic.N48.Data.Params
import Erdos993Lean.Analytic.N48.Data.P18

/-!
# The n ≥ 48 strip atlas, piece 18 (band 19): the check (`native_decide`)

Activity `[28/25, 29/25]` (0-based parent band 18).  The one `native_decide` of this module
evaluates lane A9's checker `bandOK` (`Erdos993Lean/Analytic/Atlas/Checker.lean`) on lane R4X's boxes of this
strip, with the box's own upper activity `lamBox b = qh/(1 − qh)` as tail base: every box passes and the boxes
cover `[q(28/25), q(29/25)] × [378/29, 432/29]`.  This trusts the Lean compiler
(`Lean.ofReduceBool`); what the check means is proved on standard axioms in
`Erdos993Lean/Analytic/Atlas/Sound.lean` (`band_explicitThreshold`).
-/

namespace Erdos993Lean.Analytic.N48.Checks

open Erdos993Lean.Analytic.Atlas Erdos993Lean.Analytic.N48.Data

set_option profiler true
set_option profiler.threshold 500

/-- The n ≥ 48 strip P18: every box and the cover pass. -/
theorem checkP18 :
    bandOK (piece48Band 18) lamBox (piece48Cap 18) boxesP18 slabsP18 = true := by
  native_decide

end Erdos993Lean.Analytic.N48.Checks
