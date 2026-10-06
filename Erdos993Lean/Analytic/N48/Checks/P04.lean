import Erdos993Lean.Analytic.N48.Data.Params
import Erdos993Lean.Analytic.N48.Data.P04

/-!
# The n ≥ 48 strip atlas, piece 04 (band 05): the check (`native_decide`)

Activity `[1/2, 11/20]` (0-based parent band 4).  The one `native_decide` of this module
evaluates lane A9's checker `bandOK` (`Erdos993Lean/Analytic/Atlas/Checker.lean`) on lane R4X's boxes of this
strip, with the box's own upper activity `lamBox b = qh/(1 − qh)` as tail base: every box passes and the boxes
cover `[q(1/2), q(11/20)] × [403/22, 217/11]`.  This trusts the Lean compiler
(`Lean.ofReduceBool`); what the check means is proved on standard axioms in
`Erdos993Lean/Analytic/Atlas/Sound.lean` (`band_explicitThreshold`).
-/

namespace Erdos993Lean.Analytic.N48.Checks

open Erdos993Lean.Analytic.Atlas Erdos993Lean.Analytic.N48.Data

set_option profiler true
set_option profiler.threshold 500

/-- The n ≥ 48 strip P04: every box and the cover pass. -/
theorem checkP04 :
    bandOK (piece48Band 4) lamBox (piece48Cap 4) boxesP04 slabsP04 = true := by
  native_decide

end Erdos993Lean.Analytic.N48.Checks
