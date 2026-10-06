import Erdos993Lean.Analytic.N48.Data.Params
import Erdos993Lean.Analytic.N48.Data.P29

/-!
# The n ≥ 48 strip atlas, piece 29 (band 27): the check (`native_decide`)

Activity `[7/4, 19/10]` (0-based parent band 26).  The one `native_decide` of this module
evaluates lane A9's checker `bandOK` (`Erdos993Lean/Analytic/Atlas/Checker.lean`) on lane R4X's boxes of this
strip, with the box's own upper activity `lamBox b = qh/(1 − qh)` as tail base: every box passes and the boxes
cover `[q(7/4), q(19/10)] × [232/19, 493/38]`.  This trusts the Lean compiler
(`Lean.ofReduceBool`); what the check means is proved on standard axioms in
`Erdos993Lean/Analytic/Atlas/Sound.lean` (`band_explicitThreshold`).
-/

namespace Erdos993Lean.Analytic.N48.Checks

open Erdos993Lean.Analytic.Atlas Erdos993Lean.Analytic.N48.Data

set_option profiler true
set_option profiler.threshold 500

/-- The n ≥ 48 strip P29: every box and the cover pass. -/
theorem checkP29 :
    bandOK (piece48Band 29) lamBox (piece48Cap 29) boxesP29 slabsP29 = true := by
  native_decide

end Erdos993Lean.Analytic.N48.Checks
