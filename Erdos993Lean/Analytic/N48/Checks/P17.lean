import Erdos993Lean.Analytic.N48.Data.Params
import Erdos993Lean.Analytic.N48.Data.P17

/-!
# The n ≥ 48 strip atlas, piece 17 (band 18): the check (`native_decide`)

Activity `[27/25, 28/25]` (0-based parent band 17).  The one `native_decide` of this module
evaluates lane A9's checker `bandOK` (`Erdos993Lean/Analytic/Atlas/Checker.lean`) on lane R4X's boxes of this
strip, with the box's own upper activity `lamBox b = qh/(1 − qh)` as tail base: every box passes and the boxes
cover `[q(27/25), q(28/25)] × [53/4, 795/56]`.  This trusts the Lean compiler
(`Lean.ofReduceBool`); what the check means is proved on standard axioms in
`Erdos993Lean/Analytic/Atlas/Sound.lean` (`band_explicitThreshold`).
-/

namespace Erdos993Lean.Analytic.N48.Checks

open Erdos993Lean.Analytic.Atlas Erdos993Lean.Analytic.N48.Data

set_option profiler true
set_option profiler.threshold 500

/-- The n ≥ 48 strip P17: every box and the cover pass. -/
theorem checkP17 :
    bandOK (piece48Band 17) lamBox (piece48Cap 17) boxesP17 slabsP17 = true := by
  native_decide

end Erdos993Lean.Analytic.N48.Checks
