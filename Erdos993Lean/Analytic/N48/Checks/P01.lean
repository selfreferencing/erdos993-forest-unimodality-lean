import Erdos993Lean.Analytic.N48.Data.Params
import Erdos993Lean.Analytic.N48.Data.P01

/-!
# The n ≥ 48 strip atlas, piece 01 (band 02): the check (`native_decide`)

Activity `[9/25, 2/5]` (0-based parent band 1).  The one `native_decide` of this module
evaluates lane A9's checker `bandOK` (`Erdos993Lean/Analytic/Atlas/Checker.lean`) on lane R4X's boxes of this
strip, with the box's own upper activity `lamBox b = qh/(1 − qh)` as tail base: every box passes and the boxes
cover `[q(9/25), q(2/5)] × [91/4, 49/2]`.  This trusts the Lean compiler
(`Lean.ofReduceBool`); what the check means is proved on standard axioms in
`Erdos993Lean/Analytic/Atlas/Sound.lean` (`band_explicitThreshold`).
-/

namespace Erdos993Lean.Analytic.N48.Checks

open Erdos993Lean.Analytic.Atlas Erdos993Lean.Analytic.N48.Data

set_option profiler true
set_option profiler.threshold 500

/-- The n ≥ 48 strip P01: every box and the cover pass. -/
theorem checkP01 :
    bandOK (piece48Band 1) lamBox (piece48Cap 1) boxesP01 slabsP01 = true := by
  native_decide

end Erdos993Lean.Analytic.N48.Checks
