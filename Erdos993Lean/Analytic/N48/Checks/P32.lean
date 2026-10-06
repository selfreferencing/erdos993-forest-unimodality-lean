import Erdos993Lean.Analytic.N48.Data.Params
import Erdos993Lean.Analytic.N48.Data.P32

/-!
# The n ≥ 48 strip atlas, piece 32 (band 30): the check (`native_decide`)

Activity `[9/4, 7/3]` (0-based parent band 29).  The one `native_decide` of this module
evaluates lane A9's checker `bandOK` (`Erdos993Lean/Analytic/Atlas/Checker.lean`) on lane R4X's boxes of this
strip, with the box's own upper activity `lamBox b = qh/(1 − qh)` as tail base: every box passes and the boxes
cover `[q(9/4), q(7/3)] × [85/7, 90/7]`.  This trusts the Lean compiler
(`Lean.ofReduceBool`); what the check means is proved on standard axioms in
`Erdos993Lean/Analytic/Atlas/Sound.lean` (`band_explicitThreshold`).
-/

namespace Erdos993Lean.Analytic.N48.Checks

open Erdos993Lean.Analytic.Atlas Erdos993Lean.Analytic.N48.Data

set_option profiler true
set_option profiler.threshold 500

/-- The n ≥ 48 strip P32: every box and the cover pass. -/
theorem checkP32 :
    bandOK (piece48Band 32) lamBox (piece48Cap 32) boxesP32 slabsP32 = true := by
  native_decide

end Erdos993Lean.Analytic.N48.Checks
