import Erdos993Lean.Analytic.N44.Data.Params
import Erdos993Lean.Analytic.N44.Data.P33

/-!
# The n ≥ 44 strip atlas, piece 33 (band 20): the check (`native_decide`)

Activity `[29/25, 59/50]` (0-based parent band 19).  The one `native_decide` of this module
evaluates lane A9's checker `bandOK` (`Erdos993Lean/Analytic/Atlas/Checker.lean`) on the boxes of this strip
with the piece's caps and the box's own upper activity `lamBox b = qh/(1 − qh)` as tail base: every box passes
and the boxes cover `[q(29/25), q(59/50)] × [1417/118, 763/59]`.  This trusts the Lean compiler
(`Lean.ofReduceBool`); what the check means is proved on standard axioms in
`Erdos993Lean/Analytic/Atlas/Sound.lean` (`band_explicitThreshold`).
-/

namespace Erdos993Lean.Analytic.N44.Checks

open Erdos993Lean.Analytic.Atlas Erdos993Lean.Analytic.N44.Data

set_option profiler true
set_option profiler.threshold 500

/-- The n ≥ 44 strip P33: every box and the cover pass. -/
theorem checkP33 :
    bandOK (piece44Band 33) lamBox (piece44Cap 33) boxesP33 slabsP33 = true := by
  native_decide

end Erdos993Lean.Analytic.N44.Checks
