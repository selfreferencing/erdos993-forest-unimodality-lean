import Erdos993Lean.Analytic.N44.Data.Params
import Erdos993Lean.Analytic.N44.Data.P43

/-!
# The n ≥ 44 strip atlas, piece 43 (band 25): the check (`native_decide`)

Activity `[3/2, 8/5]` (0-based parent band 24).  The one `native_decide` of this module
evaluates lane A9's checker `bandOK` (`Erdos993Lean/Analytic/Atlas/Checker.lean`) on the boxes of this strip
with the piece's caps and the box's own upper activity `lamBox b = qh/(1 − qh)` as tail base: every box passes
and the boxes cover `[q(3/2), q(8/5)] × [91/8, 195/16]`.  This trusts the Lean compiler
(`Lean.ofReduceBool`); what the check means is proved on standard axioms in
`Erdos993Lean/Analytic/Atlas/Sound.lean` (`band_explicitThreshold`).
-/

namespace Erdos993Lean.Analytic.N44.Checks

open Erdos993Lean.Analytic.Atlas Erdos993Lean.Analytic.N44.Data

set_option profiler true
set_option profiler.threshold 500

/-- The n ≥ 44 strip P43: every box and the cover pass. -/
theorem checkP43 :
    bandOK (piece44Band 43) lamBox (piece44Cap 43) boxesP43 slabsP43 = true := by
  native_decide

end Erdos993Lean.Analytic.N44.Checks
