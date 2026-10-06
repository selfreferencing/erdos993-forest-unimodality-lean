import Erdos993Lean.Analytic.N44.Data.Params
import Erdos993Lean.Analytic.N44.Data.P10

/-!
# The n ≥ 44 strip atlas, piece 10 (band 10): the check (`native_decide`)

Activity `[39/50, 4/5]` (0-based parent band 9).  The one `native_decide` of this module
evaluates lane A9's checker `bandOK` (`Erdos993Lean/Analytic/Atlas/Checker.lean`) on the boxes of this strip
with the piece's caps and the box's own upper activity `lamBox b = qh/(1 − qh)` as tail base: every box passes
and the boxes cover `[q(39/50), q(4/5)] × [27/2, 117/8]`.  This trusts the Lean compiler
(`Lean.ofReduceBool`); what the check means is proved on standard axioms in
`Erdos993Lean/Analytic/Atlas/Sound.lean` (`band_explicitThreshold`).
-/

namespace Erdos993Lean.Analytic.N44.Checks

open Erdos993Lean.Analytic.Atlas Erdos993Lean.Analytic.N44.Data

set_option profiler true
set_option profiler.threshold 500

/-- The n ≥ 44 strip P10: every box and the cover pass. -/
theorem checkP10 :
    bandOK (piece44Band 10) lamBox (piece44Cap 10) boxesP10 slabsP10 = true := by
  native_decide

end Erdos993Lean.Analytic.N44.Checks
