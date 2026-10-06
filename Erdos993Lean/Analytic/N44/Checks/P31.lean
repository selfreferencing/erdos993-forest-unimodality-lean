import Erdos993Lean.Analytic.N44.Data.Params
import Erdos993Lean.Analytic.N44.Data.P31

/-!
# The n ≥ 44 strip atlas, piece 31 (band 19): the check (`native_decide`)

Activity `[28/25, 57/50]` (0-based parent band 18).  The one `native_decide` of this module
evaluates lane A9's checker `bandOK` (`Erdos993Lean/Analytic/Atlas/Checker.lean`) on the boxes of this strip
with the piece's caps and the box's own upper activity `lamBox b = qh/(1 − qh)` as tail base: every box passes
and the boxes cover `[q(28/25), q(57/50)] × [1391/114, 749/57]`.  This trusts the Lean compiler
(`Lean.ofReduceBool`); what the check means is proved on standard axioms in
`Erdos993Lean/Analytic/Atlas/Sound.lean` (`band_explicitThreshold`).
-/

namespace Erdos993Lean.Analytic.N44.Checks

open Erdos993Lean.Analytic.Atlas Erdos993Lean.Analytic.N44.Data

set_option profiler true
set_option profiler.threshold 500

/-- The n ≥ 44 strip P31: every box and the cover pass. -/
theorem checkP31 :
    bandOK (piece44Band 31) lamBox (piece44Cap 31) boxesP31 slabsP31 = true := by
  native_decide

end Erdos993Lean.Analytic.N44.Checks
