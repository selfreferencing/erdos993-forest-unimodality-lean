import Erdos993Lean.Analytic.N45.Data.Params
import Erdos993Lean.Analytic.N45.Data.P38

/-!
# The n ≥ 45 strip atlas, piece 38 (band 27): the check (`native_decide`)

Activity `[7/4, 9/5]` (0-based parent band 26).  The one `native_decide` of this module
evaluates lane A9's checker `bandOK` (`Erdos993Lean/Analytic/Atlas/Checker.lean`) on the boxes of this strip
with the piece's caps and the box's own upper activity `lamBox b = qh/(1 − qh)` as tail base: every box passes
and the boxes cover `[q(7/4), q(9/5)] × [35/3, 232/19]`.  This trusts the Lean compiler
(`Lean.ofReduceBool`); what the check means is proved on standard axioms in
`Erdos993Lean/Analytic/Atlas/Sound.lean` (`band_explicitThreshold`).
-/

namespace Erdos993Lean.Analytic.N45.Checks

open Erdos993Lean.Analytic.Atlas Erdos993Lean.Analytic.N45.Data

set_option profiler true
set_option profiler.threshold 500

/-- The n ≥ 45 strip P38: every box and the cover pass. -/
theorem checkP38 :
    bandOK (piece45Band 38) lamBox (piece45Cap 38) boxesP38 slabsP38 = true := by
  native_decide

end Erdos993Lean.Analytic.N45.Checks
