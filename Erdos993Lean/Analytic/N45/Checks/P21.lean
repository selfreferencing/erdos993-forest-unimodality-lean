import Erdos993Lean.Analytic.N45.Data.Params
import Erdos993Lean.Analytic.N45.Data.P21

/-!
# The n ≥ 45 strip atlas, piece 21 (band 18): the check (`native_decide`)

Activity `[11/10, 28/25]` (0-based parent band 17).  The one `native_decide` of this module
evaluates lane A9's checker `bandOK` (`Erdos993Lean/Analytic/Atlas/Checker.lean`) on the boxes of this strip
with the piece's caps and the box's own upper activity `lamBox b = qh/(1 − qh)` as tail base: every box passes
and the boxes cover `[q(11/10), q(28/25)] × [689/56, 53/4]`.  This trusts the Lean compiler
(`Lean.ofReduceBool`); what the check means is proved on standard axioms in
`Erdos993Lean/Analytic/Atlas/Sound.lean` (`band_explicitThreshold`).
-/

namespace Erdos993Lean.Analytic.N45.Checks

open Erdos993Lean.Analytic.Atlas Erdos993Lean.Analytic.N45.Data

set_option profiler true
set_option profiler.threshold 500

/-- The n ≥ 45 strip P21: every box and the cover pass. -/
theorem checkP21 :
    bandOK (piece45Band 21) lamBox (piece45Cap 21) boxesP21 slabsP21 = true := by
  native_decide

end Erdos993Lean.Analytic.N45.Checks
