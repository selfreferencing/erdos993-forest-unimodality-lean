import Erdos993Lean.Analytic.N45.Data.Params
import Erdos993Lean.Analytic.N45.Data.P30

/-!
# The n ≥ 45 strip atlas, piece 30 (band 23): the check (`native_decide`)

Activity `[27/20, 7/5]` (0-based parent band 22).  The one `native_decide` of this module
evaluates lane A9's checker `bandOK` (`Erdos993Lean/Analytic/Atlas/Checker.lean`) on the boxes of this strip
with the piece's caps and the box's own upper activity `lamBox b = qh/(1 − qh)` as tail base: every box passes
and the boxes cover `[q(27/20), q(7/5)] × [12, 90/7]`.  This trusts the Lean compiler
(`Lean.ofReduceBool`); what the check means is proved on standard axioms in
`Erdos993Lean/Analytic/Atlas/Sound.lean` (`band_explicitThreshold`).
-/

namespace Erdos993Lean.Analytic.N45.Checks

open Erdos993Lean.Analytic.Atlas Erdos993Lean.Analytic.N45.Data

set_option profiler true
set_option profiler.threshold 500

/-- The n ≥ 45 strip P30: every box and the cover pass. -/
theorem checkP30 :
    bandOK (piece45Band 30) lamBox (piece45Cap 30) boxesP30 slabsP30 = true := by
  native_decide

end Erdos993Lean.Analytic.N45.Checks
