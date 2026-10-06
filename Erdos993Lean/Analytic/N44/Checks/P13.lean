import Erdos993Lean.Analytic.N44.Data.Params
import Erdos993Lean.Analytic.N44.Data.P13

/-!
# The n ≥ 44 strip atlas, piece 13 (band 12): the check (`native_decide`)

Activity `[43/50, 87/100]` (0-based parent band 11).  The one `native_decide` of this module
evaluates lane A9's checker `bandOK` (`Erdos993Lean/Analytic/Atlas/Checker.lean`) on the boxes of this strip
with the piece's caps and the box's own upper activity `lamBox b = qh/(1 − qh)` as tail base: every box passes
and the boxes cover `[q(43/50), q(87/100)] × [374/29, 611/44]`.  This trusts the Lean compiler
(`Lean.ofReduceBool`); what the check means is proved on standard axioms in
`Erdos993Lean/Analytic/Atlas/Sound.lean` (`band_explicitThreshold`).
-/

namespace Erdos993Lean.Analytic.N44.Checks

open Erdos993Lean.Analytic.Atlas Erdos993Lean.Analytic.N44.Data

set_option profiler true
set_option profiler.threshold 500

/-- The n ≥ 44 strip P13: every box and the cover pass. -/
theorem checkP13 :
    bandOK (piece44Band 13) lamBox (piece44Cap 13) boxesP13 slabsP13 = true := by
  native_decide

end Erdos993Lean.Analytic.N44.Checks
