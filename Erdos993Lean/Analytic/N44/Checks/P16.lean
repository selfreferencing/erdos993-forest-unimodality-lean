import Erdos993Lean.Analytic.N44.Data.Params
import Erdos993Lean.Analytic.N44.Data.P16

/-!
# The n ≥ 44 strip atlas, piece 16 (band 13): the check (`native_decide`)

Activity `[89/100, 91/100]` (0-based parent band 12).  The one `native_decide` of this module
evaluates lane A9's checker `bandOK` (`Erdos993Lean/Analytic/Atlas/Checker.lean`) on the boxes of this strip
with the piece's caps and the box's own upper activity `lamBox b = qh/(1 − qh)` as tail base: every box passes
and the boxes cover `[q(89/100), q(91/100)] × [1146/91, 312/23]`.  This trusts the Lean compiler
(`Lean.ofReduceBool`); what the check means is proved on standard axioms in
`Erdos993Lean/Analytic/Atlas/Sound.lean` (`band_explicitThreshold`).
-/

namespace Erdos993Lean.Analytic.N44.Checks

open Erdos993Lean.Analytic.Atlas Erdos993Lean.Analytic.N44.Data

set_option profiler true
set_option profiler.threshold 500

/-- The n ≥ 44 strip P16: every box and the cover pass. -/
theorem checkP16 :
    bandOK (piece44Band 16) lamBox (piece44Cap 16) boxesP16 slabsP16 = true := by
  native_decide

end Erdos993Lean.Analytic.N44.Checks
