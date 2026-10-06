import Erdos993Lean.Analytic.N45.Data.Params
import Erdos993Lean.Analytic.N45.Data.P41

/-!
# The n ≥ 45 strip atlas, piece 41 (band 28): the check (`native_decide`)

Activity `[19/10, 39/20]` (0-based parent band 27).  The one `native_decide` of this module
evaluates lane A9's checker `bandOK` (`Erdos993Lean/Analytic/Atlas/Checker.lean`) on the boxes of this strip
with the piece's caps and the box's own upper activity `lamBox b = qh/(1 − qh)` as tail base: every box passes
and the boxes cover `[q(19/10), q(39/20)] × [295/26, 488/41]`.  This trusts the Lean compiler
(`Lean.ofReduceBool`); what the check means is proved on standard axioms in
`Erdos993Lean/Analytic/Atlas/Sound.lean` (`band_explicitThreshold`).
-/

namespace Erdos993Lean.Analytic.N45.Checks

open Erdos993Lean.Analytic.Atlas Erdos993Lean.Analytic.N45.Data

set_option profiler true
set_option profiler.threshold 500

/-- The n ≥ 45 strip P41: every box and the cover pass. -/
theorem checkP41 :
    bandOK (piece45Band 41) lamBox (piece45Cap 41) boxesP41 slabsP41 = true := by
  native_decide

end Erdos993Lean.Analytic.N45.Checks
