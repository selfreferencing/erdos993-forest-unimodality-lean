import Erdos993Lean.Analytic.N52.Data.Params
import Erdos993Lean.Analytic.N52.Data.S17

/-!
# The n ≥ 52 strip atlas, band 17: the check (`native_decide`)

Activity band `[26/25, 27/25]` (0-based band 16).  The one `native_decide` of this module evaluates
lane A9's checker `bandOK` (`Erdos993Lean/Analytic/Atlas/Checker.lean`) on lane R52's boxes of this band, with the
box's own upper activity `lamBox b = qh/(1 − qh)` as tail base: every box passes and the boxes cover
`[q(λ_16), q(λ_17)] × [130/9, 52/3]`.  This trusts the Lean compiler (`Lean.ofReduceBool`);
what the check means is proved on standard axioms in `Erdos993Lean/Analytic/Atlas/Sound.lean`
(`band_explicitThreshold`).
-/

namespace Erdos993Lean.Analytic.N52.Checks

open Erdos993Lean.Analytic.Atlas Erdos993Lean.Analytic.N52.Data

set_option profiler true
set_option profiler.threshold 500

/-- The n ≥ 52 strip, band 17: every box and the cover pass. -/
theorem checkS17 :
    bandOK (stripBand 16) lamBox (stripCap 16) boxesS17 slabsS17 = true := by
  native_decide

end Erdos993Lean.Analytic.N52.Checks
