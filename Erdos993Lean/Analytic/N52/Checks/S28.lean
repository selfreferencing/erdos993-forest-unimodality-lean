import Erdos993Lean.Analytic.N52.Data.Params
import Erdos993Lean.Analytic.N52.Data.S28

/-!
# The n ≥ 52 strip atlas, band 28: the check (`native_decide`)

Activity band `[19/10, 41/20]` (0-based band 27).  The one `native_decide` of this module evaluates
lane A9's checker `bandOK` (`Erdos993Lean/Analytic/Atlas/Checker.lean`) on lane R52's boxes of this band, with the
box's own upper activity `lamBox b = qh/(1 − qh)` as tail base: every box passes and the boxes cover
`[q(λ_27), q(λ_28)] × [1037/82, 610/41]`.  This trusts the Lean compiler (`Lean.ofReduceBool`);
what the check means is proved on standard axioms in `Erdos993Lean/Analytic/Atlas/Sound.lean`
(`band_explicitThreshold`).
-/

namespace Erdos993Lean.Analytic.N52.Checks

open Erdos993Lean.Analytic.Atlas Erdos993Lean.Analytic.N52.Data

set_option profiler true
set_option profiler.threshold 500

/-- The n ≥ 52 strip, band 28: every box and the cover pass. -/
theorem checkS28 :
    bandOK (stripBand 27) lamBox (stripCap 27) boxesS28 slabsS28 = true := by
  native_decide

end Erdos993Lean.Analytic.N52.Checks
