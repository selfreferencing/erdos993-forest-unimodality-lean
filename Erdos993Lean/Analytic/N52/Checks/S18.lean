import Erdos993Lean.Analytic.N52.Data.Params
import Erdos993Lean.Analytic.N52.Data.S18

/-!
# The n ≥ 52 strip atlas, band 18: the check (`native_decide`)

Activity band `[27/25, 28/25]` (0-based band 17).  The one `native_decide` of this module evaluates
lane A9's checker `bandOK` (`Erdos993Lean/Analytic/Atlas/Checker.lean`) on lane R52's boxes of this band, with the
box's own upper activity `lamBox b = qh/(1 − qh)` as tail base: every box passes and the boxes cover
`[q(λ_17), q(λ_18)] × [795/56, 477/28]`.  This trusts the Lean compiler (`Lean.ofReduceBool`);
what the check means is proved on standard axioms in `Erdos993Lean/Analytic/Atlas/Sound.lean`
(`band_explicitThreshold`).
-/

namespace Erdos993Lean.Analytic.N52.Checks

open Erdos993Lean.Analytic.Atlas Erdos993Lean.Analytic.N52.Data

set_option profiler true
set_option profiler.threshold 500

/-- The n ≥ 52 strip, band 18: every box and the cover pass. -/
theorem checkS18 :
    bandOK (stripBand 17) lamBox (stripCap 17) boxesS18 slabsS18 = true := by
  native_decide

end Erdos993Lean.Analytic.N52.Checks
