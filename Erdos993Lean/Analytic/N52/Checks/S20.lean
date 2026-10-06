import Erdos993Lean.Analytic.N52.Data.Params
import Erdos993Lean.Analytic.N52.Data.S20

/-!
# The n ≥ 52 strip atlas, band 20: the check (`native_decide`)

Activity band `[29/25, 6/5]` (0-based band 19).  The one `native_decide` of this module evaluates
lane A9's checker `bandOK` (`Erdos993Lean/Analytic/Atlas/Checker.lean`) on lane R52's boxes of this band, with the
box's own upper activity `lamBox b = qh/(1 − qh)` as tail base: every box passes and the boxes cover
`[q(λ_19), q(λ_20)] × [44/3, 33/2]`.  This trusts the Lean compiler (`Lean.ofReduceBool`);
what the check means is proved on standard axioms in `Erdos993Lean/Analytic/Atlas/Sound.lean`
(`band_explicitThreshold`).
-/

namespace Erdos993Lean.Analytic.N52.Checks

open Erdos993Lean.Analytic.Atlas Erdos993Lean.Analytic.N52.Data

set_option profiler true
set_option profiler.threshold 500

/-- The n ≥ 52 strip, band 20: every box and the cover pass. -/
theorem checkS20 :
    bandOK (stripBand 19) lamBox (stripCap 19) boxesS20 slabsS20 = true := by
  native_decide

end Erdos993Lean.Analytic.N52.Checks
