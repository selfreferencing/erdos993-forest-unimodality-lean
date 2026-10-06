import Erdos993Lean.Analytic.N52.Data.Params
import Erdos993Lean.Analytic.N52.Data.S15

/-!
# The n ≥ 52 strip atlas, band 15: the check (`native_decide`)

Activity band `[24/25, 1]` (0-based band 14).  The one `native_decide` of this module evaluates
lane A9's checker `bandOK` (`Erdos993Lean/Analytic/Atlas/Checker.lean`) on lane R52's boxes of this band, with the
box's own upper activity `lamBox b = qh/(1 − qh)` as tail base: every box passes and the boxes cover
`[q(λ_14), q(λ_15)] × [14, 17]`.  This trusts the Lean compiler (`Lean.ofReduceBool`);
what the check means is proved on standard axioms in `Erdos993Lean/Analytic/Atlas/Sound.lean`
(`band_explicitThreshold`).
-/

namespace Erdos993Lean.Analytic.N52.Checks

open Erdos993Lean.Analytic.Atlas Erdos993Lean.Analytic.N52.Data

set_option profiler true
set_option profiler.threshold 500

/-- The n ≥ 52 strip, band 15: every box and the cover pass. -/
theorem checkS15 :
    bandOK (stripBand 14) lamBox (stripCap 14) boxesS15 slabsS15 = true := by
  native_decide

end Erdos993Lean.Analytic.N52.Checks
