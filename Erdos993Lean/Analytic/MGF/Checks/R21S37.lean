import Erdos993Lean.Analytic.MGF.Data.R21S37
import Erdos993Lean.Analytic.MGF.N21.Pieces

/-!
# The MGF + two-sided atlas, rung 21, strip 37: the check (`native_decide`)

The one `native_decide` of this module evaluates the checker `pieceOK` (`Erdos993Lean/Analytic/MGF/Checker.lean`) on the
boxes of this strip with the piece's caps and rows (`piece21`: the N44 caps, with lane O1R21's O1 row on pieces 24 and 27):
every box passes and the boxes cover
`[q(5/4), q(13/10)] × [161/26, 161/13]`.  What the check means is proved on standard axioms in
`Erdos993Lean/Analytic/MGF/Sound.lean` (`pieceOK_sound`).  This trusts the Lean compiler (`Lean.ofReduceBool`).
-/

namespace Erdos993Lean.Analytic.MGF.Checks

open Erdos993Lean.Analytic.MGF.Data

set_option profiler true
set_option profiler.threshold 500

/-- The strip R21S37: every box and the cover pass. -/
theorem checkR21S37 :
    pieceOK (N21.piece21 37) mloR21S37 (floor44 37) boxesR21S37 slabsR21S37 = true := by
  native_decide

end Erdos993Lean.Analytic.MGF.Checks
