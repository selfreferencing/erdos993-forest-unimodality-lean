import Erdos993Lean.Analytic.MGF.Data.R21S30
import Erdos993Lean.Analytic.MGF.N21.Pieces

/-!
# The MGF + two-sided atlas, rung 21, strip 30: the check (`native_decide`)

The one `native_decide` of this module evaluates the checker `pieceOK` (`Erdos993Lean/Analytic/MGF/Checker.lean`) on the
boxes of this strip with the piece's caps and rows (`piece21`: the N44 caps, with lane O1R21's O1 row on pieces 24 and 27):
every box passes and the boxes cover
`[q(11/10), q(28/25)] × [53/8, 689/56]`.  What the check means is proved on standard axioms in
`Erdos993Lean/Analytic/MGF/Sound.lean` (`pieceOK_sound`).  This trusts the Lean compiler (`Lean.ofReduceBool`).
-/

namespace Erdos993Lean.Analytic.MGF.Checks

open Erdos993Lean.Analytic.MGF.Data

set_option profiler true
set_option profiler.threshold 500

/-- The strip R21S30: every box and the cover pass. -/
theorem checkR21S30 :
    pieceOK (N21.piece21 30) mloR21S30 (floor44 30) boxesR21S30 slabsR21S30 = true := by
  native_decide

end Erdos993Lean.Analytic.MGF.Checks
