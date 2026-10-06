import Erdos993Lean.Analytic.MGF.Data.R21S22
import Erdos993Lean.Analytic.MGF.N21.Pieces

/-!
# The MGF + two-sided atlas, rung 21, strip 22: the check (`native_decide`)

The one `native_decide` of this module evaluates the checker `pieceOK` (`Erdos993Lean/Analytic/MGF/Checker.lean`) on the
boxes of this strip with the piece's caps and rows (`piece21`: the N44 caps, with lane O1R21's O1 row on pieces 24 and 27):
every box passes and the boxes cover
`[q(97/100), q(99/100)] × [1393/198, 2587/198]`.  What the check means is proved on standard axioms in
`Erdos993Lean/Analytic/MGF/Sound.lean` (`pieceOK_sound`).  This trusts the Lean compiler (`Lean.ofReduceBool`).
-/

namespace Erdos993Lean.Analytic.MGF.Checks

open Erdos993Lean.Analytic.MGF.Data

set_option profiler true
set_option profiler.threshold 500

/-- The strip R21S22: every box and the cover pass. -/
theorem checkR21S22 :
    pieceOK (N21.piece21 22) mloR21S22 (floor44 22) boxesR21S22 slabsR21S22 = true := by
  native_decide

end Erdos993Lean.Analytic.MGF.Checks
