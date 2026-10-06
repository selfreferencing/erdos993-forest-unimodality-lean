import Erdos993Lean.Analytic.MGF.Data.R21S31
import Erdos993Lean.Analytic.MGF.N21.Pieces

/-!
# The MGF + two-sided atlas, rung 21, strip 31: the check (`native_decide`)

The one `native_decide` of this module evaluates the checker `pieceOK` (`Erdos993Lean/Analytic/MGF/Checker.lean`) on the
boxes of this strip with the piece's caps and rows (`piece21`: the N44 caps, with lane O1R21's O1 row on pieces 24 and 27):
every box passes and the boxes cover
`[q(28/25), q(57/50)] × [749/114, 1391/114]`.  What the check means is proved on standard axioms in
`Erdos993Lean/Analytic/MGF/Sound.lean` (`pieceOK_sound`).  This trusts the Lean compiler (`Lean.ofReduceBool`).
-/

namespace Erdos993Lean.Analytic.MGF.Checks

open Erdos993Lean.Analytic.MGF.Data

set_option profiler true
set_option profiler.threshold 500

/-- The strip R21S31: every box and the cover pass. -/
theorem checkR21S31 :
    pieceOK (N21.piece21 31) mloR21S31 (floor44 31) boxesR21S31 slabsR21S31 = true := by
  native_decide

end Erdos993Lean.Analytic.MGF.Checks
