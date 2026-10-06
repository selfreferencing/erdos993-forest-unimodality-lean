import Erdos993Lean.Analytic.MGF.Act1.Data.R25S24

/-!
# Lane B L4a: R25S24 exact certificate and cover check

Source: LEAN/certfree/act1_test/REPORT.md and LEAN/certfree/referee_act1_test/REFEREE.md;
data source and exact source hashes are recorded in the imported module.
Checks q ∈ [1/2, 103/203], mean ∈ [812/103, 2639/206] at θ = 3/5, D = 6/5,
with the N44 activity/rate tables. Existing MGF.pieceOK checks all parameters, box
sanity, tails, fibres, margins and cover. One new native_decide; the compiler trust
must be listed in the final axiom audit.
-/

namespace Erdos993Lean.Analytic.MGF.Act1.Checks

open Erdos993Lean.Analytic.MGF.Act1.Data

set_option profiler true
set_option profiler.threshold 500

/-- Source: certfree/act1_test/REPORT.md; R25S24 at D = 6/5, exact boxes and rectangle. -/
theorem checkR25S24 :
    pieceOK (pieceD65 24) mloR25S24 mhiR25S24 boxesR25S24 slabsR25S24 = true := by
  native_decide

end Erdos993Lean.Analytic.MGF.Act1.Checks
