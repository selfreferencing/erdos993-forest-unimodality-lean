import Erdos993Lean.Analytic.V21.Data.To50_17

/-! Paper v2.1 Lemma 5.4: exact MGF certificate and rectangle cover.
Source hashes and table comparisons are in CHECKS/V21/coverage_audit.json.
One new native_decide. Its standard meaning is existing MGF.pieceOK_sound. -/

namespace Erdos993Lean.Analytic.V21.Checks

open Erdos993Lean.Analytic.MGF Erdos993Lean.Analytic.V21.Data

set_option profiler true
set_option profiler.threshold 500

/-- Paper v2.1 Lemma 5.4, subinterval 17: all boxes and the cover pass. -/
theorem checkTo50_17 :
    pieceOK (pieceV21 17) mloTo50_17 mhiTo50_17 boxesTo50_17 slabsTo50_17 = true := by
  native_decide

end Erdos993Lean.Analytic.V21.Checks
