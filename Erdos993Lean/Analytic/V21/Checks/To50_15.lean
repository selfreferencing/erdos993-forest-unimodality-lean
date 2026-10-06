import Erdos993Lean.Analytic.V21.Data.To50_15

/-! Paper v2.1 Lemma 5.4: exact MGF certificate and rectangle cover.
Source hashes and table comparisons are in CHECKS/V21/coverage_audit.json.
One new native_decide. Its standard meaning is existing MGF.pieceOK_sound. -/

namespace Erdos993Lean.Analytic.V21.Checks

open Erdos993Lean.Analytic.MGF Erdos993Lean.Analytic.V21.Data

set_option profiler true
set_option profiler.threshold 500

/-- Paper v2.1 Lemma 5.4, subinterval 15: all boxes and the cover pass. -/
theorem checkTo50_15 :
    pieceOK (pieceV21 15) mloTo50_15 mhiTo50_15 boxesTo50_15 slabsTo50_15 = true := by
  native_decide

end Erdos993Lean.Analytic.V21.Checks
