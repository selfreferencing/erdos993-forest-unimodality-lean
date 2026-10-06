import Erdos993Lean.Analytic.V21.Data.To50_21

/-! Paper v2.1 Lemma 5.4: exact MGF certificate and rectangle cover.
Source hashes and table comparisons are in CHECKS/V21/coverage_audit.json.
One new native_decide. Its standard meaning is existing MGF.pieceOK_sound. -/

namespace Erdos993Lean.Analytic.V21.Checks

open Erdos993Lean.Analytic.MGF Erdos993Lean.Analytic.V21.Data

set_option profiler true
set_option profiler.threshold 500

/-- Paper v2.1 Lemma 5.4, subinterval 21: all boxes and the cover pass. -/
theorem checkTo50_21 :
    pieceOK (pieceV21 21) mloTo50_21 mhiTo50_21 boxesTo50_21 slabsTo50_21 = true := by
  native_decide

end Erdos993Lean.Analytic.V21.Checks
