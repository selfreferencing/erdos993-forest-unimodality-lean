import Erdos993Lean.Analytic.V21.Data.To50_51

/-! Paper v2.1 Lemma 5.4: exact MGF certificate and rectangle cover.
Source hashes and table comparisons are in CHECKS/V21/coverage_audit.json.
One new native_decide. Its standard meaning is existing MGF.pieceOK_sound. -/

namespace Erdos993Lean.Analytic.V21.Checks

open Erdos993Lean.Analytic.MGF Erdos993Lean.Analytic.V21.Data

set_option profiler true
set_option profiler.threshold 500

/-- Paper v2.1 Lemma 5.4, subinterval 51: all boxes and the cover pass. -/
theorem checkTo50_51 :
    pieceOK (pieceV21 51) mloTo50_51 mhiTo50_51 boxesTo50_51 slabsTo50_51 = true := by
  native_decide

end Erdos993Lean.Analytic.V21.Checks
