import Erdos993Lean.Analytic.V21.Data.To50_46

/-! Paper v2.1 Lemma 5.4: exact MGF certificate and rectangle cover.
Source hashes and table comparisons are in CHECKS/V21/coverage_audit.json.
One new native_decide. Its standard meaning is existing MGF.pieceOK_sound. -/

namespace Erdos993Lean.Analytic.V21.Checks

open Erdos993Lean.Analytic.MGF Erdos993Lean.Analytic.V21.Data

set_option profiler true
set_option profiler.threshold 500

/-- Paper v2.1 Lemma 5.4, subinterval 46: all boxes and the cover pass. -/
theorem checkTo50_46 :
    pieceOK (pieceV21 46) mloTo50_46 mhiTo50_46 boxesTo50_46 slabsTo50_46 = true := by
  native_decide

end Erdos993Lean.Analytic.V21.Checks
