import Erdos993Lean.Analytic.V21.Data.To50_04

/-! Paper v2.1 Lemma 5.4: exact MGF certificate and rectangle cover.
Source hashes and table comparisons are in CHECKS/V21/coverage_audit.json.
One new native_decide. Its standard meaning is existing MGF.pieceOK_sound. -/

namespace Erdos993Lean.Analytic.V21.Checks

open Erdos993Lean.Analytic.MGF Erdos993Lean.Analytic.V21.Data

set_option profiler true
set_option profiler.threshold 500

/-- Paper v2.1 Lemma 5.4, subinterval 4: all boxes and the cover pass. -/
theorem checkTo50_04 :
    pieceOK (pieceV21 4) mloTo50_04 mhiTo50_04 boxesTo50_04 slabsTo50_04 = true := by
  native_decide

end Erdos993Lean.Analytic.V21.Checks
