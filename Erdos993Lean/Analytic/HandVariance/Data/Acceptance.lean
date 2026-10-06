import Erdos993Lean.Analytic.HandVariance.Data.Mid
import Erdos993Lean.Analytic.HandVariance.Data.Lo
import Erdos993Lean.Analytic.HandVariance.Data.U1
import Erdos993Lean.Analytic.HandVariance.Data.U2
import Erdos993Lean.Analytic.HandVariance.Data.U3
import Erdos993Lean.Analytic.HandVariance.Data.U4
import Erdos993Lean.Analytic.HandVariance.Data.MidPolygons
import Erdos993Lean.Analytic.HandVariance.Data.OtherPolygons
import Erdos993Lean.Analytic.HandVariance.Data.Base
import Erdos993Lean.Analytic.HandVariance.Compute.Checks

/-!
# Native acceptance of the Appendix N.4 rational recipes

Source: TWIN v1.8 Appendix N.4, families chk:tgt and chk:mc, final
referee-corrected exact recipes. These theorems assert Boolean calculation
acceptance only. They do not assert interval soundness or covering.

Trust: nine uses of native_decide, named individually below. The compiler
axioms Lean.ofReduceBool and Lean.trustCompiler are present in their axiom audit. All functions
are structural and retain every arithmetic safety guard.
-/

namespace Erdos993Lean.Analytic.HandVariance.Data
open Compute
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Source: Appendix N.4 exact mid recipes, computed with retained guards. -/
theorem mid_accepted : midActivities.all activityOK = true := by native_decide

/-- Source: Appendix N.4 exact lo recipes, computed with retained guards. -/
theorem lo_accepted : loActivities.all activityOK = true := by native_decide

/-- Source: Appendix N.4 exact u1 recipes, computed with retained guards. -/
theorem u1_accepted : u1Activities.all activityOK = true := by native_decide

/-- Source: Appendix N.4 exact u2 recipes, computed with retained guards. -/
theorem u2_accepted : u2Activities.all activityOK = true := by native_decide

/-- Source: Appendix N.4 exact u3 recipes, computed with retained guards. -/
theorem u3_accepted : u3Activities.all activityOK = true := by native_decide

/-- Source: Appendix N.4 exact u4 recipes, computed with retained guards. -/
theorem u4_accepted : u4Activities.all activityOK = true := by native_decide

/-- Source: Appendix N.4 exact midPolygon recipes, computed with retained guards. -/
theorem midPolygon_accepted : midPolygons.all polygonOK = true := by native_decide

/-- Source: Appendix N.4 exact otherPolygon recipes, computed with retained guards. -/
theorem otherPolygon_accepted : otherPolygons.all polygonOK = true := by native_decide

/-- Source: mc:lem:base and tgt:thm, all 13 selected-leaf recipes. -/
theorem base_accepted : baseChecks.all (fun b => optionPositive (baseLower b)) = true := by
  native_decide

end Erdos993Lean.Analytic.HandVariance.Data

#print axioms Erdos993Lean.Analytic.HandVariance.Data.mid_accepted

#print axioms Erdos993Lean.Analytic.HandVariance.Data.lo_accepted

#print axioms Erdos993Lean.Analytic.HandVariance.Data.u1_accepted

#print axioms Erdos993Lean.Analytic.HandVariance.Data.u2_accepted

#print axioms Erdos993Lean.Analytic.HandVariance.Data.u3_accepted

#print axioms Erdos993Lean.Analytic.HandVariance.Data.u4_accepted

#print axioms Erdos993Lean.Analytic.HandVariance.Data.midPolygon_accepted

#print axioms Erdos993Lean.Analytic.HandVariance.Data.otherPolygon_accepted

#print axioms Erdos993Lean.Analytic.HandVariance.Data.base_accepted
