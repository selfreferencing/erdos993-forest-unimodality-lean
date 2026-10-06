import Erdos993Lean.Analytic.HandVariance.Data.Mid
import Erdos993Lean.Analytic.HandVariance.Data.Lo
import Erdos993Lean.Analytic.HandVariance.Data.U1
import Erdos993Lean.Analytic.HandVariance.Data.U2
import Erdos993Lean.Analytic.HandVariance.Data.U3
import Erdos993Lean.Analytic.HandVariance.Data.U4
import Erdos993Lean.Analytic.HandVariance.Data.MidPolygons
import Erdos993Lean.Analytic.HandVariance.Data.OtherPolygons
import Erdos993Lean.Analytic.HandVariance.Data.Base
import Erdos993Lean.Analytic.HandVariance.Compute.Coverage

/-!
# Native acceptance of the retained Appendix N.4 coverage data

These nine finite calculations assert coverage and geometric guard acceptance,
separately from Data.Acceptance's nine numerical calculations. Their ordinary
soundness is in HandVariance.CoverageSound (namespace Compute). Every source vertex, every spatial cut,
the cap line, every child Taylor partition and the terminal infinity tag are
retained. Trust: nine named `native_decide` calls; their audit must include
`Lean.ofReduceBool` and `Lean.trustCompiler`. No floating-point lower bound is imported as a fact.
-/

namespace Erdos993Lean.Analytic.HandVariance.Data
open Compute
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def allPolygons : List Polygon := midPolygons ++ otherPolygons

/-- Source: TWIN v1.8 Appendix N.4, `tgt:lem:child`, `tgt:lem:poly`, Table `tgt:tab:poly`;
exact closed coverage and retained guards for the midPolygon family. -/
theorem midPolygon_coverage : midPolygons.all polygonCoverageCheck = true := by native_decide

/-- Source: TWIN v1.8 Appendix N.4, `tgt:lem:child`, `tgt:lem:poly`, Table `mc:tab:poly`;
exact closed coverage and retained guards for the otherPolygon family. -/
theorem otherPolygon_coverage : otherPolygons.all polygonCoverageCheck = true := by native_decide

/-- Source: TWIN v1.8 Appendix N.4, `mc:thm:step`, Table `mc:tab:sub`;
exact closed coverage and retained guards for the lo family. -/
theorem lo_coverage : segmentActivityCoverageCheck 0 loActivities allPolygons = true := by native_decide

/-- Source: TWIN v1.8 Appendix N.4, `tgt:thm`, Table `tgt:tab:sub`;
exact closed coverage and retained guards for the mid family. -/
theorem mid_coverage : segmentActivityCoverageCheck 1 midActivities allPolygons = true := by native_decide

/-- Source: TWIN v1.8 Appendix N.4, `mc:thm:step`, Table `mc:tab:sub`;
exact closed coverage and retained guards for the u1 family. -/
theorem u1_coverage : segmentActivityCoverageCheck 2 u1Activities allPolygons = true := by native_decide

/-- Source: TWIN v1.8 Appendix N.4, `mc:thm:step`, Table `mc:tab:sub`;
exact closed coverage and retained guards for the u2 family. -/
theorem u2_coverage : segmentActivityCoverageCheck 3 u2Activities allPolygons = true := by native_decide

/-- Source: TWIN v1.8 Appendix N.4, `mc:thm:step`, Table `mc:tab:sub`;
exact closed coverage and retained guards for the u3 family. -/
theorem u3_coverage : segmentActivityCoverageCheck 4 u3Activities allPolygons = true := by native_decide

/-- Source: TWIN v1.8 Appendix N.4, `mc:thm:step`, Table `mc:tab:sub`;
exact closed coverage and retained guards for the u4 family. -/
theorem u4_coverage : segmentActivityCoverageCheck 5 u4Activities allPolygons = true := by native_decide

/-- Source: TWIN v1.8 Appendix N.4, `mc:eq:base`, `mc:lem:base`, and the base part of `tgt:thm`;
exact closed coverage and retained guards for the base family. -/
theorem base_coverage : (List.range 6).all (fun segment =>
    baseCoverageCheck segment (baseChecks.filter (fun b => decide (b.segment = segment)))) = true := by
  native_decide

end Erdos993Lean.Analytic.HandVariance.Data

#print axioms Erdos993Lean.Analytic.HandVariance.Data.midPolygon_coverage
#print axioms Erdos993Lean.Analytic.HandVariance.Data.otherPolygon_coverage
#print axioms Erdos993Lean.Analytic.HandVariance.Data.lo_coverage
#print axioms Erdos993Lean.Analytic.HandVariance.Data.mid_coverage
#print axioms Erdos993Lean.Analytic.HandVariance.Data.u1_coverage
#print axioms Erdos993Lean.Analytic.HandVariance.Data.u2_coverage
#print axioms Erdos993Lean.Analytic.HandVariance.Data.u3_coverage
#print axioms Erdos993Lean.Analytic.HandVariance.Data.u4_coverage
#print axioms Erdos993Lean.Analytic.HandVariance.Data.base_coverage
