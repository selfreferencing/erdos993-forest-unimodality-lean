import Erdos993Lean.Analytic.HandVariance.BandSound
import Erdos993Lean.Analytic.HandVariance.Data.Acceptance
import Erdos993Lean.Analytic.HandVariance.Data.CoverageAcceptance
import Erdos993Lean.Analytic.Reserve.Assembly
import Erdos993Lean.Analytic.Reserve.Entropy

/-!
# Actual hand recipes supply the six reserve certificates

Source: TWIN v1.8 Appendix N.4, `tgt:thm` and `mc:thm:var`.
The numerical and coverage acceptance theorems are consumed through ordinary
soundness proofs. Every band keeps its exact source activities, polygons,
spatial cuts and leaf rows. The reserve induction applies to the actual forest.

Trust: the imported acceptance modules contain eighteen explicitly named
`native_decide` calls. Their compiler trust axioms are `Lean.ofReduceBool` and
`Lean.trustCompiler`; this module introduces no further native calculation.
-/

namespace Erdos993Lean.Analytic.HandVariance

open Reserve Compute

/-- Source: Tables `tgt:tab:sub` and `mc:tab:sub`; the exact exported activity
rows for the named source segment. -/
def activitiesOf : Segment → List Activity
  | .lo => Data.loActivities
  | .mid => Data.midActivities
  | .u1 => Data.u1Activities
  | .u2 => Data.u2Activities
  | .u3 => Data.u3Activities
  | .u4 => Data.u4Activities

/-- Source: `mc:eq:base`, `mc:lem:base` and `tgt:thm`; the exact exported
selected-leaf rows retaining this segment's identity. -/
def basesOf (s : Segment) : List BaseCheck :=
  Data.baseChecks.filter (fun b => decide (b.segment = s.index))

/-- Source: `tgt:thm`, `mc:thm:step` and Tables `tgt:tab:sub`, `mc:tab:sub`;
the retained activity rows cover the entire named closed segment. -/
theorem activities_coverage (s : Segment) :
    segmentActivityCoverageCheck s.index (activitiesOf s) Data.allPolygons = true := by
  cases s with
  | lo => exact Data.lo_coverage
  | mid => exact Data.mid_coverage
  | u1 => exact Data.u1_coverage
  | u2 => exact Data.u2_coverage
  | u3 => exact Data.u3_coverage
  | u4 => exact Data.u4_coverage

/-- Source: exact finite-check families `chk:tgt` and `chk:mc`, consumed by
`tgt:thm` and `mc:thm:step`; every retained activity calculation is accepted. -/
theorem activities_accepted (s : Segment) :
    (activitiesOf s).all activityOK = true := by
  cases s with
  | lo => exact Data.lo_accepted
  | mid => exact Data.mid_accepted
  | u1 => exact Data.u1_accepted
  | u2 => exact Data.u2_accepted
  | u3 => exact Data.u3_accepted
  | u4 => exact Data.u4_accepted

/-- Source: `tgt:lem:child`, `tgt:lem:poly` and Tables `tgt:tab:poly`,
`mc:tab:poly`; all retained child partitions and terminal chains cover. -/
theorem polygons_coverage : Data.allPolygons.all polygonCoverageCheck = true := by
  simp only [Data.allPolygons, List.all_append, Data.midPolygon_coverage,
    Data.otherPolygon_coverage, Bool.and_self]

/-- Source: exact child-polygon calculations in families `chk:tgt`, `chk:mc`,
used in `tgt:thm` and `mc:thm:step`; every retained line and chain is accepted. -/
theorem polygons_accepted : Data.allPolygons.all polygonOK = true := by
  simp only [Data.allPolygons, List.all_append, Data.midPolygon_accepted,
    Data.otherPolygon_accepted, Bool.and_self]

/-- Source: `mc:eq:base`, `mc:lem:base` and the base part of `tgt:thm`;
the retained selected-leaf rows cover the entire named closed segment. -/
theorem bases_coverage (s : Segment) : baseCoverageCheck s.index (basesOf s) = true :=
  List.all_eq_true.mp Data.base_coverage s.index
    (List.mem_range.mpr s.index_lt_six)

/-- Source: the thirteen selected-leaf calculations in families `chk:tgt`
and `chk:mc`, used in `tgt:thm` and `mc:lem:base`; each retained row is accepted. -/
theorem bases_accepted (s : Segment) :
    (basesOf s).all (fun b => optionPositive (baseLower b)) = true := by
  apply List.all_eq_true.mpr
  intro b hb
  exact List.all_eq_true.mp Data.base_accepted b (List.mem_filter.mp hb).1

/-- Source: `tgt:thm` and `mc:thm:step`. The retained finite data prove every comparison at every feasible pair
of actual child and parent log masses in this source band. -/
theorem segment_compOK (s : Segment) :
    ∀ lam T Y : ℝ, (s.band.lo : ℝ) ≤ lam → lam ≤ s.band.hi → 0 ≤ T →
      lmass lam T ≤ Y → CompOK s.band lam T Y :=
  band_compOK_of_checks s (activities_coverage s) (activities_accepted s)
    polygons_coverage polygons_accepted

/-- Source: the all-feasible-pair comparisons of `tgt:thm`, `mc:thm:step`,
restricted to the existing reserve consumer's finite box. -/
theorem segment_boxOK (s : Segment) : BoxOK s.band := by
  intro lam T Y hlo hhi hT _ hTY _
  exact segment_compOK s lam T Y hlo hhi hT hTY

/-- Source: the all-feasible-pair comparisons of `tgt:thm`, `mc:thm:step`,
restricted to the existing reserve consumer's tails. -/
theorem segment_tailOK (s : Segment) : TailOK s.band := by
  intro lam T Y hlo hhi hT hTY _
  exact segment_compOK s lam T Y hlo hhi hT hTY

/-- Source: `mc:eq:base`, `mc:lem:base` and the selected-leaf part of
`tgt:thm`; the unchanged reserve's exact childless-vertex inequality. -/
theorem segment_leafOK (s : Segment) : LeafOK s.band :=
  band_leafOK_of_checks s (bases_coverage s) (bases_accepted s)

/-- Source: `tgt:thm`, `mc:thm:step` and `mc:def:curve`; the actual source multipliers give the unchanged reserve
step certificate throughout the closed segment, including shared endpoints. -/
theorem segment_stepCert (s : Segment) {lam : ℝ}
    (hlo : (s.band.lo : ℝ) ≤ lam) (hhi : lam ≤ s.band.hi) :
    StepCert (gamma s.band lam) lam (alpha s.band lam) 0 (capA s.band lam) :=
  stepCert_of_band (segment_bandSide s) entropyOK (segment_boxOK s)
    (segment_tailOK s) (segment_leafOK s) hlo hhi

/-- Source `mc:thm:var`: all six actual hand segments receive the forest
variance theorem through the unchanged reserve induction and leaf exchange. -/
theorem segment_bandVar (s : Segment) : BandVar s.band :=
  bandVar_of_ok s.band (segment_bandSide s) entropyOK (segment_boxOK s)
    (segment_tailOK s) (segment_leafOK s)

end Erdos993Lean.Analytic.HandVariance

#print axioms Erdos993Lean.Analytic.HandVariance.segment_compOK
#print axioms Erdos993Lean.Analytic.HandVariance.segment_stepCert
#print axioms Erdos993Lean.Analytic.HandVariance.segment_bandVar
