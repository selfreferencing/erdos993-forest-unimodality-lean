import Erdos993Lean.Analytic.HandVariance.FinalStep
import Erdos993Lean.Analytic.HandVariance.Assembly

/-!
# The hand variance theorem for the actual forest mixture

Source: TWIN v1.8 Appendix N.4, Theorem `mc:thm:var` and Definition
`mc:def:curve`. This theorem has no outstanding band-comparison hypothesis.
It retains the finite forest, actual activity and maximum-weight independent
set, and supplies the existing analytic `VarianceBound` interface.

The finite calculations enter only through the eighteen named acceptance
theorems in Data.Acceptance and Data.CoverageAcceptance. The complete axiom
audit below includes their `Lean.ofReduceBool` and `Lean.trustCompiler` trust.
-/

namespace Erdos993Lean.Analytic.HandVariance

/-- Source: `mc:thm:var` and `mc:def:curve`. The hand cap bounds the binomial-mixture variance for every finite forest
and every maximum-weight independent set on the complete activity window. -/
theorem hand_variance_bound (F : FiniteForest) {t : ℝ}
    (ht : InRange t) {B : Finset (Fin F.n)} (hB : IsMaxWeight F t B) :
    (forestMixture F B t).varM ≤ handCap t * (forestMixture F B t).meanM :=
  hand_variance_bound_of_bandVars segment_bandVar F ht hB

/-- Source: `mc:thm:var` and `mc:def:curve`. The existing O1 consumer receives the hand cap, retaining all other
fields of the supplied analytic profile verbatim. -/
theorem varianceBound_handProfile (P : Profile) : VarianceBound (handProfile P) :=
  varianceBound_handProfile_of_bandVars P segment_bandVar

/-- Source: `mc:thm:var` and `mc:def:curve`. Any profile whose cap dominates the hand cap also receives the unchanged
O1 variance interface. The cap domination is the only profile-specific input. -/
theorem varianceBound_of_handCap {P : Profile}
    (hDb : ∀ t : ℝ, InRange t → handCap t ≤ P.Db t) : VarianceBound P :=
  varianceBound_of_bandVars segment_bandVar hDb

/-- Source: the first conclusion of `mc:thm:var`, with the cap selected by
`mc:def:curve`; the hard-core variance of the actual selected count. -/
theorem hand_selected_count_variance_bound (F : FiniteForest) {t : ℝ}
    (ht : InRange t) {B : Finset (Fin F.n)} (hB : IsMaxWeight F t B) :
    HardCore.varKB F t B ≤
      (1 + (handCap t - 1) * actQ t) * weightW F t B := by
  obtain ⟨s,hlo,hhi,hcap⟩ := exists_segment_for_handCap ht
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
  have h := Reserve.varKB_le_of_stepCert F hB.1
    (Reserve.leafProp_of_isMaxWeight F htpos hB) (segment_stepCert s hlo hhi)
  simpa only [Reserve.capA, ← hcap] using h

end Erdos993Lean.Analytic.HandVariance

#print axioms Erdos993Lean.Analytic.HandVariance.hand_variance_bound
#print axioms Erdos993Lean.Analytic.HandVariance.varianceBound_handProfile
#print axioms Erdos993Lean.Analytic.HandVariance.hand_selected_count_variance_bound
