import Erdos993Lean.Analytic.HandVariance.Defs
import Erdos993Lean.Analytic.Reserve.Assembly
import Erdos993Lean.Analytic.HardCore.Mixture

/-!
# Conditional assembly of the hand variance bound

Source: `for_tong/TWIN_v1.8/apx_hand.tex`, Theorem `mc:thm:var`,
Definition `mc:def:curve` and Table `mc:tab:curve`, in
`ProofRuns/2026-09-28_analytic_large_n/LEAN`.

This module consumes a variance theorem for each of the six closed segments.
Those six inputs are explicit hypotheses: this module does not establish the
hand step certificates or instantiate the hypotheses with the old certified
variance route. At shared endpoints the smaller cap is retained. The actual
forest, activity, maximum-weight independent set and binomial mixture survive
verbatim into the existing analytic consumer.
-/

namespace Erdos993Lean.Analytic.HandVariance

open Reserve

/-- Source: Definition `mc:def:curve`; preserve the analytic profile's
other fields while supplying exactly the hand variance cap. -/
noncomputable def handProfile (P : Profile) : Profile := { P with Db := handCap }

/-- Source: Definition `mc:def:curve` and Table `mc:tab:curve`.
Every activity in the window lies in a closed segment attaining the least
hand cap; this selects a segment while retaining the activity itself. -/
theorem exists_segment_for_handCap {t : ℝ} (ht : InRange t) :
    ∃ s : Segment, (s.band.lo : ℝ) ≤ t ∧ t ≤ s.band.hi ∧
      handCap t = (s.band.D : ℝ) := by
  by_cases h0 : t ≤ 11 / 20
  · refine ⟨.lo, ?_, ?_, ?_⟩
    · norm_num [Segment.band]
      exact ht.1
    · norm_num [Segment.band]
      exact h0
    · have h1 : t ≤ 263 / 200 := by linarith
      norm_num [handCap, h1, Segment.band]
  by_cases h1 : t ≤ 263 / 200
  · refine ⟨.mid, ?_, ?_, ?_⟩
    · norm_num [Segment.band]
      linarith
    · norm_num [Segment.band]
      exact h1
    · norm_num [handCap, h1, Segment.band]
  by_cases h2 : t ≤ 3 / 2
  · refine ⟨.u1, ?_, ?_, ?_⟩
    · norm_num [Segment.band]
      linarith
    · norm_num [Segment.band]
      exact h2
    · norm_num [handCap, h1, h2, Segment.band]
  by_cases h3 : t ≤ 7 / 4
  · refine ⟨.u2, ?_, ?_, ?_⟩
    · norm_num [Segment.band]
      linarith
    · norm_num [Segment.band]
      exact h3
    · norm_num [handCap, h1, h2, h3, Segment.band]
  by_cases h4 : t ≤ 2
  · refine ⟨.u3, ?_, ?_, ?_⟩
    · norm_num [Segment.band]
      linarith
    · norm_num [Segment.band]
      exact h4
    · norm_num [handCap, h1, h2, h3, h4, Segment.band]
  · refine ⟨.u4, ?_, ?_, ?_⟩
    · norm_num [Segment.band]
      linarith
    · norm_num [Segment.band]
      exact ht.2
    · norm_num [handCap, h1, h2, h3, h4, Segment.band]

/-- Source: Theorem `mc:thm:var`. Conditional on all six closed-segment
variance theorems, the hand cap bounds the variance of the actual forest
mixture for every forest and every maximum-weight independent set. -/
theorem hand_variance_bound_of_bandVars
    (hbands : ∀ s : Segment, BandVar s.band) (F : FiniteForest) {t : ℝ}
    (ht : InRange t) {B : Finset (Fin F.n)} (hB : IsMaxWeight F t B) :
    (forestMixture F B t).varM ≤
      handCap t * (forestMixture F B t).meanM := by
  obtain ⟨s, hlo, hhi, hcap⟩ := exists_segment_for_handCap ht
  rw [hcap]
  exact hbands s F t hlo hhi B hB

/-- Source: Theorem `mc:thm:var` and the existing O1 `VarianceBound`
interface. Conditional on the six hand segment theorems, any profile whose
variance cap dominates the hand cap receives the unchanged O1 input. -/
theorem varianceBound_of_bandVars {P : Profile}
    (hbands : ∀ s : Segment, BandVar s.band)
    (hDb : ∀ t : ℝ, InRange t → handCap t ≤ P.Db t) :
    VarianceBound P := by
  intro F _ t ht _ B hB
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
  have hprob := HardCore.forestMixture_isProb F hB.1 htpos
  have hm : 0 ≤ (forestMixture F B t).meanM := by
    unfold Mixture.meanM Mixture.expect
    exact Finset.sum_nonneg fun σ hσ =>
      mul_nonneg (hprob.1 σ hσ) (Nat.cast_nonneg _)
  exact le_trans (hand_variance_bound_of_bandVars hbands F ht hB)
    (mul_le_mul_of_nonneg_right (hDb t ht) hm)

/-- Source: Theorem `mc:thm:var`; the six explicit hand segment variance
theorems supply the named analytic consumer with exactly the hand cap.
No domination claim about the old profile cap is needed or asserted. -/
theorem varianceBound_handProfile_of_bandVars (P : Profile)
    (hbands : ∀ s : Segment, BandVar s.band) : VarianceBound (handProfile P) :=
  varianceBound_of_bandVars hbands (fun _ _ => le_rfl)

end Erdos993Lean.Analytic.HandVariance
