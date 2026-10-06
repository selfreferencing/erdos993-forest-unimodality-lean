import Erdos993Lean.Analytic.V22.Assembly

/-! Paper v2.2 Theorem 3.1: the actual forest-mixture ceiling consumer.
The proof uses the window mean floor, variance bound, hand cap and
subinterval MGF rows. Its only analytic premise is Theorem 5.6. -/
namespace Erdos993Lean.Analytic.V22

open Erdos993Lean N44

/-- Source: the proof of Theorem 3.1. Conditional on exactly v2.2 Theorem 5.6,
no window rank of a forest of order at least 25 is a weak valley. -/
theorem noWeakValley_of_parameterNoValley (hparam : FullParameterNoValley)
    (F : FiniteForest) (hn : 25 ≤ F.n) (k : ℕ)
    (hk1 : (F.n + 3) / 4 < k) (hk2 : k < hB F) :
    ¬ (independenceCount F k ≤ independenceCount F (k - 1) ∧
       independenceCount F k ≤ independenceCount F (k + 1)) := by
  have hmix := mixtureFacts
  obtain ⟨t, hR, ht, hI, hμ⟩ := exists_activity_inRange F k hk1 hk2
  obtain ⟨B, hBmax⟩ := hmix.exists_maxWeight F t ht
  have hBind : F.graph.IsIndepSet (B : Set (Fin F.n)) := hBmax.1
  have hδ2 : (forestMixture F B t).expect (fun M Y => delta (actQ t) k M Y ^ 2) ≤
      P44.θb t * (actQ t * (1 - actQ t)) * (forestMixture F B t).meanM := by
    rw [hmix.var_delta F t B ht hBind k hμ]
    have hO2 := varianceRatioBound44_all F hR hBmax
    rw [← hmix.weight_eq F t B ht hBind] at hO2
    linarith
  have hnv := hparam t hR (forestMixture F B t).meanM
    (MGF.N25.densityBound25 F hn t hR hI B hBmax)
    (Finset (Fin F.n)) (forestMixture F B t) k
    (hmix.isProb F t B ht hBind) rfl (hmix.mean_delta F t B ht hBind k hμ) hδ2
    (HandVariance.hand_variance_bound F hR hBmax)
    (MGF.tailMGF44_all F hR hBmax)
  exact not_valley_of_not_weakValley F (forestMixture F B t) ht (by omega)
    (hmix.prob_eq F t B ht hBind (k - 1)) (hmix.prob_eq F t B ht hBind k)
    (hmix.prob_eq F t B ht hBind (k + 1)) hnv

/-- Source: Theorem 3.1 and the window corollary. This is explicitly conditional;
`FullParameterNoValley` is supplied by the two cases of v2.2 Theorem 5.6. -/
theorem ceilingStatement_25_of_parameterNoValley (hparam : FullParameterNoValley) :
    CeilingStatement 25 := by
  intro F hn
  unfold independenceSequenceUnimodal
  exact unimodalUpTo_of_unimodal (unimodal_of_noWeakValley_window F
    (fun k hk1 hk2 => noWeakValley_of_parameterNoValley hparam F hn k hk1 hk2))

end Erdos993Lean.Analytic.V22
