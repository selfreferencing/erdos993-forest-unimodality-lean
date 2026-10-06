import Erdos993Lean.Analytic.V21.Inputs

/-!
# Paper v2.1, Theorem 3.1: the exact consumer of parameter Theorem 5.8

Sources: TWIN_v2.1/s3_part_a.tex (`p2:thm:main`, proof steps 1--3),
s5_part_b.tex (`p2:thm:O4`). This module records a conditional consumer,
not an unconditional proof of either theorem. Its hypothesis retains both
Laplace-rate families, the actual hand cap and the window-only mean floor.
No earlier second criterion, density certificate or certified variance
cover is used in its proof.
-/

namespace Erdos993Lean.Analytic.V21

open Erdos993Lean N44

/-- Source: Theorem 5.8, with both the subinterval and band Laplace constraints. -/
def ParameterNoValley : Prop :=
  ∀ t : ℝ, InRange t → ∀ m : ℝ,
    ((MGF.N25.Data.mmin25.getD (pieceOf t) 0 : ℚ) : ℝ) ≤ m →
    ∀ (ι : Type) (X : Mixture ι) (k : ℤ), X.IsProb → X.meanM = m →
      X.expect (fun M Y => delta (actQ t) k M Y) = 0 →
      X.expect (fun M Y => delta (actQ t) k M Y ^ 2) ≤
        P44.θb t * (actQ t * (1 - actQ t)) * m →
      X.varM ≤ HandVariance.handCap t * m →
      (∀ r ∈ mgfRows (MGF.tilts44R t) (actQ t) m,
        X.expect (fun M _ => r.1 ^ M) ≤ r.2) →
      (∀ r ∈ mgfRows (bandTilts t) (actQ t) m,
        X.expect (fun M _ => r.1 ^ M) ≤ r.2) →
      ¬ X.WeakValley (actQ t) k

/-- Source: the proof of Theorem 3.1. Conditional on exactly Theorem 5.8,
no window rank of a forest of order at least 25 is a weak valley. -/
theorem noWeakValley_of_parameterNoValley (hparam : ParameterNoValley)
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
    (MGF.tailMGF44_all F hR hBmax) (bandMGF_all F hR hBmax)
  exact not_valley_of_not_weakValley F (forestMixture F B t) ht (by omega)
    (hmix.prob_eq F t B ht hBind (k - 1)) (hmix.prob_eq F t B ht hBind k)
    (hmix.prob_eq F t B ht hBind (k + 1)) hnv

/-- Source: Theorem 3.1 and the window corollary. This is explicitly conditional;
`ParameterNoValley` must be proved by all three cases of Theorem 5.8. -/
theorem ceilingStatement_25_of_parameterNoValley (hparam : ParameterNoValley) :
    CeilingStatement 25 := by
  intro F hn
  unfold independenceSequenceUnimodal
  exact unimodalUpTo_of_unimodal (unimodal_of_noWeakValley_window F
    (fun k hk1 hk2 => noWeakValley_of_parameterNoValley hparam F hn k hk1 hk2))

end Erdos993Lean.Analytic.V21
