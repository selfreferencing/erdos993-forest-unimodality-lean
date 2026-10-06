import Erdos993Lean.Analytic.V22.Analysis.InterfaceDefinitions
import Erdos993Lean.Analytic.V21.Below50

/-!
# Paper v2.2 Theorem 5.6: the two-case parameter theorem

The exact E interface is copied from one-route-v22-analysis at 7a06d9f0.
Case (a') reuses all 779 checked F6 boxes on [m25,50]. Since every
Table 17 starting mean is at most 50, no restriction of those boxes is needed.
Case (c') consumes the named E proposition at the actual starting mean.
All mixture parameters and source moment/MGF conditions survive verbatim.
-/
namespace Erdos993Lean.Analytic.V22

open Erdos993Lean Erdos993Lean.Analytic N44

/-- Main-paper Table 17 (standalone-note Table 2): all 55 exact rational starting means are at most 50. -/
theorem startingMean_le_50 (p : Nat) (hp : p < 55) : startingMean p ≤ 50 := by
  have hall : ∀ i : Fin 55, mu0Data.getD i.val 0 ≤ (50 : ℚ) := by decide +kernel
  unfold startingMean
  exact_mod_cast hall ⟨p, hp⟩

/-- Theorem 5.6(a'): F6 proves the entire interval below the new start. -/
theorem parameter_case_a {t m : ℝ} (ht : InRange t)
    (hm : ((V21.m25.getD (pieceOf t) 0 : ℚ) : ℝ) ≤ m)
    (hstart : m < startingMean (pieceOf t)) :
    NoValleyAtMGF2 (actQ t) m (P44.θb t) (HandVariance.handCap t)
      (mgfRows (MGF.tilts44R t) (actQ t) m) := by
  apply V21.below50_noValley ht hm
  exact hstart.le.trans (startingMean_le_50 _ (pieceOf_spec ht).1)

/-- Theorem 5.6(c'): the above-start fiber theorem is E's exact interface.
This is a named hypothesis, and no unconditional analytic theorem is asserted. -/
theorem parameter_case_c (fiberAbove : ParameterNoValley) : ParameterNoValley :=
  fiberAbove

/-- Paper v2.2 Theorem 5.6, with the unchanged mean floor and source
variance, hand cap, zero-mean and subinterval MGF hypotheses. -/
def FullParameterNoValley : Prop :=
  ∀ t : ℝ, InRange t → ∀ m : ℝ,
    ((MGF.N25.Data.mmin25.getD (pieceOf t) 0 : ℚ) : ℝ) ≤ m →
    ∀ (ι : Type) (X : Mixture ι) (k : ℤ), X.IsProb → X.meanM = m →
      X.expect (fun M Y => delta (actQ t) k M Y) = 0 →
      X.expect (fun M Y => delta (actQ t) k M Y ^ 2) ≤
        P44.θb t * (actQ t * (1 - actQ t)) * m →
      X.varM ≤ HandVariance.handCap t * m →
      (∀ r ∈ mgfRows (MGF.tilts44R t) (actQ t) m,
        X.expect (fun M _ => r.1 ^ M) ≤ r.2) →
      ¬ X.WeakValley (actQ t) k

/-- Theorem 5.6: exact split at mu0, including equality in case (c'). -/
theorem parameterNoValley (fiberAbove : ParameterNoValley) :
    FullParameterNoValley := by
  intro t ht m hm ι X k hP hmean hδ hδ2 hvar hSub
  by_cases hstart : startingMean (pieceOf t) ≤ m
  · exact parameter_case_c fiberAbove t ht m hstart ι X k
      hP hmean hδ hδ2 hvar hSub
  · have hfloor : ((V21.m25.getD (pieceOf t) 0 : ℚ) : ℝ) ≤ m := by
      rw [V21.m25_eq_window25]
      exact hm
    exact parameter_case_a ht hfloor (lt_of_not_ge hstart)
      ι X k hP hmean hδ hδ2 hvar hSub

end Erdos993Lean.Analytic.V22
