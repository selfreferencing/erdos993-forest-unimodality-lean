import Erdos993Lean.Analytic.V21.Assembly
import Erdos993Lean.Analytic.V22.Checks.Statements

/-!
# Lane F interface definitions for paper v2.2

Source: the note's above-starting-mean no-valley theorem, with the consumer
hypotheses of `V21.ParameterNoValley` and without its band-rate family.
These are definitions only. The analysis proof of the interface must consume
the source analytic theorems and exactly the finite statements bundled here.
-/

namespace Erdos993Lean.Analytic.V22

open Erdos993Lean Erdos993Lean.Analytic N44

/-- The sole finite-check premise reserved for the lane F assembly. The
certified (rather than display-rounded) B3 exports are retained for ROW-v21. -/
def FiniteChecks : Prop :=
  Checks.lemma_7_1 ∧ Checks.lemma_7_2 ∧ Checks.lemma_7_3 ∧
  Checks.lemma_7_4 ∧ Checks.lemma_7_5 ∧ Checks.lemma_7_6 ∧
  Checks.lemma_7_7 ∧ Checks.lemma_7_8 ∧ Checks.lemma_7_9 ∧
  Checks.lemma_7_10 ∧ Checks.lemma_7_11 ∧ Checks.lemma_7_12 ∧
  Checks.lemma_7_13 ∧ Checks.lemma_7_14 ∧ Checks.lemma_7_14_certified ∧
  Checks.lemma_7_15 ∧ Checks.lemma_7_16 ∧ Checks.lemma_7_17 ∧
  Checks.lemma_7_18 ∧ Checks.lemma_7_19 ∧ Checks.lemma_7_20 ∧ Checks.lemma_7_21

/-- Exact intended conclusion E6: every real activity in the inherited
range and every mean at or above the Table 2 starting mean of its piece.
All the native mixture, zero mean, variance and inherited MGF rows survive. -/
def ParameterNoValley : Prop :=
  ∀ t : ℝ, InRange t → ∀ m : ℝ,
    startingMean (pieceOf t) ≤ m →
    ∀ (ι : Type) (X : Mixture ι) (k : ℤ), X.IsProb → X.meanM = m →
      X.expect (fun M Y => delta (actQ t) k M Y) = 0 →
      X.expect (fun M Y => delta (actQ t) k M Y ^ 2) ≤
        P44.θb t * (actQ t * (1 - actQ t)) * m →
      X.varM ≤ HandVariance.handCap t * m →
      (∀ r ∈ mgfRows (MGF.tilts44R t) (actQ t) m,
        X.expect (fun M _ => r.1 ^ M) ≤ r.2) →
      ¬ X.WeakValley (actQ t) k

end Erdos993Lean.Analytic.V22
