import Erdos993Lean.Analytic.V22.Checks.BasicTheorems
import Erdos993Lean.Analytic.V22.Checks.CoefficientTheorems
import Erdos993Lean.Analytic.V22.Checks.GeneratedTheorems

/-!
# The twenty independent Section 7 facts

Every field is the unchanged source proposition. The bundle omits full
Lemma 7.14 and its certified exports, so the analysis lane can consume
these facts before constructing the marked-spike window transport.

The source proof of Theorem 5.14 explicitly uses Lemma 7.11 and Lemmas
7.16--7.20, together with analytic Lemmas 5.9--5.13; it does not use 7.14.
Theorem 5.14's final statement covers `t >= tau`. Marked spike cells below
`tau` require its generic fixed-start, all-integer-offset minorant argument
with the marked cell's starting hypotheses, not an application of that
final statement. This bundle supplies no analytic transport instance.
-/

namespace Erdos993Lean.Analytic.V22.Checked

structure Section7IndependentFacts : Prop where
  l7_1 : Checks.lemma_7_1
  l7_2 : Checks.lemma_7_2
  l7_3 : Checks.lemma_7_3
  l7_4 : Checks.lemma_7_4
  l7_5 : Checks.lemma_7_5
  l7_6 : Checks.lemma_7_6
  l7_7 : Checks.lemma_7_7
  l7_8 : Checks.lemma_7_8
  l7_9 : Checks.lemma_7_9
  l7_10 : Checks.lemma_7_10
  l7_11 : Checks.lemma_7_11
  l7_12 : Checks.lemma_7_12
  l7_13 : Checks.lemma_7_13
  l7_15 : Checks.lemma_7_15
  l7_16 : Checks.lemma_7_16
  l7_17 : Checks.lemma_7_17
  l7_18 : Checks.lemma_7_18
  l7_19 : Checks.lemma_7_19
  l7_20 : Checks.lemma_7_20
  l7_21 : Checks.lemma_7_21

/-- The unchanged twenty independent finite-check propositions, with no
marked-spike analytic transport argument. -/
theorem checkedSection7Independent : Section7IndependentFacts where
  l7_1 := lemma_7_1
  l7_2 := lemma_7_2
  l7_3 := lemma_7_3
  l7_4 := lemma_7_4
  l7_5 := lemma_7_5
  l7_6 := lemma_7_6
  l7_7 := lemma_7_7
  l7_8 := lemma_7_8
  l7_9 := lemma_7_9
  l7_10 := lemma_7_10
  l7_11 := lemma_7_11
  l7_12 := lemma_7_12
  l7_13 := lemma_7_13
  l7_15 := lemma_7_15
  l7_16 := lemma_7_16
  l7_17 := lemma_7_17
  l7_18 := lemma_7_18
  l7_19 := lemma_7_19
  l7_20 := lemma_7_20
  l7_21 := lemma_7_21

end Erdos993Lean.Analytic.V22.Checked
