import Erdos993Lean.Analytic.V22.Checks.BasicTheorems
import Erdos993Lean.Analytic.V22.Checks.CoefficientTheorems
import Erdos993Lean.Analytic.V22.Checks.GeneratedTheorems
import Erdos993Lean.Analytic.V22.Checks.SpikeTheorems

/-! Exact Section 7 fact bundle. Twenty lemma wrappers are unconditional;
Lemma 7.14 and its certified exports require the named analytic transport
explicitly. No transport instance is installed or manufactured by finite
checking. This module and its pending dependencies require serial verification.
-/

namespace Erdos993Lean.Analytic.V22.Checked

structure Section7Facts : Prop where
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
  l7_14 : Checks.lemma_7_14
  l7_15 : Checks.lemma_7_15
  l7_16 : Checks.lemma_7_16
  l7_17 : Checks.lemma_7_17
  l7_18 : Checks.lemma_7_18
  l7_19 : Checks.lemma_7_19
  l7_20 : Checks.lemma_7_20
  l7_21 : Checks.lemma_7_21
  l7_14_certified : Checks.lemma_7_14_certified

theorem checkedSection7
    (transport : Compute.SpikeWindowExprs.DeficitToWindowPriceTransport) : Section7Facts where
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
  l7_14 := lemma_7_14 transport
  l7_15 := lemma_7_15
  l7_16 := lemma_7_16
  l7_17 := lemma_7_17
  l7_18 := lemma_7_18
  l7_19 := lemma_7_19
  l7_20 := lemma_7_20
  l7_21 := lemma_7_21
  l7_14_certified := lemma_7_14_certified transport

end Erdos993Lean.Analytic.V22.Checked
