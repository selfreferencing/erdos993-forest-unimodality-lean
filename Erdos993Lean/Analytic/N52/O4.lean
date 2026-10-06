import Erdos993Lean.Analytic.N52.Strip
import Erdos993Lean.Analytic.Atlas.Main
import Erdos993Lean.Analytic.N52.Data.Strip
import Erdos993Lean.Analytic.N52.Checks.S01
import Erdos993Lean.Analytic.N52.Checks.S02
import Erdos993Lean.Analytic.N52.Checks.S03
import Erdos993Lean.Analytic.N52.Checks.S04
import Erdos993Lean.Analytic.N52.Checks.S05
import Erdos993Lean.Analytic.N52.Checks.S06
import Erdos993Lean.Analytic.N52.Checks.S07
import Erdos993Lean.Analytic.N52.Checks.S08
import Erdos993Lean.Analytic.N52.Checks.S09
import Erdos993Lean.Analytic.N52.Checks.S10
import Erdos993Lean.Analytic.N52.Checks.S11
import Erdos993Lean.Analytic.N52.Checks.S12
import Erdos993Lean.Analytic.N52.Checks.S13
import Erdos993Lean.Analytic.N52.Checks.S14
import Erdos993Lean.Analytic.N52.Checks.S15
import Erdos993Lean.Analytic.N52.Checks.S16
import Erdos993Lean.Analytic.N52.Checks.S17
import Erdos993Lean.Analytic.N52.Checks.S18
import Erdos993Lean.Analytic.N52.Checks.S19
import Erdos993Lean.Analytic.N52.Checks.S20
import Erdos993Lean.Analytic.N52.Checks.S21
import Erdos993Lean.Analytic.N52.Checks.S22
import Erdos993Lean.Analytic.N52.Checks.S23
import Erdos993Lean.Analytic.N52.Checks.S24
import Erdos993Lean.Analytic.N52.Checks.S25
import Erdos993Lean.Analytic.N52.Checks.S26
import Erdos993Lean.Analytic.N52.Checks.S27
import Erdos993Lean.Analytic.N52.Checks.S28
import Erdos993Lean.Analytic.N52.Checks.S29
import Erdos993Lean.Analytic.N52.Checks.S30

/-!
# O4 for `P52`: the strip checks, lane A9's atlas and the large-mean theorem

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A19.  The 30 strip checks (`Checks/S01.lean` … `S30.lean`,
one `native_decide` each: lane A9's checker `bandOK` on lane R52's 594 boxes with the box tail base `lamBox`) are
collected (`stripChecks`) and combined with lane A9's 60 band checks (`Atlas.lowerChecks`, `Atlas.upperChecks`) by
the standard-axiom glue of `Strip.lean`:

* **`explicitThreshold_small_P52`**: T1's explicit threshold for `P52` at every activity in range and every
  `P52.mfloor t ≤ m < 400`;
* **`thresholdNoValley_P52 : ThresholdNoValley P52`** (O4 for `P52`, with the large-mean theorem on `m ≥ 400`).

Trust: the 30 strip checks and lane A9's 60 checks are `native_decide` (`Lean.ofReduceBool`,
`Lean.trustCompiler`); everything else uses `propext`, `Classical.choice`, `Quot.sound`.

Scalarity check: no new scalar; see `Strip.lean`.
-/

namespace Erdos993Lean.Analytic.N52

open Erdos993Lean.Analytic.Atlas Erdos993Lean.Analytic.N52.Checks

/-- **The 30 strip checks** (`[floor(n ≥ 52), floor(n ≥ 61)]`, box tail base `lamBox`). -/
theorem stripChecks : ∀ i < 30, bandOK (Data.stripBand i) lamBox (Data.stripCap i) (Data.stripBoxes i)
    (Data.stripSlabs i) = true := by
  intro i hi
  interval_cases i
  exacts [checkS01, checkS02, checkS03, checkS04, checkS05, checkS06, checkS07, checkS08, checkS09, checkS10,
    checkS11, checkS12, checkS13, checkS14, checkS15, checkS16, checkS17, checkS18, checkS19, checkS20,
    checkS21, checkS22, checkS23, checkS24, checkS25, checkS26, checkS27, checkS28, checkS29, checkS30]

/-- **T1's explicit threshold for `P52` on bounded `m`**: every activity in range and every
`P52.mfloor t ≤ m < 400` (the strip below Profile30's floor, lane A9's atlas above it). -/
theorem explicitThreshold_small_P52 :
    ∀ t, InRange t → ∀ m, P52.mfloor t ≤ m → m < 400 →
      ExplicitThreshold (actQ t) m (P52.θb t) (P52.Db t) (P52.Tb t m) (P52.M1b t m) :=
  explicitThreshold_small_P52_of_checks Data.stripBoxes Data.stripSlabs stripChecks
    Atlas.Data.lowerBoxes Atlas.Data.lowerSlabs Atlas.Data.upperBoxes Atlas.Data.upperSlabs
    lowerChecks upperChecks

/-- **O4 for `P52`** (`ThresholdNoValley P52`): T1 with the strip and lane A9's atlas on `m < 400`, the large-mean
theorem on `m ≥ 400`. -/
theorem thresholdNoValley_P52 : ThresholdNoValley P52 :=
  thresholdNoValley_P52_of explicitThreshold_small_P52

end Erdos993Lean.Analytic.N52
