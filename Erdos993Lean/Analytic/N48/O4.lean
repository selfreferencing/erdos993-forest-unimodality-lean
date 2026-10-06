import Erdos993Lean.Analytic.N48.Strip
import Erdos993Lean.Analytic.N52.O4
import Erdos993Lean.Analytic.N48.Data.Strip
import Erdos993Lean.Analytic.N48.Checks.P00
import Erdos993Lean.Analytic.N48.Checks.P01
import Erdos993Lean.Analytic.N48.Checks.P02
import Erdos993Lean.Analytic.N48.Checks.P03
import Erdos993Lean.Analytic.N48.Checks.P04
import Erdos993Lean.Analytic.N48.Checks.P05
import Erdos993Lean.Analytic.N48.Checks.P06
import Erdos993Lean.Analytic.N48.Checks.P07
import Erdos993Lean.Analytic.N48.Checks.P08
import Erdos993Lean.Analytic.N48.Checks.P09
import Erdos993Lean.Analytic.N48.Checks.P10
import Erdos993Lean.Analytic.N48.Checks.P11
import Erdos993Lean.Analytic.N48.Checks.P12
import Erdos993Lean.Analytic.N48.Checks.P15
import Erdos993Lean.Analytic.N48.Checks.P16
import Erdos993Lean.Analytic.N48.Checks.P17
import Erdos993Lean.Analytic.N48.Checks.P18
import Erdos993Lean.Analytic.N48.Checks.P19
import Erdos993Lean.Analytic.N48.Checks.P20
import Erdos993Lean.Analytic.N48.Checks.P21
import Erdos993Lean.Analytic.N48.Checks.P22
import Erdos993Lean.Analytic.N48.Checks.P23
import Erdos993Lean.Analytic.N48.Checks.P24
import Erdos993Lean.Analytic.N48.Checks.P25
import Erdos993Lean.Analytic.N48.Checks.P26
import Erdos993Lean.Analytic.N48.Checks.P27
import Erdos993Lean.Analytic.N48.Checks.P28
import Erdos993Lean.Analytic.N48.Checks.P29
import Erdos993Lean.Analytic.N48.Checks.P30
import Erdos993Lean.Analytic.N48.Checks.P31
import Erdos993Lean.Analytic.N48.Checks.P32

/-!
# O4 for `P48`: the n ≥ 48 piece checks, lane A19's strip, lane A9's atlas and the large-mean theorem

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A20.  The 31 piece checks (`Checks/P00.lean` … `P32.lean`
without pieces 13 and 14, one `native_decide` each: lane A9's checker `bandOK` on lane R4X's 547 boxes — 29 strips of
`atlas48_trial` and the strips of bands 25 and 29 of `atlas45_trial` — with the box tail base `lamBox`) are collected
(`strip48Checks`) and combined with lane A19's `N52.explicitThreshold_small_P52` (its 30 strip checks and lane A9's 60
band checks) by the standard-axiom glue of `Strip.lean`:

* **`explicitThreshold_small_P48`**: T1's explicit threshold for `P48` at every activity in range and every
  `P48.mfloor t ≤ m < 400`;
* **`thresholdNoValley_P48 : ThresholdNoValley P48`** (O4 for `P48`, with the large-mean theorem on `m ≥ 400`).

Trust: the 31 new piece checks, lane A19's 30 and lane A9's 60 checks are `native_decide` (`Lean.ofReduceBool`,
`Lean.trustCompiler`); everything else uses `propext`, `Classical.choice`, `Quot.sound`.

Scalarity check: no new scalar; see `Strip.lean`.
-/

namespace Erdos993Lean.Analytic.N48

open Erdos993Lean.Analytic.Atlas Erdos993Lean.Analytic.N48.Checks

/-- **The 31 n ≥ 48 piece checks** (`[floor(n ≥ 48), floor(n ≥ 52)]` on every piece but 13 and 14; box tail base
`lamBox`). -/
theorem strip48Checks : ∀ p < 33, p ≠ 13 → p ≠ 14 →
    bandOK (Data.piece48Band p) lamBox (Data.piece48Cap p) (Data.strip48Boxes p) (Data.strip48Slabs p) = true := by
  intro p hp h13 h14
  interval_cases p
  · exact checkP00
  · exact checkP01
  · exact checkP02
  · exact checkP03
  · exact checkP04
  · exact checkP05
  · exact checkP06
  · exact checkP07
  · exact checkP08
  · exact checkP09
  · exact checkP10
  · exact checkP11
  · exact checkP12
  · exact absurd rfl h13
  · exact absurd rfl h14
  · exact checkP15
  · exact checkP16
  · exact checkP17
  · exact checkP18
  · exact checkP19
  · exact checkP20
  · exact checkP21
  · exact checkP22
  · exact checkP23
  · exact checkP24
  · exact checkP25
  · exact checkP26
  · exact checkP27
  · exact checkP28
  · exact checkP29
  · exact checkP30
  · exact checkP31
  · exact checkP32

/-- **T1's explicit threshold for `P48` on bounded `m`**: every activity in range and every
`P48.mfloor t ≤ m < 400` (the n ≥ 48 strip, then lane A19's n ≥ 52 strip and lane A9's atlas). -/
theorem explicitThreshold_small_P48 :
    ∀ t, InRange t → ∀ m, P48.mfloor t ≤ m → m < 400 →
      ExplicitThreshold (actQ t) m (P48.θb t) (P48.Db t) (P48.Tb t m) (P48.M1b t m) :=
  explicitThreshold_small_P48_of_checks Data.strip48Boxes Data.strip48Slabs strip48Checks
    N52.explicitThreshold_small_P52

/-- **O4 for `P48`** (`ThresholdNoValley P48`): T1 with the strips and lane A9's atlas on `m < 400`, the large-mean
theorem on `m ≥ 400`. -/
theorem thresholdNoValley_P48 : ThresholdNoValley P48 :=
  thresholdNoValley_P48_of explicitThreshold_small_P48

end Erdos993Lean.Analytic.N48
