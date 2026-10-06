import Erdos993Lean.Analytic.N45.Strip
import Erdos993Lean.Analytic.N48.O4
import Erdos993Lean.Analytic.N45.Data.Strip
import Erdos993Lean.Analytic.N45.Checks.P13
import Erdos993Lean.Analytic.N45.Checks.P14
import Erdos993Lean.Analytic.N45.Checks.P15
import Erdos993Lean.Analytic.N45.Checks.P16
import Erdos993Lean.Analytic.N45.Checks.P17
import Erdos993Lean.Analytic.N45.Checks.P18
import Erdos993Lean.Analytic.N45.Checks.P19
import Erdos993Lean.Analytic.N45.Checks.P20
import Erdos993Lean.Analytic.N45.Checks.P21
import Erdos993Lean.Analytic.N45.Checks.P24
import Erdos993Lean.Analytic.N45.Checks.P25
import Erdos993Lean.Analytic.N45.Checks.P26
import Erdos993Lean.Analytic.N45.Checks.P27
import Erdos993Lean.Analytic.N45.Checks.P28
import Erdos993Lean.Analytic.N45.Checks.P29
import Erdos993Lean.Analytic.N45.Checks.P30
import Erdos993Lean.Analytic.N45.Checks.P31
import Erdos993Lean.Analytic.N45.Checks.P32
import Erdos993Lean.Analytic.N45.Checks.P33
import Erdos993Lean.Analytic.N45.Checks.P35
import Erdos993Lean.Analytic.N45.Checks.P36
import Erdos993Lean.Analytic.N45.Checks.P37
import Erdos993Lean.Analytic.N45.Checks.P38
import Erdos993Lean.Analytic.N45.Checks.P39
import Erdos993Lean.Analytic.N45.Checks.P40
import Erdos993Lean.Analytic.N45.Checks.P41
import Erdos993Lean.Analytic.N45.Checks.P42
import Erdos993Lean.Analytic.N45.Checks.P43
import Erdos993Lean.Analytic.N45.Checks.P44
import Erdos993Lean.Analytic.N45.Checks.P45

/-!
# O4 for `P45`: the n ≥ 45 piece checks and lane A20's O4 for `P48`

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A21.  The 30 piece checks (`Checks/P13.lean` … `P45.lean`, one
`native_decide` each: lane A9's checker `bandOK` on the 1969 boxes of the n ≥ 45 strip — 28 strips of lane R4X's
`atlas45_trial` trimmed to `[floor, cap]`, and two strips built by this lane with a byte-identical copy of R4X's constructor —
with the piece's caps and the box tail base `lamBox`) are collected (`strip45Checks`) and combined with lane A20's
`N48.explicitThreshold_small_P48` (its 31 piece checks, lane A19's 30 strip checks and lane A9's 60 band checks) by the
standard-axiom glue of `Strip.lean`:

* **`explicitThreshold_small_P45`**: T1's explicit threshold for `P45` at every activity in range and every
  `P45.mfloor t ≤ m < 400`;
* **`thresholdNoValley_P45 : ThresholdNoValley P45`** (O4 for `P45`, with the large-mean theorem on `m ≥ 400`).

Trust: the 30 new piece checks and the inherited checks are `native_decide` (`Lean.ofReduceBool`,
`Lean.trustCompiler`); everything else uses `propext`, `Classical.choice`, `Quot.sound`.

Scalarity check: no new scalar; see `Strip.lean`.
-/

namespace Erdos993Lean.Analytic.N45

open Erdos993Lean.Analytic.Atlas Erdos993Lean.Analytic.N45.Checks

/-- **The 30 n ≥ 45 piece checks** (`[floor(n ≥ 45), floor(n ≥ 48)]` on every piece whose floor drops; box tail base
`lamBox`). -/
theorem strip45Checks : ∀ p < 46, Data.mmin45.getD p 0 < Data.piece45Cap p →
    bandOK (Data.piece45Band p) lamBox (Data.piece45Cap p) (Data.strip45Boxes p) (Data.strip45Slabs p) = true := by
  intro p hp h
  interval_cases p
  · exact absurd h (by decide +kernel)
  · exact absurd h (by decide +kernel)
  · exact absurd h (by decide +kernel)
  · exact absurd h (by decide +kernel)
  · exact absurd h (by decide +kernel)
  · exact absurd h (by decide +kernel)
  · exact absurd h (by decide +kernel)
  · exact absurd h (by decide +kernel)
  · exact absurd h (by decide +kernel)
  · exact absurd h (by decide +kernel)
  · exact absurd h (by decide +kernel)
  · exact absurd h (by decide +kernel)
  · exact absurd h (by decide +kernel)
  · exact checkP13
  · exact checkP14
  · exact checkP15
  · exact checkP16
  · exact checkP17
  · exact checkP18
  · exact checkP19
  · exact checkP20
  · exact checkP21
  · exact absurd h (by decide +kernel)
  · exact absurd h (by decide +kernel)
  · exact checkP24
  · exact checkP25
  · exact checkP26
  · exact checkP27
  · exact checkP28
  · exact checkP29
  · exact checkP30
  · exact checkP31
  · exact checkP32
  · exact checkP33
  · exact absurd h (by decide +kernel)
  · exact checkP35
  · exact checkP36
  · exact checkP37
  · exact checkP38
  · exact checkP39
  · exact checkP40
  · exact checkP41
  · exact checkP42
  · exact checkP43
  · exact checkP44
  · exact checkP45

/-- **T1's explicit threshold for `P45` on bounded `m`**: every activity in range and every
`P45.mfloor t ≤ m < 400` (the n ≥ 45 strip, then lane A20's `P48`). -/
theorem explicitThreshold_small_P45 :
    ∀ t, InRange t → ∀ m, P45.mfloor t ≤ m → m < 400 →
      ExplicitThreshold (actQ t) m (P45.θb t) (P45.Db t) (P45.Tb t m) (P45.M1b t m) :=
  explicitThreshold_small_P45_of_checks Data.strip45Boxes Data.strip45Slabs strip45Checks
    N48.explicitThreshold_small_P48

/-- **O4 for `P45`** (`ThresholdNoValley P45`): T1 with the strips and the atlases on `m < 400`, the large-mean
theorem on `m ≥ 400`. -/
theorem thresholdNoValley_P45 : ThresholdNoValley P45 :=
  thresholdNoValley_P45_of explicitThreshold_small_P45

end Erdos993Lean.Analytic.N45
