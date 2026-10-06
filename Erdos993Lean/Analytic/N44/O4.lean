import Erdos993Lean.Analytic.N44.Strip
import Erdos993Lean.Analytic.N45.O4
import Erdos993Lean.Analytic.N44.Data.Strip
import Erdos993Lean.Analytic.N44.Checks.P00
import Erdos993Lean.Analytic.N44.Checks.P01
import Erdos993Lean.Analytic.N44.Checks.P02
import Erdos993Lean.Analytic.N44.Checks.P03
import Erdos993Lean.Analytic.N44.Checks.P04
import Erdos993Lean.Analytic.N44.Checks.P05
import Erdos993Lean.Analytic.N44.Checks.P06
import Erdos993Lean.Analytic.N44.Checks.P07
import Erdos993Lean.Analytic.N44.Checks.P08
import Erdos993Lean.Analytic.N44.Checks.P09
import Erdos993Lean.Analytic.N44.Checks.P10
import Erdos993Lean.Analytic.N44.Checks.P11
import Erdos993Lean.Analytic.N44.Checks.P12
import Erdos993Lean.Analytic.N44.Checks.P13
import Erdos993Lean.Analytic.N44.Checks.P14
import Erdos993Lean.Analytic.N44.Checks.P15
import Erdos993Lean.Analytic.N44.Checks.P16
import Erdos993Lean.Analytic.N44.Checks.P17
import Erdos993Lean.Analytic.N44.Checks.P18
import Erdos993Lean.Analytic.N44.Checks.P31
import Erdos993Lean.Analytic.N44.Checks.P32
import Erdos993Lean.Analytic.N44.Checks.P33
import Erdos993Lean.Analytic.N44.Checks.P34
import Erdos993Lean.Analytic.N44.Checks.P35
import Erdos993Lean.Analytic.N44.Checks.P43
import Erdos993Lean.Analytic.N44.Checks.P44
import Erdos993Lean.Analytic.N44.Checks.P54

/-!
# O4 for `P44`: the n ≥ 44 piece checks and O4 for `P45`

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A21.  The 27 piece checks (`Checks/P00.lean` … `P54.lean`, one
`native_decide` each: lane A9's checker `bandOK` on the 935 boxes of the n ≥ 44 strip — 26 strips of lane R4X's
`atlas44_trial` trimmed to `[floor, cap]`, and the strip `[6/5, 49/40]` built by this lane with a byte-identical copy of R4X's
constructor — with the piece's caps and the box tail base `lamBox`) are collected (`strip44Checks`) and combined with
`N45.explicitThreshold_small_P45` by the standard-axiom glue of `Strip.lean`:

* **`explicitThreshold_small_P44`**: T1's explicit threshold for `P44` at every activity in range and every
  `P44.mfloor t ≤ m < 400`;
* **`thresholdNoValley_P44 : ThresholdNoValley P44`** (O4 for `P44`).

Trust: the 27 new piece checks and the inherited checks are `native_decide`; everything else uses `propext`,
`Classical.choice`, `Quot.sound`.

Scalarity check: no new scalar; see `Strip.lean`.
-/

namespace Erdos993Lean.Analytic.N44

open Erdos993Lean.Analytic.Atlas Erdos993Lean.Analytic.N44.Checks

/-- **The 27 n ≥ 44 piece checks** (`[floor(n ≥ 44), floor(n ≥ 45)]` on every piece whose floor drops; box tail base
`lamBox`). -/
theorem strip44Checks : ∀ p < 55, Data.mmin44.getD p 0 < Data.piece44Cap p →
    bandOK (Data.piece44Band p) lamBox (Data.piece44Cap p) (Data.strip44Boxes p) (Data.strip44Slabs p) = true := by
  intro p hp h
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
  · exact checkP13
  · exact checkP14
  · exact checkP15
  · exact checkP16
  · exact checkP17
  · exact checkP18
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
  · exact checkP31
  · exact checkP32
  · exact checkP33
  · exact checkP34
  · exact checkP35
  · exact absurd h (by decide +kernel)
  · exact absurd h (by decide +kernel)
  · exact absurd h (by decide +kernel)
  · exact absurd h (by decide +kernel)
  · exact absurd h (by decide +kernel)
  · exact absurd h (by decide +kernel)
  · exact absurd h (by decide +kernel)
  · exact checkP43
  · exact checkP44
  · exact absurd h (by decide +kernel)
  · exact absurd h (by decide +kernel)
  · exact absurd h (by decide +kernel)
  · exact absurd h (by decide +kernel)
  · exact absurd h (by decide +kernel)
  · exact absurd h (by decide +kernel)
  · exact absurd h (by decide +kernel)
  · exact absurd h (by decide +kernel)
  · exact absurd h (by decide +kernel)
  · exact checkP54

/-- **T1's explicit threshold for `P44` on bounded `m`** (the n ≥ 44 strip, then `P45`). -/
theorem explicitThreshold_small_P44 :
    ∀ t, InRange t → ∀ m, P44.mfloor t ≤ m → m < 400 →
      ExplicitThreshold (actQ t) m (P44.θb t) (P44.Db t) (P44.Tb t m) (P44.M1b t m) :=
  explicitThreshold_small_P44_of_checks Data.strip44Boxes Data.strip44Slabs strip44Checks
    N45.explicitThreshold_small_P45

/-- **O4 for `P44`** (`ThresholdNoValley P44`). -/
theorem thresholdNoValley_P44 : ThresholdNoValley P44 :=
  thresholdNoValley_P44_of explicitThreshold_small_P44

end Erdos993Lean.Analytic.N44
