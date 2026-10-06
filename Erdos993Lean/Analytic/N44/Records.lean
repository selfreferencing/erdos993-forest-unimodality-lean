import Erdos993Lean.Analytic.N51.Records

/-!
# One more density record: `x = 8/5`

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A21.  Sources: lane R4X's trial record at `x = 8/5`
(`LEAN/r4x/trial_records.json`: `r, s0, g, B0` verbatim, built by R4X's constructor and accepted by the verbatim O5
checker), lane A8's record structure (`Erdos993Lean/Analytic/Density/Record.lean`), lane A20's `N51.rec75` (the same
correction: the boundary `h` lowered below `c∞`).  The record is proved exactly as `rec1`, `rec11`
(`constructor <;> decide +kernel`).

* **`rec85`** (`x = 8/5`): R4X's trial constants `r = 0.312643678`, `s0`, `g`, `B0` verbatim, with the boundary of the
  forests with at least eight vertices lowered from R4X's `h = 226737850483/10¹² ≈ 0.22674` to `h = 1999/10000`, just
  below the limit `c∞(8/5) = (1 + 2x − s)/s² ≈ 0.199960` (`s = √(1 + 4x)`): above `x ≈ 1.16` the constructor's `r` lies
  below the path density and `h = μ(P₈) − 8r` exceeds `c∞`, while the Lean path tail (`Density.path_tail`) needs
  `h < c∞` (the condition `K_c` of `Record.Valid`).  With the gap `c∞ − h ≈ 6·10⁻⁵`, the tail constant is `K = 6400`,
  `N₀ = 17`; `sH, sL` are rational bounds of `√(1 + 4x) = √(33/5)`.
* `hardCoreMean_ge_rec85`: `μ_F(8/5) ≥ r n + h` for every forest with `n ≥ 8`.

Why it is needed (`REACH_BELOW_52.md` §5(d) lists no record for the `N = 44` step because R4X's floors used trial records
with their full `h`): at `n ≥ 44` the Lean records `x = 1, 11/10, 57/50, 7/5, 23/25` give the rank `14` on the piece
`[33/20, 17/10]` of band 26 (floor `189/17`), where R4X's configuration needs `15` (floor `405/34`; the fine-box LP fails
at `189/17` by `0.054`, `LEAN/lanes/A21/scratch/config_check44.out`); `x = 8/5` gives `15`
(`√(q_a/q_x) L = 14.038 > 14`, `N44/Density.lean`).  It is the only record the step `N = 44` needs beyond lane A20's.

Scalarity check: the record summarizes one object, the hard-core mean `μ_F(8/5)` of every forest, as the affine lower
bound `r n + h` (produced by lane A8's density induction from the finite conditions; consumed by the O5 rank table at
`n ≥ 44`).
-/

namespace Erdos993Lean.Analytic.N44

open Density

/-- R4X's trial density record at `x = 8/5` (`LEAN/r4x/trial_records.json`: `r, s0, g, B0` verbatim), with the
boundary `h` of the forests with at least eight vertices lowered to `1999/10000` (below `c∞(8/5) ≈ 0.199960`). -/
def rec85 : Record where
  x := 8 / 5
  r := 156321839 / 500000000
  s0 := 717241381 / 5250000000
  g := 192396110281 / 1000000000000
  B0 := 45646574327 / 200000000000
  h := 1999 / 10000
  sH := 27203 / 10000
  sL := 13601 / 5000
  K := 6400
  N0 := 17

/-- The record at `x = 8/5` satisfies every finite condition (kernel `decide`). -/
theorem rec85_valid : rec85.Valid := by
  constructor <;> decide +kernel

/-- **The density record at `x = 8/5`**: `μ_F(8/5) ≥ r n + h` for every forest with `n ≥ 8`
(`r = 0.312643678`, `h = 0.1999`). -/
theorem hardCoreMean_ge_rec85 (F : FiniteForest) (hn : 8 ≤ F.n) :
    ((156321839 / 500000000 : ℚ) : ℝ) * F.n + ((1999 / 10000 : ℚ) : ℝ) ≤
      hardCoreMean F ((8 / 5 : ℚ) : ℝ) := by
  have h := rec85_valid.hardCoreMean_ge F hn
  simpa [rec85] using h

end Erdos993Lean.Analytic.N44
