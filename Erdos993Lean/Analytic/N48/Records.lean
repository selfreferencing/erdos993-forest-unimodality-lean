import Erdos993Lean.Analytic.N51.Records

/-!
# One more density record: `x = 23/25`

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A20.  Sources: Soul's `SOUL/O6_O5/density_certified.json` (the
106 certified records; copied as `LEAN/r4x/density_certified.json`), lane A8's record structure
(`Erdos993Lean/Analytic/Density/Record.lean`).  The record is proved exactly as `rec1`, `rec11`
(`constructor <;> decide +kernel`).

* **`rec2325`** (`x = 23/25`): Soul's certified record, verbatim (`r, s0, g, B0, h`; `r` equals the path density
  `ρ(23/25)` to `10⁻⁹`).  The path-tail parameters are the lane's: `sH, sL` (rational bounds of `√(1 + 4x)`) and
  `K = 3200`, `N₀ = 16` (the gap `c∞ − h ≈ 2.1·10⁻⁴` is smaller than for `x = 1`, so `K = 1600` does not suffice).
* `hardCoreMean_ge_rec2325`: `μ_F(23/25) ≥ r n + h` for every forest with `n ≥ 8`.

Why it is needed (not in lane R4X's work order §5(d)): at `n ≥ 48` the Lean records `x = 1, 11/10, 57/50, 7/5` give
the rank `13` on bands 14 and 15 (`λ ∈ [23/25, 1]`), below the rank `14` of R4X's configuration (its atlas has no
strip there); `x = 23/25` gives `14` on both (`√(q_a/q_x) L = 14.050` and `14.194`, `N48/Density.lean`).

Scalarity check: the record summarizes one object, the hard-core mean `μ_F(23/25)` of every forest, as the affine
lower bound `r n + h` (produced by lane A8's density induction from the finite conditions; consumed by the O5 rank
table at `n ≥ 48`).
-/

namespace Erdos993Lean.Analytic.N48

open Density

/-- Soul's certified density record at `x = 23/25` (`SOUL/O6_O5/density_certified.json`, verbatim). -/
def rec2325 : Record where
  x := 23 / 25
  r := 134437459 / 500000000
  s0 := 1954940411 / 17750000000
  g := 2427130781 / 17625000000
  B0 := 14887779706201 / 93600500000000
  h := 31928273757431 / 221143187500000
  sH := 10817 / 5000
  sL := 21633 / 10000
  K := 3200
  N0 := 16

/-- The record at `x = 23/25` satisfies every finite condition (kernel `decide`). -/
theorem rec2325_valid : rec2325.Valid := by
  constructor <;> decide +kernel

/-- **The density record at `x = 23/25`**: `μ_F(23/25) ≥ r n + h` for every forest with `n ≥ 8`
(`r = 0.268874918`, `h = 0.14437…`). -/
theorem hardCoreMean_ge_rec2325 (F : FiniteForest) (hn : 8 ≤ F.n) :
    ((134437459 / 500000000 : ℚ) : ℝ) * F.n + ((31928273757431 / 221143187500000 : ℚ) : ℝ) ≤
      hardCoreMean F ((23 / 25 : ℚ) : ℝ) := by
  have h := rec2325_valid.hardCoreMean_ge F hn
  simpa [rec2325] using h

end Erdos993Lean.Analytic.N48
