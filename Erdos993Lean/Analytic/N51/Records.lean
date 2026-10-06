import Erdos993Lean.Analytic.Density.Records

/-!
# Two more density records: `x = 57/50` and `x = 7/5`

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A20.  Sources: lane R4X's `LEAN/r4x/REACH_BELOW_52.md` §5(d)
(the records the analytic floor needs below `n = 52`), Soul's `SOUL/O6_O5/density_certified.json` (the 106 certified
records; copied as `LEAN/r4x/density_certified.json`) and R4X's `LEAN/r4x/trial_records.json` (trial records built by
R4X's constructor and accepted by the verbatim O5 checker).  The record structure and its finite conditions are lane
A8's (`Erdos993Lean/Analytic/Density/Record.lean`); each record here is proved exactly as `rec1`, `rec11` are
(`constructor <;> decide +kernel`).

* **`rec5750`** (`x = 57/50`): Soul's certified record, verbatim (`r, s0, g, B0, h`); `r` equals the path density
  `ρ(57/50)` to `6·10⁻¹⁰`.
* **`rec75`** (`x = 7/5`): R4X's trial record with `r, s0, g, B0` verbatim and the boundary of the forests with at
  least eight vertices lowered from R4X's `h = 100244105381/(5·10¹¹) ≈ 0.20049` to `h = 93/500 = 0.186`.  Reason:
  above `x ≈ 1.16` the constructor's `r` lies below the path density (`ρ(7/5) − r ≈ 1.9·10⁻³`), and R4X's
  `h = μ(P₈) − 8r` exceeds the limit `c∞ = (1 + 2x − s)/s² ≈ 0.18651` (`s = √(1 + 4x)`) of `μ(P_j) − ρ j`; the Lean
  path tail (`Density.path_tail`) needs `h < c∞` (the condition `K_c` of `Record.Valid`).  The O5 table at
  `n ≥ 51` needs `h ≥ 0.0995` on band 26 and `h ≥ 0.1265` on band 30 (`N51/Density.lean`), so `93/500` suffices.
* The path-tail parameters `sH, sL` (rational bounds of `√(1 + 4x)`), `K`, `N₀` are the lane's.
* `hardCoreMean_ge_rec5750`, `hardCoreMean_ge_rec75`: `μ_F(x) ≥ r n + h` for every forest with `n ≥ 8`.

Scalarity check: each record summarizes one object, the hard-core mean `μ_F(x)` of every forest at the activity `x`,
as the affine lower bound `r n + h` (produced by lane A8's density induction from the finite conditions below;
consumed by the O5 rank table at `n ≥ 51`, `N51/Density.lean`, through the activity transfer `le_of_transfer`).
-/

namespace Erdos993Lean.Analytic.N51

open Density

/-- Soul's certified density record at `x = 57/50` (`SOUL/O6_O5/density_certified.json`, verbatim). -/
def rec5750 : Record where
  x := 57 / 50
  r := 287952767 / 1000000000
  s0 := 2443936553 / 20500000000
  g := 914280918751 / 5911750000000
  B0 := 68938166775582777 / 390116382500000000
  h := 1950136275417533 / 11794887625000000
  sH := 1179 / 500
  sL := 23579 / 10000
  K := 1600
  N0 := 15

/-- R4X's trial density record at `x = 7/5` (`LEAN/r4x/trial_records.json`: `r, s0, g, B0` verbatim), with the
boundary `h` of the forests with at least eight vertices lowered to `93/500` (below `c∞(7/5) ≈ 0.18651`). -/
def rec75 : Record where
  x := 7 / 5
  r := 303496503 / 1000000000
  s0 := 1233566443 / 9500000000
  g := 7081585161 / 40000000000
  B0 := 103381134257 / 500000000000
  h := 93 / 500
  sH := 25691 / 10000
  sL := 2569 / 1000
  K := 1600
  N0 := 15

/-- The record at `x = 57/50` satisfies every finite condition (kernel `decide`). -/
theorem rec5750_valid : rec5750.Valid := by
  constructor <;> decide +kernel

/-- The record at `x = 7/5` satisfies every finite condition (kernel `decide`). -/
theorem rec75_valid : rec75.Valid := by
  constructor <;> decide +kernel

/-- **The density record at `x = 57/50`**: `μ_F(57/50) ≥ r n + h` for every forest with `n ≥ 8`
(`r = 0.287952767`, `h = 0.16533…`). -/
theorem hardCoreMean_ge_rec5750 (F : FiniteForest) (hn : 8 ≤ F.n) :
    ((287952767 / 1000000000 : ℚ) : ℝ) * F.n + ((1950136275417533 / 11794887625000000 : ℚ) : ℝ) ≤
      hardCoreMean F ((57 / 50 : ℚ) : ℝ) := by
  have h := rec5750_valid.hardCoreMean_ge F hn
  simpa [rec5750] using h

/-- **The density record at `x = 7/5`**: `μ_F(7/5) ≥ r n + h` for every forest with `n ≥ 8`
(`r = 0.303496503`, `h = 0.186`). -/
theorem hardCoreMean_ge_rec75 (F : FiniteForest) (hn : 8 ≤ F.n) :
    ((303496503 / 1000000000 : ℚ) : ℝ) * F.n + ((93 / 500 : ℚ) : ℝ) ≤
      hardCoreMean F ((7 / 5 : ℚ) : ℝ) := by
  have h := rec75_valid.hardCoreMean_ge F hn
  simpa [rec75] using h

end Erdos993Lean.Analytic.N51
