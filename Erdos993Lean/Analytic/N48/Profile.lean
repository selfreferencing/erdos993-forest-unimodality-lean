import Erdos993Lean.Analytic.N48.Pieces
import Erdos993Lean.Analytic.N52.Profile

/-!
# The profile of the analytic route at `n ≥ 48`

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A20.  Sources: lane R4X's `LEAN/r4x/REACH_BELOW_52.md` §5 (the
step `N = 48`: four O3 rows at `t = 0` on sub-bands of bands 23 and 26, the O5 table on the sub-band edges), lane A19's
profile `P52` (`Erdos993Lean/Analytic/N52/Profile.lean`), lane A9's actual-activity tail `Atlas.tailFnAct`.

* `tailFn48 t m r`: lane A9's `tailFnAct t m r`, and on the four pieces with a new O3 row (pieces 22, 26, 27, 28:
  `[13/10, 27/20]`, `[8/5, 33/20]`, `[33/20, 17/10]`, `[17/10, 7/4]`) its minimum with the new term
  `e^{−ℓ_new m} (1 + t)^r` (the Laplace parameter `t_0 = 0`).  So `tailFn48 ≤ tailFnAct` everywhere
  (`tailFn48_le_act`), and on the new pieces also `tailFn48 ≤ e^{−ℓ_new m} (1 + t)^r` (`tailFn48_le_new`).
* **`P48`**: lane A9's `P30act` (Profile30's `θ`, `D`, `M1`) with the tail `tailFn48` and the floor `mmin48` of the
  piece of `t` (`N48/Data/Params.lean`).

Scalarity check: `tailFn48` is the bound on the lower tail `P(M ≤ r)` of the free count `M` (O3); its new rate
`ℓ_new` summarizes the Laplace transform of `M` at `t = 0`, `E (1 − q)^M ≤ e^{−ℓ_new m}`, certified on each of the four
pieces by lane A10's checker (`N48/Tail.lean`), and is consumed by O4 (the strips and T1); `mmin48_p` is the floor of
the expected free count `m = E M` on piece `p` (produced by O5 at `n ≥ 48`, `N48/Density.lean`; consumed by O4 as the
`m`-range of the strips).  `θ`, `D`, `M1` are Profile30's objects, unchanged.
-/

namespace Erdos993Lean.Analytic.N48

open Profile30

/-- The new O3 rate at `t = 0` of the piece of `t` as a real number (`0`: none). -/
noncomputable def newEllR (t : ℝ) : ℝ := ((Data.newEll.getD (pieceOf t) 0 : ℚ) : ℝ)

/-- **The lower-tail function at `n ≥ 48`**: lane A9's actual-activity tail, and on the four pieces with a new O3 row
its minimum with `e^{−ℓ_new m} (1 + t)^r`. -/
noncomputable def tailFn48 (t m : ℝ) (r : ℕ) : ℝ :=
  if Data.newEll.getD (pieceOf t) 0 = 0 then Atlas.tailFnAct t m r
  else min (Atlas.tailFnAct t m r) (Real.exp (-(newEllR t * m)) * (1 + t) ^ r)

theorem tailFn48_le_act (t m : ℝ) (r : ℕ) : tailFn48 t m r ≤ Atlas.tailFnAct t m r := by
  unfold tailFn48
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem tailFn48_le_new {t : ℝ} (h : Data.newEll.getD (pieceOf t) 0 ≠ 0) (m : ℝ) (r : ℕ) :
    tailFn48 t m r ≤ Real.exp (-(newEllR t * m)) * (1 + t) ^ r := by
  unfold tailFn48
  rw [if_neg h]
  exact min_le_right _ _

theorem tailFn48_le_one (t m : ℝ) (r : ℕ) : tailFn48 t m r ≤ 1 :=
  (tailFn48_le_act t m r).trans (min_le_left _ _)

/-- **The profile of the route at `n ≥ 48`**: lane A9's `P30act` (Profile30's `θ`, `D`, `M1`) with the tail
`tailFn48` and the floor of `m` of the piece of `t` at `n ≥ 48`. -/
noncomputable def P48 : Profile :=
  { Atlas.P30act with Tb := tailFn48, mfloor := fun t => ((Data.mmin48.getD (pieceOf t) 0 : ℚ) : ℝ) }

theorem P48_θb : P48.θb = N52.P52.θb := rfl

theorem P48_Db : P48.Db = N52.P52.Db := rfl

theorem P48_M1b : P48.M1b = N52.P52.M1b := rfl

theorem P48_Tb : P48.Tb = tailFn48 := rfl

theorem P48_mfloor (t : ℝ) : P48.mfloor t = ((Data.mmin48.getD (pieceOf t) 0 : ℚ) : ℝ) := rfl

/-- `P48` and lane A19's `P52` agree except for the tail and the floor. -/
theorem P48_eq_P52 : { P48 with Tb := N52.P52.Tb, mfloor := N52.P52.mfloor } = N52.P52 := rfl

end Erdos993Lean.Analytic.N48
