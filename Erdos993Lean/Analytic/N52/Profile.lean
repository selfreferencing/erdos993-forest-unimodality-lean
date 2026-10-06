import Erdos993Lean.Analytic.Atlas.Profile

/-!
# The profile of the analytic route at `n ≥ 52`

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A19.  Sources: lane R52's `LEAN/r52/REQUIREMENTS_52.md` §1
(the O5 band rule `K(a, N) = max(⌈N/4⌉ + 1, max_{x ≤ a} ⌈√(q_a/q_x)(r_x N + h_x)⌉)` re-evaluated at `N = 52` with the
two density records in Lean, `x = 1` and `x = 11/10`), `Erdos993Lean/Analytic/Profile30.lean` (the band edges and
the caps `θ`, `D`, the O3 rates), lane A9's `Atlas.tailFnAct` (`Erdos993Lean/Analytic/Atlas/Profile.lean`: the
lower-tail function with the actual activity in the Laplace base, lane A3's `Tail.tail_t3` form).

* `kmin52`: the integer rank of each band at `n ≥ 52`: `14` on bands 1–15 (`k > ⌈52/4⌉ = 13`), `15` on 16–18, `16` on
  19–24, `17` on 25–29, `18` on 30 (the density records; `Density52.band_checks52`).
* `mmin52`: the floor of the expected free count, `mmin52_i = k_i / (2 q(λ_{i+1}))` (`mmin52_eq`).
* **`P52`**: Profile30's `θ`, `D` and tail cutoff `M1 = ⌈m⌉ + 1`, the actual-activity tail `tailFnAct`
  (`P30act`'s), and the floor `mmin52` of its band.  It differs from lane A9's `Atlas.P30act` only in the floor
  (`P52_θb`, `P52_Db`, `P52_Tb`, `P52_M1b`).

Scalarity check: `kmin52_i` summarizes the hard-core mean `μ_F(t) = k` at an interior rank of a forest with
`n ≥ 52` on band `i` (produced by the rank condition and the density records, `Density52`), `mmin52_i` the expected
free count `m = E M ≥ k/(2q)` (consumed by the no-valley numerics O4 through `P52.mfloor`: the new strip atlas
below Profile30's floor, lane A9's atlas above).  The other fields are Profile30's objects (O1's `D`, O2's `θ`, O3's
rates), unchanged.
-/

namespace Erdos993Lean.Analytic.N52

open Profile30

/-- The integer rank of band `i` (0-based) at `n ≥ 52`. -/
def kmin52 : List ℕ :=
  [14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14,
    15, 15, 15, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 18]

/-- The floor of `m` at `n ≥ 52` per band (0-based). -/
def mmin52 : List ℚ :=
  [238/9, 49/2, 203/9, 21, 217/11, 56/3, 231/13, 17, 49/3, 63/4, 46/3, 329/22, 336/23, 343/24, 14,
    765/52, 130/9, 795/56, 432/29, 44/3, 72/5, 184/13, 96/7, 40/3, 221/16, 187/14, 493/38, 1037/82,
    221/18, 90/7]

theorem kmin52_length : kmin52.length = 30 := by decide

theorem mmin52_length : mmin52.length = 30 := by decide

/-- `mmin52_i = k_i / (2 q(λ_{i+1}))` on every band (kernel `decide`). -/
theorem mmin52_eq : ∀ i < 30, mmin52.getD i 0 =
    (kmin52.getD i 0 : ℚ) / (2 * (edges.getD (i + 1) 0 / (1 + edges.getD (i + 1) 0))) := by
  decide +kernel

/-- The floor at `n ≥ 52` lies below Profile30's floor at `n ≥ 61`, band by band (kernel `decide`). -/
theorem mmin52_le_mmin : ∀ i < 30, mmin52.getD i 0 ≤ mmin.getD i 0 := by
  decide +kernel

/-- **The profile of the route at `n ≥ 52`**: lane A9's `P30act` (Profile30's `θ`, `D`, `M1` and the
actual-activity tail) with the floor of `m` at `n ≥ 52`. -/
noncomputable def P52 : Profile :=
  { Atlas.P30act with mfloor := fun t => ((mmin52.getD (bandOf t) 0 : ℚ) : ℝ) }

theorem P52_θb : P52.θb = Profile30.P.θb := rfl

theorem P52_Db : P52.Db = Profile30.P.Db := rfl

theorem P52_Tb : P52.Tb = Atlas.tailFnAct := rfl

theorem P52_M1b : P52.M1b = Profile30.P.M1b := rfl

theorem P52_mfloor (t : ℝ) : P52.mfloor t = ((mmin52.getD (bandOf t) 0 : ℚ) : ℝ) := rfl

/-- `P52` and lane A9's `P30act` agree except for the floor. -/
theorem P52_eq_P30act : { P52 with mfloor := Profile30.P.mfloor } = Atlas.P30act := rfl

/-- The floor of `P52` is at most Profile30's. -/
theorem P52_mfloor_le {t : ℝ} (ht : InRange t) : P52.mfloor t ≤ Profile30.P.mfloor t := by
  have hi := (Atlas.bandOf_spec ht).1
  have h := mmin52_le_mmin (bandOf t) hi
  show ((mmin52.getD (bandOf t) 0 : ℚ) : ℝ) ≤ ((mmin.getD (bandOf t) 0 : ℚ) : ℝ)
  exact_mod_cast h

end Erdos993Lean.Analytic.N52
