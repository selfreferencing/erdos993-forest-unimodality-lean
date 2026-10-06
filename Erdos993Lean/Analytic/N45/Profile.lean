import Erdos993Lean.Analytic.N45.Pieces
import Erdos993Lean.Analytic.N48.Profile

/-!
# The profile of the analytic route at `n ≥ 45`

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A21.  Sources: lane R4X's `LEAN/r4x/REACH_BELOW_52.md` §5 and its
final configuration `config_N45_min.json` (the step `N = 45`: O1 refits `D = 13/10` on band 23 and `D = 7/5` on
`[8/5, 33/20]`, the O2 refit `θ = 19/20` on `[33/20, 7/4]`, twelve O3 rows at `t = 0`, floor splits), lane A20's profile
`P48` (`N48/Profile.lean`), lane A19's `P52`, lane A9's `P30act`.

* `thetaR t`, `DR t`: the caps of the piece of `t` (`N45/Data/Params.lean`: the configuration's refits, else the parent
  band's Profile30 caps).  They are at most Profile30's (`P45_θb_le`, `P45_Db_le`) and nonnegative.
* `tailFn45 t m r`: lane A20's `tailFn48 t m r`, and on the pieces with a ladder O3 row its minimum with the new term
  `e^{−ℓ_new m} (1 + t)^r` (the Laplace parameter `t_0 = 0`).  So `tailFn45 ≤ tailFn48` everywhere
  (`tailFn45_le_48`), and on the new pieces also `tailFn45 ≤ e^{−ℓ_new m} (1 + t)^r` (`tailFn45_le_new`).
* **`P45`**: the profile with the piece-wise caps, the tail `tailFn45`, Profile30's tail cutoff `M1 = ⌈m⌉ + 1` and the
  floor `mmin45` of the piece of `t`.

Scalarity check: `thetaR` is O2's cap on the second moment of `δ` (through `V ≤ (1 + θ)(1 − q) W`), produced by the
O2 rows (lane A16's ledger; the O2R1 row on `[33/20, 7/4]`) and consumed by O4; `DR` is O1's cap on `Var M / E M`
(the O1 rows; O1R1, O1R2 on the refit pieces); `tailFn45` bounds the lower tail `P(M ≤ r)` of the free count `M` (O3),
its new rates summarizing the Laplace transform of `M` at `t = 0` on the ladder pieces (`N45/Tail.lean`); `mmin45_p` is
the floor of `m = E M` on piece `p` (O5, `N45/Density.lean`).  All are consumed by O4 (`N45/Strip.lean`).
-/

namespace Erdos993Lean.Analytic.N45

open Profile30

/-- The O2 cap `θ` of the piece of `t` as a real number. -/
noncomputable def thetaR (t : ℝ) : ℝ := ((Data.theta45.getD (pieceOf t) 0 : ℚ) : ℝ)

/-- The O1 cap `D` of the piece of `t` as a real number. -/
noncomputable def DR (t : ℝ) : ℝ := ((Data.D45.getD (pieceOf t) 0 : ℚ) : ℝ)

/-- The ladder O3 rate at `t = 0` of the piece of `t` as a real number (`0`: none). -/
noncomputable def newEllR (t : ℝ) : ℝ := ((Data.newEll.getD (pieceOf t) 0 : ℚ) : ℝ)

/-- **The lower-tail function at `n ≥ 45`**: lane A20's tail, and on the pieces with a ladder O3 row its minimum with
`e^{−ℓ_new m} (1 + t)^r`. -/
noncomputable def tailFn45 (t m : ℝ) (r : ℕ) : ℝ :=
  if Data.newEll.getD (pieceOf t) 0 = 0 then N48.tailFn48 t m r
  else min (N48.tailFn48 t m r) (Real.exp (-(newEllR t * m)) * (1 + t) ^ r)

theorem tailFn45_le_48 (t m : ℝ) (r : ℕ) : tailFn45 t m r ≤ N48.tailFn48 t m r := by
  unfold tailFn45
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem tailFn45_le_new {t : ℝ} (h : Data.newEll.getD (pieceOf t) 0 ≠ 0) (m : ℝ) (r : ℕ) :
    tailFn45 t m r ≤ Real.exp (-(newEllR t * m)) * (1 + t) ^ r := by
  unfold tailFn45
  rw [if_neg h]
  exact min_le_right _ _

theorem tailFn45_le_act (t m : ℝ) (r : ℕ) : tailFn45 t m r ≤ Atlas.tailFnAct t m r :=
  (tailFn45_le_48 t m r).trans (N48.tailFn48_le_act t m r)

theorem tailFn45_le_one (t m : ℝ) (r : ℕ) : tailFn45 t m r ≤ 1 :=
  (tailFn45_le_48 t m r).trans (N48.tailFn48_le_one t m r)

/-- **The profile of the route at `n ≥ 45`**: the piece-wise caps `θ`, `D` of the final configuration, the tail
`tailFn45`, Profile30's tail cutoff and the floor of `m` of the piece of `t` at `n ≥ 45`. -/
noncomputable def P45 : Profile :=
  { θb := thetaR
    Db := DR
    Tb := tailFn45
    M1b := Profile30.P.M1b
    mfloor := fun t => ((Data.mmin45.getD (pieceOf t) 0 : ℚ) : ℝ) }

theorem P45_θb (t : ℝ) : P45.θb t = ((Data.theta45.getD (pieceOf t) 0 : ℚ) : ℝ) := rfl

theorem P45_Db (t : ℝ) : P45.Db t = ((Data.D45.getD (pieceOf t) 0 : ℚ) : ℝ) := rfl

theorem P45_Tb : P45.Tb = tailFn45 := rfl

theorem P45_M1b : P45.M1b = N48.P48.M1b := rfl

theorem P45_mfloor (t : ℝ) : P45.mfloor t = ((Data.mmin45.getD (pieceOf t) 0 : ℚ) : ℝ) := rfl

/-- The caps are nonnegative and at most the parent band's (kernel `decide`). -/
theorem theta45_bounds : ∀ p < 46, 0 ≤ Data.theta45.getD p 0 ∧
    Data.theta45.getD p 0 ≤ θt.getD (Data.pieceParent.getD p 0) 1 := by
  decide +kernel

theorem D45_bounds : ∀ p < 46, 0 ≤ Data.D45.getD p 0 ∧
    Data.D45.getD p 0 ≤ Dt.getD (Data.pieceParent.getD p 0) (8 / 5) := by
  decide +kernel

theorem mmin45_pos : ∀ p < 46, 0 < Data.mmin45.getD p 0 := by decide +kernel

/-- `θ` at `n ≥ 45` is at most Profile30's `θ` (the parent band's). -/
theorem P45_θb_le {t : ℝ} (ht : InRange t) : P45.θb t ≤ Profile30.P.θb t := by
  obtain ⟨hp, hpar, -, -⟩ := pieceOf_spec ht
  have h := (theta45_bounds _ hp).2
  rw [hpar] at h
  show ((Data.theta45.getD (pieceOf t) 0 : ℚ) : ℝ) ≤ ((θt.getD (bandOf t) 1 : ℚ) : ℝ)
  exact_mod_cast h

theorem P45_θb_nonneg {t : ℝ} (ht : InRange t) : 0 ≤ P45.θb t := by
  have h := (theta45_bounds _ (pieceOf_spec ht).1).1
  show (0 : ℝ) ≤ ((Data.theta45.getD (pieceOf t) 0 : ℚ) : ℝ)
  exact_mod_cast h

/-- `D` at `n ≥ 45` is at most Profile30's `D` (the parent band's). -/
theorem P45_Db_le {t : ℝ} (ht : InRange t) : P45.Db t ≤ Profile30.P.Db t := by
  obtain ⟨hp, hpar, -, -⟩ := pieceOf_spec ht
  have h := (D45_bounds _ hp).2
  rw [hpar] at h
  show ((Data.D45.getD (pieceOf t) 0 : ℚ) : ℝ) ≤ ((Dt.getD (bandOf t) (8 / 5) : ℚ) : ℝ)
  exact_mod_cast h

theorem P45_Db_nonneg {t : ℝ} (ht : InRange t) : 0 ≤ P45.Db t := by
  have h := (D45_bounds _ (pieceOf_spec ht).1).1
  show (0 : ℝ) ≤ ((Data.D45.getD (pieceOf t) 0 : ℚ) : ℝ)
  exact_mod_cast h

theorem P45_mfloor_nonneg {t : ℝ} (ht : InRange t) : 0 ≤ P45.mfloor t := by
  have h := mmin45_pos _ (pieceOf_spec ht).1
  rw [P45_mfloor]
  exact_mod_cast h.le

end Erdos993Lean.Analytic.N45
