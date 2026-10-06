import Erdos993Lean.Analytic.N44.Pieces
import Erdos993Lean.Analytic.N45.Profile

/-!
# The profile of the analytic route at `n ≥ 44`

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A21.  Sources: lane R4X's `LEAN/r4x/REACH_BELOW_52.md` §5 and its
final configuration `config_N44_final.json` (the step `N = 44`: the O1 refit `D = 11/10` on `[22/25, 47/50]`, the O2 refits
`θ = 9/10` on `[8/5, 33/20]` and `θ = 13/20` on `[39/50, 4/5]`, ten more O3 rows at `t = 0`, floor splits), this lane's
profile `P45` (`N45/Profile.lean`).

* `thetaR t`, `DR t`: the caps of the piece of `t` (`N44/Data/Params.lean`).  They are at most those of `P45` on the
  containing piece (`P44_θb_le`, `P44_Db_le`) and nonnegative.
* `tailFn44 t m r`: `tailFn45 t m r`, and on the pieces with a ladder O3 row its minimum with the new term
  `e^{−ℓ_new m} (1 + t)^r`; so `tailFn44 ≤ tailFn45` (`tailFn44_le_45`) and `tailFn44 ≤ e^{−ℓ_new m} (1 + t)^r` on
  the rows (`tailFn44_le_new`).
* **`P44`**: the profile with the piece-wise caps, the tail `tailFn44`, Profile30's tail cutoff and the floor `mmin44`
  of the piece of `t`.

Scalarity check: as `N45/Profile.lean`, with the O2R2, O2R3 rows and the O1R3 row on the new refit pieces.
-/

namespace Erdos993Lean.Analytic.N44

open Profile30

/-- The O2 cap `θ` of the piece of `t` as a real number. -/
noncomputable def thetaR (t : ℝ) : ℝ := ((Data.theta44.getD (pieceOf t) 0 : ℚ) : ℝ)

/-- The O1 cap `D` of the piece of `t` as a real number. -/
noncomputable def DR (t : ℝ) : ℝ := ((Data.D44.getD (pieceOf t) 0 : ℚ) : ℝ)

/-- The ladder O3 rate at `t = 0` of the piece of `t` as a real number (`0`: none). -/
noncomputable def newEllR (t : ℝ) : ℝ := ((Data.newEll.getD (pieceOf t) 0 : ℚ) : ℝ)

/-- **The lower-tail function at `n ≥ 44`**: the tail at `n ≥ 45`, and on the pieces with a ladder O3 row its minimum
with `e^{−ℓ_new m} (1 + t)^r`. -/
noncomputable def tailFn44 (t m : ℝ) (r : ℕ) : ℝ :=
  if Data.newEll.getD (pieceOf t) 0 = 0 then N45.tailFn45 t m r
  else min (N45.tailFn45 t m r) (Real.exp (-(newEllR t * m)) * (1 + t) ^ r)

theorem tailFn44_le_45 (t m : ℝ) (r : ℕ) : tailFn44 t m r ≤ N45.tailFn45 t m r := by
  unfold tailFn44
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem tailFn44_le_new {t : ℝ} (h : Data.newEll.getD (pieceOf t) 0 ≠ 0) (m : ℝ) (r : ℕ) :
    tailFn44 t m r ≤ Real.exp (-(newEllR t * m)) * (1 + t) ^ r := by
  unfold tailFn44
  rw [if_neg h]
  exact min_le_right _ _

theorem tailFn44_le_act (t m : ℝ) (r : ℕ) : tailFn44 t m r ≤ Atlas.tailFnAct t m r :=
  (tailFn44_le_45 t m r).trans (N45.tailFn45_le_act t m r)

theorem tailFn44_le_one (t m : ℝ) (r : ℕ) : tailFn44 t m r ≤ 1 :=
  (tailFn44_le_45 t m r).trans (N45.tailFn45_le_one t m r)

/-- **The profile of the route at `n ≥ 44`**. -/
noncomputable def P44 : Profile :=
  { θb := thetaR
    Db := DR
    Tb := tailFn44
    M1b := Profile30.P.M1b
    mfloor := fun t => ((Data.mmin44.getD (pieceOf t) 0 : ℚ) : ℝ) }

theorem P44_θb (t : ℝ) : P44.θb t = ((Data.theta44.getD (pieceOf t) 0 : ℚ) : ℝ) := rfl

theorem P44_Db (t : ℝ) : P44.Db t = ((Data.D44.getD (pieceOf t) 0 : ℚ) : ℝ) := rfl

theorem P44_Tb : P44.Tb = tailFn44 := rfl

theorem P44_M1b : P44.M1b = N45.P45.M1b := rfl

theorem P44_mfloor (t : ℝ) : P44.mfloor t = ((Data.mmin44.getD (pieceOf t) 0 : ℚ) : ℝ) := rfl

/-- The caps are nonnegative and at most those of the containing n ≥ 45 piece (kernel `decide`). -/
theorem theta44_bounds : ∀ p < 55, 0 ≤ Data.theta44.getD p 0 ∧
    Data.theta44.getD p 0 ≤ N45.Data.theta45.getD (Data.pieceUp.getD p 0) 0 := by
  decide +kernel

theorem D44_bounds : ∀ p < 55, 0 ≤ Data.D44.getD p 0 ∧
    Data.D44.getD p 0 ≤ N45.Data.D45.getD (Data.pieceUp.getD p 0) 0 := by
  decide +kernel

theorem mmin44_pos : ∀ p < 55, 0 < Data.mmin44.getD p 0 := by decide +kernel

/-- `θ` at `n ≥ 44` is at most `θ` at `n ≥ 45`. -/
theorem P44_θb_le {t : ℝ} (ht : InRange t) : P44.θb t ≤ N45.P45.θb t := by
  have hp := (pieceOf_spec ht).1
  have h := (theta44_bounds _ hp).2
  rw [← pieceOf45_eq ht] at h
  rw [P44_θb, N45.P45_θb]
  exact_mod_cast h

theorem P44_θb_nonneg {t : ℝ} (ht : InRange t) : 0 ≤ P44.θb t := by
  have h := (theta44_bounds _ (pieceOf_spec ht).1).1
  rw [P44_θb]
  exact_mod_cast h

/-- `D` at `n ≥ 44` is at most `D` at `n ≥ 45`. -/
theorem P44_Db_le {t : ℝ} (ht : InRange t) : P44.Db t ≤ N45.P45.Db t := by
  have hp := (pieceOf_spec ht).1
  have h := (D44_bounds _ hp).2
  rw [← pieceOf45_eq ht] at h
  rw [P44_Db, N45.P45_Db]
  exact_mod_cast h

theorem P44_Db_nonneg {t : ℝ} (ht : InRange t) : 0 ≤ P44.Db t := by
  have h := (D44_bounds _ (pieceOf_spec ht).1).1
  rw [P44_Db]
  exact_mod_cast h

theorem P44_mfloor_nonneg {t : ℝ} (ht : InRange t) : 0 ≤ P44.mfloor t := by
  have h := mmin44_pos _ (pieceOf_spec ht).1
  rw [P44_mfloor]
  exact_mod_cast h.le

end Erdos993Lean.Analytic.N44
