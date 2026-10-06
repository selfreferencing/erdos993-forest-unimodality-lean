import Erdos993Lean.Analytic.N44.Profile
import Erdos993Lean.Analytic.N45.Tail

/-!
# O3 at `n ≥ 44`: the tail of the free count with the ladder rows at `t = 0`

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A21.  Sources: lane R4X's `LEAN/r4x/REACH_BELOW_52.md` §5(c) (the
ten `N = 44` rows at `t = 0`; row 19 of band 13 is certified on `[89/100, 23/25]` and used on the narrower
`[89/100, 91/100]`), lane O3R's certificates (`LEAN/ladder/o3/rows.json`), this lane's `Ladder/O3/Rows.lean` (`rows_ok`)
and `N45/Tail.lean` (whose proofs are copied, with the row's interval containing the piece).

* `row_table`, `newRows`: every piece with a ladder row passes the checker on the row's interval, which contains the
  piece, at the piece's rate and coefficient (kernel `decide` for the table lookup).
* **`tailNew`**: on such a piece, `P(M ≤ r) ≤ e^{−ℓ_new m} (1 + t)^r` for every forest and maximum-weight `B`.
* **`tailBound44_all`**, **`tailBound44 : TailBoundN 44 P44`**.

Trust: the 26 `native_decide` row checks and lane A10's 30 band checks (through `N45.tailBound45_all`).

Scalarity check: as `N45/Tail.lean`.
-/

namespace Erdos993Lean.Analytic.N44

open Profile30

/-- The ladder row of each piece with a new rate: its index is below `26`, the row's interval contains the piece, and
its coefficient and rate are the piece's (kernel `decide`). -/
theorem row_table : ∀ p < 55, Data.newEll.getD p 0 ≠ 0 →
    Data.rowOf.getD p 0 < 26 ∧
    Ladder.O3.rowLo.getD (Data.rowOf.getD p 0) 0 ≤ Data.pieceLo.getD p 0 ∧
    Data.pieceHi.getD p 0 ≤ Ladder.O3.rowHi.getD (Data.rowOf.getD p 0) 0 ∧
    Ladder.O3.rowA.getD (Data.rowOf.getD p 0) 0 = Data.newA.getD p 0 ∧
    Ladder.O3.rowEll.getD (Data.rowOf.getD p 0) 0 = Data.newEll.getD p 0 := by
  decide +kernel

/-- **The ladder rows of the pieces pass lane A10's checker** at `t = 0`, on the row's interval. -/
theorem newRows : ∀ p < 55, Data.newEll.getD p 0 ≠ 0 →
    TailCert.Compute.checkBand (Ladder.O3.rowLo.getD (Data.rowOf.getD p 0) 0)
      (Ladder.O3.rowHi.getD (Data.rowOf.getD p 0) 0) (Data.newA.getD p 0) (Data.newEll.getD p 0) 0 = true := by
  intro p hp hne
  obtain ⟨h1, -, -, h4, h5⟩ := row_table p hp hne
  rw [← h4, ← h5]
  exact Ladder.O3.rows_ok _ h1

/-- The side facts of the new rows: `0 ≤ ℓ ≤ 1`, `0 ≤ a` and `expUp5 ℓ ≤ 1 + pieceLo` (kernel `decide`). -/
theorem newRows_facts : ∀ p < 55, Data.newEll.getD p 0 ≠ 0 →
    0 ≤ Data.newEll.getD p 0 ∧ Data.newEll.getD p 0 ≤ 1 ∧ 0 ≤ Data.newA.getD p 0 ∧
      TailCert.expUp5 (Data.newEll.getD p 0) ≤ 1 + Data.pieceLo.getD p 0 := by
  decide +kernel

/-- **The tail on a piece with a ladder row**: `P(M ≤ r) ≤ e^{−ℓ_new m} (1 + t)^r`. -/
theorem tailNew (F : FiniteForest) {t : ℝ} (ht : InRange t) {B : Finset (Fin F.n)}
    (hB : IsMaxWeight F t B) (hne : Data.newEll.getD (pieceOf t) 0 ≠ 0) (M' : ℕ) :
    (forestMixture F B t).cdfM M' ≤
      Real.exp (-(newEllR t * (forestMixture F B t).meanM)) * (1 + t) ^ M' := by
  obtain ⟨hp, -, hlo, hhi⟩ := pieceOf_spec ht
  unfold loR at hlo
  unfold hiR at hhi
  have ht0 : 0 < t := by have := ht.1; linarith
  have hc := newRows (pieceOf t) hp hne
  obtain ⟨-, hrlo, hrhi, -, -⟩ := row_table (pieceOf t) hp hne
  obtain ⟨hl0, hl1, ha, hexp⟩ := newRows_facts (pieceOf t) hp hne
  have hlo' : ((Ladder.O3.rowLo.getD (Data.rowOf.getD (pieceOf t) 0) 0 : ℚ) : ℝ) ≤ t :=
    le_trans (by exact_mod_cast hrlo) hlo
  have hhi' : t ≤ ((Ladder.O3.rowHi.getD (Data.rowOf.getD (pieceOf t) 0) 0 : ℚ) : ℝ) :=
    le_trans hhi (by exact_mod_cast hrhi)
  have hU := TailCert.checkBand_sound hc t hlo' hhi'
  have hz : ((0 : ℚ) : ℝ) = 0 := Rat.cast_zero
  have hiso : ((Data.newEll.getD (pieceOf t) 0 : ℚ) : ℝ) ≤
      Real.log ((1 + t) / (1 + t * ((0 : ℚ) : ℝ))) := by
    rw [hz, mul_zero, add_zero, div_one, Real.le_log_iff_exp_le (by linarith)]
    have h1 := TailCert.exp_le_expUp5 hl0 hl1
    have h2 : ((TailCert.expUp5 (Data.newEll.getD (pieceOf t) 0) : ℚ) : ℝ) ≤
        1 + ((Data.pieceLo.getD (pieceOf t) 0 : ℚ) : ℝ) := by
      exact_mod_cast hexp
    linarith
  have h := Tail.tail_t3 F B hB.1 (TailCert.leafCondition_of_isMaxWeight ht0 hB) ht0
    (by have := ht.2; linarith) (by norm_num) (by norm_num) (by exact_mod_cast ha) hiso hU M'
  have e : (1 + t) / (1 + t * ((0 : ℚ) : ℝ)) = 1 + t := by rw [hz, mul_zero, add_zero, div_one]
  rw [e, neg_mul] at h
  exact h

/-- **O3 for every forest at `n ≥ 44`'s tail**: `P(M ≤ r) ≤ tailFn44(t, m, r)`. -/
theorem tailBound44_all (F : FiniteForest) {t : ℝ} (ht : InRange t) {B : Finset (Fin F.n)}
    (hB : IsMaxWeight F t B) (M' : ℕ) :
    (forestMixture F B t).cdfM M' ≤ tailFn44 t (forestMixture F B t).meanM M' := by
  have h1 := N45.tailBound45_all F ht hB M'
  unfold tailFn44
  split_ifs with h
  · exact h1
  · exact le_min h1 (tailNew F ht hB h M')

/-- **O3 at `n ≥ 44`** for `P44`. -/
theorem tailBound44 : N52.TailBoundN 44 P44 :=
  fun F _ _ ht _ _ hB M' _ => tailBound44_all F ht hB M'

end Erdos993Lean.Analytic.N44
