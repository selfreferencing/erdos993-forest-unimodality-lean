import Erdos993Lean.Analytic.N45.Profile
import Erdos993Lean.Analytic.N48.Tail
import Erdos993Lean.Analytic.Ladder.O3.Rows
import Erdos993Lean.Analytic.TailCert.Sound

/-!
# O3 at `n ≥ 45`: the tail of the free count with the ladder rows at `t = 0`

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A21.  Sources: lane R4X's `LEAN/r4x/REACH_BELOW_52.md` §5(c)
(the twelve `N = 45` rows and the four `N = 48` rows at `t = 0`), lane O3R's certificates (`LEAN/ladder/o3/rows.json`,
rows 1–16, run with the unmodified O3 checker), this lane's `Ladder/O3/Rows.lean` (`rows_ok`: the 26 rows pass lane
A10's verified cell checker `TailCert.Compute.checkBand`), lane A10's soundness `TailCert.checkBand_sound`, lane A3's
`Tail.tail_t3`, lane A20's `N48.tailBound48_all` (whose proof `tailNew` copies).

* `row_table`, `newRows`: every piece with a ladder row (`Data.newEll ≠ 0`) passes the checker on its own interval
  at its own rate and coefficient (the row `Data.rowOf p` of the 26-row table; kernel `decide` for the table lookup).
* **`tailNew`**: on such a piece, for every forest and maximum-weight `B`: `P(M ≤ r) ≤ e^{−ℓ_new m} (1 + t)^r`
  (T3-2 at `z = 0`; the isolated-vertex condition `ℓ ≤ log(1 + λ)` from `expUp5 ℓ ≤ 1 + pieceLo`, kernel `decide`).
* **`tailBound45_all`**: `P(M ≤ r) ≤ tailFn45(t, m, r)` for every forest; **`tailBound45 : TailBoundN 45 P45`**.

Trust: the 26 `native_decide` row checks (lane A20's four and this lane's 22) and lane A10's 30 band checks (through
`N48.tailBound48_all`); the proofs here use only `propext`, `Classical.choice`, `Quot.sound`.

Scalarity check: `ℓ_new` summarizes the Laplace transform of the free count `M` at `z = 0` (T3-2:
`P(M ≤ r) ≤ e^{−ℓ m}(1 + λ)^r`), produced by the certificate `T3UNonneg λ 0 a ℓ` of each piece; `a` is the potential's
coefficient (consumed only by `T3UNonneg`); the consumer is O4 through `P45.Tb = tailFn45`.
-/

namespace Erdos993Lean.Analytic.N45

open Profile30

/-- The ladder row of each piece with a new rate: its index is below `26` and the row's interval, coefficient and
rate are the piece's (kernel `decide`). -/
theorem row_table : ∀ p < 46, Data.newEll.getD p 0 ≠ 0 →
    Data.rowOf.getD p 0 < 26 ∧
    Ladder.O3.rowLo.getD (Data.rowOf.getD p 0) 0 = Data.pieceLo.getD p 0 ∧
    Ladder.O3.rowHi.getD (Data.rowOf.getD p 0) 0 = Data.pieceHi.getD p 0 ∧
    Ladder.O3.rowA.getD (Data.rowOf.getD p 0) 0 = Data.newA.getD p 0 ∧
    Ladder.O3.rowEll.getD (Data.rowOf.getD p 0) 0 = Data.newEll.getD p 0 := by
  decide +kernel

/-- **The ladder rows of the pieces pass lane A10's checker** at `t = 0`. -/
theorem newRows : ∀ p < 46, Data.newEll.getD p 0 ≠ 0 →
    TailCert.Compute.checkBand (Data.pieceLo.getD p 0) (Data.pieceHi.getD p 0) (Data.newA.getD p 0)
      (Data.newEll.getD p 0) 0 = true := by
  intro p hp hne
  obtain ⟨h1, h2, h3, h4, h5⟩ := row_table p hp hne
  rw [← h2, ← h3, ← h4, ← h5]
  exact Ladder.O3.rows_ok _ h1

/-- The side facts of the new rows: `0 ≤ ℓ ≤ 1`, `0 ≤ a` and `expUp5 ℓ ≤ 1 + pieceLo` (kernel `decide`). -/
theorem newRows_facts : ∀ p < 46, Data.newEll.getD p 0 ≠ 0 →
    0 ≤ Data.newEll.getD p 0 ∧ Data.newEll.getD p 0 ≤ 1 ∧ 0 ≤ Data.newA.getD p 0 ∧
      TailCert.expUp5 (Data.newEll.getD p 0) ≤ 1 + Data.pieceLo.getD p 0 := by
  decide +kernel

/-- **The tail on a piece with a ladder row**: for every forest, every activity `t` in range whose piece carries a
row and every maximum-weight independent set `B`, `P(M ≤ r) ≤ e^{−ℓ_new m} (1 + t)^r`. -/
theorem tailNew (F : FiniteForest) {t : ℝ} (ht : InRange t) {B : Finset (Fin F.n)}
    (hB : IsMaxWeight F t B) (hne : Data.newEll.getD (pieceOf t) 0 ≠ 0) (M' : ℕ) :
    (forestMixture F B t).cdfM M' ≤
      Real.exp (-(newEllR t * (forestMixture F B t).meanM)) * (1 + t) ^ M' := by
  obtain ⟨hp, -, hlo, hhi⟩ := pieceOf_spec ht
  unfold loR at hlo
  unfold hiR at hhi
  have ht0 : 0 < t := by have := ht.1; linarith
  have hc := newRows (pieceOf t) hp hne
  obtain ⟨hl0, hl1, ha, hexp⟩ := newRows_facts (pieceOf t) hp hne
  have hU := TailCert.checkBand_sound hc t hlo hhi
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

/-- **O3 for every forest at `n ≥ 45`'s tail**: `P(M ≤ r) ≤ tailFn45(t, m, r)` at every activity in range and every
maximum-weight independent set (lane A20's tail, and the new term on the ladder pieces). -/
theorem tailBound45_all (F : FiniteForest) {t : ℝ} (ht : InRange t) {B : Finset (Fin F.n)}
    (hB : IsMaxWeight F t B) (M' : ℕ) :
    (forestMixture F B t).cdfM M' ≤ tailFn45 t (forestMixture F B t).meanM M' := by
  have h1 := N48.tailBound48_all F ht hB M'
  unfold tailFn45
  split_ifs with h
  · exact h1
  · exact le_min h1 (tailNew F ht hB h M')

/-- **O3 at `n ≥ 45`** for `P45`. -/
theorem tailBound45 : N52.TailBoundN 45 P45 :=
  fun F _ _ ht _ _ hB M' _ => tailBound45_all F ht hB M'

end Erdos993Lean.Analytic.N45
