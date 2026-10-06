import Erdos993Lean.Analytic.N48.Profile
import Erdos993Lean.Analytic.N52.Inputs
import Erdos993Lean.Analytic.TailCert.Sound
import Erdos993Lean.Analytic.N48.TailChecks.P22
import Erdos993Lean.Analytic.N48.TailChecks.P26
import Erdos993Lean.Analytic.N48.TailChecks.P27
import Erdos993Lean.Analytic.N48.TailChecks.P28

/-!
# O3 at `n ≥ 48`: the tail of the free count with the four new sub-band rows

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A20.  Sources: lane R4X's `LEAN/r4x/REACH_BELOW_52.md` §5(c)
(the four N = 48 rows at `t = 0`), lane O3R's certificates (`LEAN/ladder/o3/rows.json`, rows 1–4: the interval, the
rate `ℓ` and the potential coefficient `a`, run with the unmodified O3 checker), lane A10's pipeline: its verified cell
checker `TailCert.Compute.checkBand` (its own adaptive cover) with the soundness `TailCert.checkBand_sound`
(`Erdos993Lean/Analytic/TailCert/Sound.lean`), lane A3's `Tail.tail_t3`, and lane A19's all-forest O3
`N52.tailBound_act_all` (the tilts `t > 0` and every other piece are inherited from the parent band).

* `newRows`: the four checks `checkBand pieceLo pieceHi a ℓ 0 = true` of the pieces 22, 26, 27, 28
  (`TailChecks.rowP22` … `rowP28`, one `native_decide` each).
* **`tailNew`**: on a piece with a new row, for every forest and maximum-weight `B`:
  `P(M ≤ r) ≤ e^{−ℓ_new m} (1 + t)^r` (T3-2 at `z = 0`; the isolated-vertex condition `ℓ ≤ log(1 + λ)` from
  `expUp5 ℓ ≤ 1 + pieceLo`, kernel `decide`).
* **`tailBound48_all`**: `P(M ≤ r) ≤ tailFn48(t, m, r)` for every forest; **`tailBound48 : TailBoundN 48 P48`**.

Trust: the four `native_decide` checks of `TailChecks/*.lean` and lane A10's 30 band checks (through
`N52.tailBound_act_all`); the proofs here use only `propext`, `Classical.choice`, `Quot.sound`.

Scalarity check: `ℓ_new` summarizes the Laplace transform of the free count `M` at `z = 0` (T3-2: `E(1 − q)^M`-form
`P(M ≤ r) ≤ e^{−ℓ m}(1 + λ)^r`), produced by the certificate `T3UNonneg λ 0 a ℓ` of each piece; `a` is the potential's
coefficient (consumed only by `T3UNonneg`); the consumer is O4 through `P48.Tb = tailFn48`.
-/

namespace Erdos993Lean.Analytic.N48

open Profile30

/-- The pieces with a new O3 row are 22, 26, 27, 28 (kernel `decide`). -/
theorem newEll_ne_zero : ∀ p < 33, Data.newEll.getD p 0 ≠ 0 → p = 22 ∨ p = 26 ∨ p = 27 ∨ p = 28 := by
  decide +kernel

/-- The data of the four new rows (kernel `decide`). -/
theorem row_data :
    (Data.pieceLo.getD 22 0 = 13 / 10 ∧ Data.pieceHi.getD 22 0 = 27 / 20 ∧ Data.newA.getD 22 0 = 7 / 100 ∧
      Data.newEll.getD 22 0 = 23 / 50) ∧
    (Data.pieceLo.getD 26 0 = 8 / 5 ∧ Data.pieceHi.getD 26 0 = 33 / 20 ∧ Data.newA.getD 26 0 = 47 / 500 ∧
      Data.newEll.getD 26 0 = 939 / 2000) ∧
    (Data.pieceLo.getD 27 0 = 33 / 20 ∧ Data.pieceHi.getD 27 0 = 17 / 10 ∧ Data.newA.getD 27 0 = 97 / 1000 ∧
      Data.newEll.getD 27 0 = 47 / 100) ∧
    (Data.pieceLo.getD 28 0 = 17 / 10 ∧ Data.pieceHi.getD 28 0 = 7 / 4 ∧ Data.newA.getD 28 0 = 1 / 10 ∧
      Data.newEll.getD 28 0 = 941 / 2000) := by
  decide +kernel

/-- **The four new O3 rows pass lane A10's checker** (the `native_decide` checks `TailChecks.rowP22` … `rowP28`). -/
theorem newRows : ∀ p < 33, Data.newEll.getD p 0 ≠ 0 →
    TailCert.Compute.checkBand (Data.pieceLo.getD p 0) (Data.pieceHi.getD p 0) (Data.newA.getD p 0)
      (Data.newEll.getD p 0) 0 = true := by
  intro p hp hne
  obtain ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩, ⟨c1, c2, c3, c4⟩, ⟨d1, d2, d3, d4⟩⟩ := row_data
  rcases newEll_ne_zero p hp hne with rfl | rfl | rfl | rfl
  · rw [a1, a2, a3, a4]; exact TailChecks.rowP22
  · rw [b1, b2, b3, b4]; exact TailChecks.rowP26
  · rw [c1, c2, c3, c4]; exact TailChecks.rowP27
  · rw [d1, d2, d3, d4]; exact TailChecks.rowP28

/-- The side facts of the new rows: `0 ≤ ℓ ≤ 1`, `0 ≤ a` and `expUp5 ℓ ≤ 1 + pieceLo` (kernel `decide`). -/
theorem newRows_facts : ∀ p < 33, Data.newEll.getD p 0 ≠ 0 →
    0 ≤ Data.newEll.getD p 0 ∧ Data.newEll.getD p 0 ≤ 1 ∧ 0 ≤ Data.newA.getD p 0 ∧
      TailCert.expUp5 (Data.newEll.getD p 0) ≤ 1 + Data.pieceLo.getD p 0 := by
  decide +kernel

/-- **The tail on a piece with a new row**: for every forest, every activity `t` in range whose piece carries a new
O3 row and every maximum-weight independent set `B`, `P(M ≤ r) ≤ e^{−ℓ_new m} (1 + t)^r`. -/
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

/-- **O3 for every forest at `n ≥ 48`'s tail**: `P(M ≤ r) ≤ tailFn48(t, m, r)` at every activity in range and every
maximum-weight independent set (lane A19's actual-activity tail, and the new term on the four pieces). -/
theorem tailBound48_all (F : FiniteForest) {t : ℝ} (ht : InRange t) {B : Finset (Fin F.n)}
    (hB : IsMaxWeight F t B) (M' : ℕ) :
    (forestMixture F B t).cdfM M' ≤ tailFn48 t (forestMixture F B t).meanM M' := by
  have h1 := N52.tailBound_act_all F ht hB M'
  unfold tailFn48
  split_ifs with h
  · exact h1
  · exact le_min h1 (tailNew F ht hB h M')

/-- **O3 at `n ≥ 48`** for `P48`. -/
theorem tailBound48 : N52.TailBoundN 48 P48 :=
  fun F _ _ ht _ _ hB M' _ => tailBound48_all F ht hB M'

end Erdos993Lean.Analytic.N48
