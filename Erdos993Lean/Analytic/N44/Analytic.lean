import Erdos993Lean.Analytic.N44.Density
import Erdos993Lean.Analytic.N44.Tail
import Erdos993Lean.Analytic.N44.O4
import Erdos993Lean.Analytic.N52.Inputs
import Erdos993Lean.Analytic.Ladder.O1.Rows
import Erdos993Lean.Analytic.Ladder.O2.Rows

/-!
# The analytic half: every forest with at least 44 vertices is unimodal

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A21.  Lane R4X (`LEAN/r4x/REACH_BELOW_52.md` §0, §5(f) step 4)
showed that the analytic route closes for `n ≥ 44` with one more O1 refit, two more O2 refits, ten more O3 sub-band
rows at `t = 0`, one more record and floor splits; the referee adopted the rows.  This file assembles it for the profile
`P44`:

* O1 at `n ≥ 44` (`varianceBound44`): lane A19's `N52.varianceBound_all` on the pieces with Profile30's `D`, and the O1R
  rows on the refit pieces (`bandVar_bandR3_proved` on `[22/25, 47/50]` at `D = 11/10`, `bandVar_bandR2_proved` on band
  23 at `13/10`, `bandVar_bandR1_proved` on `[8/5, 33/20]` at `7/5`);
* O2 at `n ≥ 44` (`varianceRatioBound44`): lane A19's `N52.varianceRatioBound_all`, and the O2R rows (`vrb_O2R3` on
  `[39/50, 4/5]` at `θ = 13/20`, `vrb_O2R2` on `[8/5, 33/20]` at `9/10`, `vrb_O2R1` on `[33/20, 7/4]` at `19/20`);
* O3 (`tailBound44`), O4 (`thresholdNoValley_P44`), O5 (`densityBound44`).

**`unimodal_of_ge_44`**: every finite forest with at least 44 vertices has a unimodal independence sequence.

Trust: the `native_decide` checks inherited from the certificate layers (O1: 13 + 3, O2: 168 + 36, O3: 30 + 26, lane
A9's atlas: 60, lane A19's strip: 30, lane A20's strip: 31, the n ≥ 45 strip: 30, the n ≥ 44 strip: 27); everything
else `propext`, `Classical.choice`, `Quot.sound`.

Scalarity check: no new scalar; each field of `P44` is consumed by O4 as in `Top.lean`.
-/

namespace Erdos993Lean.Analytic.N44

open Profile30 N52

/-- Every piece's `D` is the parent band's or one of the three O1R refits, on a piece inside the row (kernel
`decide`). -/
theorem D44_table : ∀ p < 55,
    Data.D44.getD p 0 = Dt.getD (Data.pieceParent.getD p 0) (8 / 5) ∨
    (Data.D44.getD p 0 = 11 / 10 ∧ 22 / 25 ≤ Data.pieceLo.getD p 0 ∧ Data.pieceHi.getD p 0 ≤ 47 / 50) ∨
    (Data.D44.getD p 0 = 13 / 10 ∧ 13 / 10 ≤ Data.pieceLo.getD p 0 ∧ Data.pieceHi.getD p 0 ≤ 7 / 5) ∨
    (Data.D44.getD p 0 = 7 / 5 ∧ 8 / 5 ≤ Data.pieceLo.getD p 0 ∧ Data.pieceHi.getD p 0 ≤ 33 / 20) := by
  decide +kernel

/-- Every piece's `θ` is the parent band's or one of the three O2R refits, on a piece inside the row (kernel
`decide`). -/
theorem theta44_table : ∀ p < 55,
    Data.theta44.getD p 0 = θt.getD (Data.pieceParent.getD p 0) 1 ∨
    (Data.theta44.getD p 0 = 13 / 20 ∧ 39 / 50 ≤ Data.pieceLo.getD p 0 ∧ Data.pieceHi.getD p 0 ≤ 4 / 5) ∨
    (Data.theta44.getD p 0 = 9 / 10 ∧ 8 / 5 ≤ Data.pieceLo.getD p 0 ∧ Data.pieceHi.getD p 0 ≤ 33 / 20) ∨
    (Data.theta44.getD p 0 = 19 / 20 ∧ 33 / 20 ≤ Data.pieceLo.getD p 0 ∧ Data.pieceHi.getD p 0 ≤ 7 / 4) := by
  decide +kernel

/-- **O1 for every forest at `n ≥ 44`'s caps**: `Var M ≤ D(λ) m` with the piece-wise `D`. -/
theorem varianceBound44_all (F : FiniteForest) {t : ℝ} (ht : InRange t) {B : Finset (Fin F.n)}
    (hB : IsMaxWeight F t B) :
    (forestMixture F B t).varM ≤ P44.Db t * (forestMixture F B t).meanM := by
  obtain ⟨hp, hpar, hlo, hhi⟩ := pieceOf_spec ht
  unfold loR at hlo
  unfold hiR at hhi
  rw [P44_Db]
  rcases D44_table _ hp with h | ⟨e, a, b⟩ | ⟨e, a, b⟩ | ⟨e, a, b⟩
  · rw [h, hpar]
    exact varianceBound_all F ht hB
  · rw [e]
    exact Ladder.O1.bandVar_bandR3_proved F t (le_trans (by exact_mod_cast a) hlo)
      (le_trans hhi (by exact_mod_cast b)) B hB
  · rw [e]
    exact Ladder.O1.bandVar_bandR2_proved F t (le_trans (by exact_mod_cast a) hlo)
      (le_trans hhi (by exact_mod_cast b)) B hB
  · rw [e]
    exact Ladder.O1.bandVar_bandR1_proved F t (le_trans (by exact_mod_cast a) hlo)
      (le_trans hhi (by exact_mod_cast b)) B hB

/-- **O2 for every forest at `n ≥ 44`'s caps**: `V ≤ (1 + θ(λ))(1 − q) W` with the piece-wise `θ`. -/
theorem varianceRatioBound44_all (F : FiniteForest) {t : ℝ} (ht : InRange t) {B : Finset (Fin F.n)}
    (hB : IsMaxWeight F t B) :
    hardCoreVar F t ≤ (1 + P44.θb t) * (1 - actQ t) * weightW F t B := by
  obtain ⟨hp, hpar, hlo, hhi⟩ := pieceOf_spec ht
  unfold loR at hlo
  unfold hiR at hhi
  rw [P44_θb]
  rcases theta44_table _ hp with h | ⟨e, a, b⟩ | ⟨e, a, b⟩ | ⟨e, a, b⟩
  · rw [h, hpar]
    exact varianceRatioBound_all F ht hB
  · rw [e]
    exact Ladder.O2.vrb_O2R3 F (le_trans (by exact_mod_cast a) hlo) (le_trans hhi (by exact_mod_cast b)) hB
  · rw [e]
    exact Ladder.O2.vrb_O2R2 F (le_trans (by exact_mod_cast a) hlo) (le_trans hhi (by exact_mod_cast b)) hB
  · rw [e]
    exact Ladder.O2.vrb_O2R1 F (le_trans (by exact_mod_cast a) hlo) (le_trans hhi (by exact_mod_cast b)) hB

/-- **O1 at `n ≥ 44`** for `P44`. -/
theorem varianceBound44 : VarianceBoundN 44 P44 :=
  fun F _ _ ht _ _ hB => varianceBound44_all F ht hB

/-- **O2 at `n ≥ 44`** for `P44`. -/
theorem varianceRatioBound44 : VarianceRatioBoundN 44 P44 :=
  fun F _ _ ht _ _ hB => varianceRatioBound44_all F ht hB

/-- **The analytic inputs at `n ≥ 44`** for the profile `P44`. -/
theorem analyticInputs44 : AnalyticInputsN 44 P44 :=
  ⟨varianceBound44, varianceRatioBound44, tailBound44, thresholdNoValley_P44, densityBound44⟩

/-- **The analytic half of Erdős #993 at 44**: every finite forest with at least 44 vertices has a unimodal
independence sequence. -/
theorem unimodal_of_ge_44 : ∀ F : FiniteForest, 44 ≤ F.n → independenceSequenceUnimodal F :=
  fun F hn => unimodal_of_inputsN analyticInputs44 F hn

/-- The analytic half as the ceiling claim at 44. -/
theorem ceilingStatement_44 : CeilingStatement 44 := unimodal_of_ge_44

end Erdos993Lean.Analytic.N44
