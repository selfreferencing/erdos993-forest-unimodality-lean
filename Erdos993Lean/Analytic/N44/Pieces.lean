import Erdos993Lean.Analytic.N45.Pieces
import Erdos993Lean.Analytic.N44.Data.Params

/-!
# The 55 pieces at `n ≥ 44`

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A21.  Source: lane R4X's `LEAN/r4x/config_N44_final.json` (the final
configuration of the step `N = 44`: the `N = 45` pieces with bands 10, 12, 13, 14, 15 split further), the piece tables of
`N44/Data/Params.lean`, this lane's `Ladder/Pieces.lean` and `N45/Pieces.lean`.

* `T44`: the pieces as a `Ladder.Pieces` table; `T44_good` (kernel `decide`).
* **`pieceOf t`**: the piece of an activity; **`pieceOf_spec`**: for `t` in range, `pieceOf t < 55`, its parent is
  `bandOf t`, and `pieceLo ≤ t ≤ pieceHi`.
* `T44_refines`: the pieces refine the `n ≥ 45` pieces through `Data.pieceUp` (kernel `decide`); **`pieceOf45_eq`**:
  `N45.pieceOf t = pieceUp (pieceOf t)`, so the strip tops (`piece44Cap`) are the n ≥ 45 floors of `N45.P45.mfloor`.

Scalarity check: the piece edges delimit the activity domains of the ladder certificates and of the O5 floors; they are
consumed by `N44/{Profile,Tail,Density,Strip}.lean`.
-/

namespace Erdos993Lean.Analytic.N44

open Profile30 Ladder

/-- The 55 pieces at `n ≥ 44` as a table. -/
def T44 : Pieces :=
  ⟨Data.pieceFirst, Data.pieceNsub, Data.pieceLo, Data.pieceHi, Data.pieceParent, 55⟩

/-- The table conditions of `T44` (kernel `decide`). -/
theorem T44_good : T44.Good := by decide +kernel

/-- The pieces at `n ≥ 44` refine the pieces at `n ≥ 45` through `Data.pieceUp` (kernel `decide`). -/
theorem T44_refines : Pieces.Refines T44 N45.T45 Data.pieceUp := by decide +kernel

/-- The piece (0-based, `< 55`) of an activity: the left piece takes a common edge. -/
noncomputable def pieceOf (t : ℝ) : ℕ := T44.pieceOf t

/-- The lower edge of piece `p` as a real number. -/
noncomputable def loR (p : ℕ) : ℝ := ((Data.pieceLo.getD p 0 : ℚ) : ℝ)

/-- The upper edge of piece `p` as a real number. -/
noncomputable def hiR (p : ℕ) : ℝ := ((Data.pieceHi.getD p 0 : ℚ) : ℝ)

/-- **The piece of an activity in range**: `pieceOf t < 55`, its parent band is `bandOf t`, and
`pieceLo ≤ t ≤ pieceHi`. -/
theorem pieceOf_spec {t : ℝ} (ht : InRange t) :
    pieceOf t < 55 ∧ Data.pieceParent.getD (pieceOf t) 0 = bandOf t ∧ loR (pieceOf t) ≤ t ∧
      t ≤ hiR (pieceOf t) :=
  Pieces.pieceOf_spec T44_good ht

/-- **The `n ≥ 45` piece of `t` is the containing piece of the piece of `t`.** -/
theorem pieceOf45_eq {t : ℝ} (ht : InRange t) : N45.pieceOf t = Data.pieceUp.getD (pieceOf t) 0 :=
  Pieces.pieceOf_refines T44_good N45.T45_good T44_refines ht

/-- The containing n ≥ 45 piece of every piece is below `46` (kernel `decide`). -/
theorem pieceUp_lt : ∀ p < 55, Data.pieceUp.getD p 0 < 46 := by decide +kernel

/-- The piece edges are positive (kernel `decide`). -/
theorem pieceLo_pos : ∀ p < 55, 0 < Data.pieceLo.getD p 0 := by decide +kernel

end Erdos993Lean.Analytic.N44
