import Erdos993Lean.Analytic.Ladder.Pieces48
import Erdos993Lean.Analytic.N45.Data.Params

/-!
# The 46 pieces at `n ≥ 45`

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A21.  Source: lane R4X's `LEAN/r4x/config_N45_min.json` (the final
configuration of the step `N = 45`: Profile30's 30 bands with 16 of them split into two or three sub-bands), the piece
tables of `N45/Data/Params.lean`, and this lane's `Ladder/Pieces.lean`, `Ladder/Pieces48.lean`.

* `T45`: the pieces as a `Ladder.Pieces` table; `T45_good` (kernel `decide`).
* **`pieceOf t`**: the piece of an activity (`P45.pieceOf`); **`pieceOf_spec`**: for `t` in range, `pieceOf t < 46`, its
  parent is `bandOf t`, and `pieceLo ≤ t ≤ pieceHi`.
* `T45_refines`: the pieces refine lane A20's through `Data.pieceUp` (kernel `decide`); **`pieceOf48_eq`**: lane A20's
  `N48.pieceOf t = pieceUp (pieceOf t)`, so the strip tops (`piece45Cap`) are the n ≥ 48 floors of `N48.P48.mfloor`.
* `piece_in_parent`: every piece lies inside its parent band (kernel `decide`).

Scalarity check: the piece edges delimit the activity domains of the ladder certificates (O1, O2, O3 rows) and of the O5
floors; they are consumed by `N45/{Profile,Tail,Density,Strip}.lean`.
-/

namespace Erdos993Lean.Analytic.N45

open Profile30 Ladder

/-- The 46 pieces at `n ≥ 45` as a table. -/
def T45 : Pieces :=
  ⟨Data.pieceFirst, Data.pieceNsub, Data.pieceLo, Data.pieceHi, Data.pieceParent, 46⟩

/-- The table conditions of `T45` (kernel `decide`). -/
theorem T45_good : T45.Good := by decide +kernel

/-- The pieces at `n ≥ 45` refine lane A20's pieces at `n ≥ 48` through `Data.pieceUp` (kernel `decide`). -/
theorem T45_refines : Pieces.Refines T45 P48 Data.pieceUp := by decide +kernel

/-- The piece (0-based, `< 46`) of an activity: the left piece takes a common edge. -/
noncomputable def pieceOf (t : ℝ) : ℕ := T45.pieceOf t

/-- The lower edge of piece `p` as a real number. -/
noncomputable def loR (p : ℕ) : ℝ := ((Data.pieceLo.getD p 0 : ℚ) : ℝ)

/-- The upper edge of piece `p` as a real number. -/
noncomputable def hiR (p : ℕ) : ℝ := ((Data.pieceHi.getD p 0 : ℚ) : ℝ)

/-- **The piece of an activity in range**: `pieceOf t < 46`, its parent band is `bandOf t`, and
`pieceLo ≤ t ≤ pieceHi`. -/
theorem pieceOf_spec {t : ℝ} (ht : InRange t) :
    pieceOf t < 46 ∧ Data.pieceParent.getD (pieceOf t) 0 = bandOf t ∧ loR (pieceOf t) ≤ t ∧
      t ≤ hiR (pieceOf t) :=
  Pieces.pieceOf_spec T45_good ht

/-- **Lane A20's piece of `t` is the containing piece of the piece of `t`.** -/
theorem pieceOf48_eq {t : ℝ} (ht : InRange t) : N48.pieceOf t = Data.pieceUp.getD (pieceOf t) 0 := by
  rw [N48_pieceOf_eq ht]
  exact Pieces.pieceOf_refines T45_good P48_good T45_refines ht

/-- The parent band of piece `p` is below `30` and the piece lies inside it (kernel `decide`). -/
theorem piece_in_parent : ∀ p < 46, Data.pieceParent.getD p 0 < 30 ∧
    edges.getD (Data.pieceParent.getD p 0) 0 ≤ Data.pieceLo.getD p 0 ∧
    Data.pieceLo.getD p 0 < Data.pieceHi.getD p 0 ∧
    Data.pieceHi.getD p 0 ≤ edges.getD (Data.pieceParent.getD p 0 + 1) 0 := by
  decide +kernel

/-- The containing n ≥ 48 piece of every piece is below `33` (kernel `decide`). -/
theorem pieceUp_lt : ∀ p < 46, Data.pieceUp.getD p 0 < 33 := by decide +kernel

/-- The piece edges are positive (kernel `decide`). -/
theorem pieceLo_pos : ∀ p < 46, 0 < Data.pieceLo.getD p 0 := by decide +kernel

end Erdos993Lean.Analytic.N45
