import Erdos993Lean.Analytic.N48.Data.Params
import Erdos993Lean.Analytic.Atlas.Profile

/-!
# The 33 pieces at `n ≥ 48`

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A20.  Source: lane R4X's `LEAN/r4x/config_N48.json` (the
configuration of the step `N = 48`, `REACH_BELOW_52.md` §5): Profile30's 30 activity bands, with band 23 (0-based 22,
`[13/10, 7/5]`) split at `27/20` and band 26 (0-based 25, `[8/5, 7/4]`) split at `33/20` and `17/10`, because the new
O3 rows at `t = 0` (lane O3R, `LEAN/ladder/o3/rows.json`) are certified on those sub-bands.  The piece data (edges,
parents, rates, ranks, floors) are in `N48/Data/Params.lean` (Lean core only, shared with the strip checks).

* `pieceOf t`: the piece of an activity (the left piece takes a common edge);
* `loR`, `hiR`: the piece edges as reals;
* **`pieceOf_spec`**: an activity in range lies in its piece: `pieceOf t < 33`, the piece's parent is `bandOf t`, and
  `pieceLo ≤ t ≤ pieceHi`;
* `piece_low`, `piece_mid`, `piece_high`, `piece_split`: the piece table against Profile30's edges (kernel `decide`).

Scalarity check: the piece edges delimit the activity domains of the new O3 certificates and of the O5 floors; they
are consumed by O3 (`N48/Tail.lean`), O5 (`N48/Density.lean`) and the strip cover (O4, `N48/Strip.lean`).
-/

namespace Erdos993Lean.Analytic.N48

open Profile30

/-- The piece (0-based, `< 33`) of an activity: its band, with band 22 split at `27/20` and band 25 at `33/20` and
`17/10` (the left piece takes the common edge). -/
noncomputable def pieceOf (t : ℝ) : ℕ :=
  if bandOf t < 22 then bandOf t
  else if bandOf t = 22 then (if t ≤ ((27 / 20 : ℚ) : ℝ) then 22 else 23)
  else if bandOf t < 25 then bandOf t + 1
  else if bandOf t = 25 then
    (if t ≤ ((33 / 20 : ℚ) : ℝ) then 26 else if t ≤ ((17 / 10 : ℚ) : ℝ) then 27 else 28)
  else bandOf t + 3

/-- The lower edge of piece `p` as a real number. -/
noncomputable def loR (p : ℕ) : ℝ := ((Data.pieceLo.getD p 0 : ℚ) : ℝ)

/-- The upper edge of piece `p` as a real number. -/
noncomputable def hiR (p : ℕ) : ℝ := ((Data.pieceHi.getD p 0 : ℚ) : ℝ)

/-- Pieces `0 … 21` are the bands `0 … 21`. -/
theorem piece_low : ∀ i < 22, Data.pieceLo.getD i 0 = edges.getD i 0 ∧
    Data.pieceHi.getD i 0 = edges.getD (i + 1) 0 ∧ Data.pieceParent.getD i 0 = i := by
  decide +kernel

/-- Pieces `24, 25` are the bands `23, 24`. -/
theorem piece_mid : ∀ i < 25, 23 ≤ i → Data.pieceLo.getD (i + 1) 0 = edges.getD i 0 ∧
    Data.pieceHi.getD (i + 1) 0 = edges.getD (i + 1) 0 ∧ Data.pieceParent.getD (i + 1) 0 = i := by
  decide +kernel

/-- Pieces `29 … 32` are the bands `26 … 29`. -/
theorem piece_high : ∀ i < 30, 26 ≤ i → Data.pieceLo.getD (i + 3) 0 = edges.getD i 0 ∧
    Data.pieceHi.getD (i + 3) 0 = edges.getD (i + 1) 0 ∧ Data.pieceParent.getD (i + 3) 0 = i := by
  decide +kernel

/-- The split pieces `22, 23` (band 22) and `26, 27, 28` (band 25). -/
theorem piece_split :
    Data.pieceLo.getD 22 0 = edges.getD 22 0 ∧ Data.pieceHi.getD 22 0 = 27 / 20 ∧
      Data.pieceParent.getD 22 0 = 22 ∧
    Data.pieceLo.getD 23 0 = 27 / 20 ∧ Data.pieceHi.getD 23 0 = edges.getD 23 0 ∧
      Data.pieceParent.getD 23 0 = 22 ∧
    Data.pieceLo.getD 26 0 = edges.getD 25 0 ∧ Data.pieceHi.getD 26 0 = 33 / 20 ∧
      Data.pieceParent.getD 26 0 = 25 ∧
    Data.pieceLo.getD 27 0 = 33 / 20 ∧ Data.pieceHi.getD 27 0 = 17 / 10 ∧
      Data.pieceParent.getD 27 0 = 25 ∧
    Data.pieceLo.getD 28 0 = 17 / 10 ∧ Data.pieceHi.getD 28 0 = edges.getD 26 0 ∧
      Data.pieceParent.getD 28 0 = 25 := by
  decide +kernel

/-- **The piece of an activity in range**: `pieceOf t < 33`, its parent band is `bandOf t`, and
`pieceLo ≤ t ≤ pieceHi`. -/
theorem pieceOf_spec {t : ℝ} (ht : InRange t) :
    pieceOf t < 33 ∧ Data.pieceParent.getD (pieceOf t) 0 = bandOf t ∧ loR (pieceOf t) ≤ t ∧
      t ≤ hiR (pieceOf t) := by
  obtain ⟨hi, hlo, hhi⟩ := Atlas.bandOf_spec ht
  unfold Atlas.edgeR at hlo hhi
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15⟩ := piece_split
  unfold loR hiR
  by_cases h1 : bandOf t < 22
  · have e : pieceOf t = bandOf t := by unfold pieceOf; rw [if_pos h1]
    obtain ⟨a, b, c⟩ := piece_low (bandOf t) h1
    rw [e, a, b]
    exact ⟨by omega, c, hlo, hhi⟩
  by_cases h2 : bandOf t = 22
  · have hlo' := hlo
    have hhi' := hhi
    rw [h2] at hlo' hhi'
    by_cases h3 : t ≤ ((27 / 20 : ℚ) : ℝ)
    · have e : pieceOf t = 22 := by unfold pieceOf; rw [if_neg h1, if_pos h2, if_pos h3]
      rw [e, s1, s2, s3, h2]
      exact ⟨by norm_num, rfl, hlo', h3⟩
    · have e : pieceOf t = 23 := by unfold pieceOf; rw [if_neg h1, if_pos h2, if_neg h3]
      rw [e, s4, s5, s6, h2]
      exact ⟨by norm_num, rfl, (not_le.mp h3).le, hhi'⟩
  by_cases h4 : bandOf t < 25
  · have e : pieceOf t = bandOf t + 1 := by unfold pieceOf; rw [if_neg h1, if_neg h2, if_pos h4]
    obtain ⟨a, b, c⟩ := piece_mid (bandOf t) h4 (by omega)
    rw [e, a, b]
    exact ⟨by omega, c, hlo, hhi⟩
  by_cases h5 : bandOf t = 25
  · have hlo' := hlo
    have hhi' := hhi
    rw [h5] at hlo' hhi'
    by_cases h6 : t ≤ ((33 / 20 : ℚ) : ℝ)
    · have e : pieceOf t = 26 := by unfold pieceOf; rw [if_neg h1, if_neg h2, if_neg h4, if_pos h5, if_pos h6]
      rw [e, s7, s8, s9, h5]
      exact ⟨by norm_num, rfl, hlo', h6⟩
    by_cases h7 : t ≤ ((17 / 10 : ℚ) : ℝ)
    · have e : pieceOf t = 27 := by
        unfold pieceOf; rw [if_neg h1, if_neg h2, if_neg h4, if_pos h5, if_neg h6, if_pos h7]
      rw [e, s10, s11, s12, h5]
      exact ⟨by norm_num, rfl, (not_le.mp h6).le, h7⟩
    · have e : pieceOf t = 28 := by
        unfold pieceOf; rw [if_neg h1, if_neg h2, if_neg h4, if_pos h5, if_neg h6, if_neg h7]
      rw [e, s13, s14, s15, h5]
      exact ⟨by norm_num, rfl, (not_le.mp h7).le, hhi'⟩
  · have e : pieceOf t = bandOf t + 3 := by unfold pieceOf; rw [if_neg h1, if_neg h2, if_neg h4, if_neg h5]
    obtain ⟨a, b, c⟩ := piece_high (bandOf t) hi (by omega)
    rw [e, a, b]
    exact ⟨by omega, c, hlo, hhi⟩

/-- The parent band of piece `p` is below `30` and the piece lies inside it. -/
theorem piece_in_parent : ∀ p < 33, Data.pieceParent.getD p 0 < 30 ∧
    edges.getD (Data.pieceParent.getD p 0) 0 ≤ Data.pieceLo.getD p 0 ∧
    Data.pieceLo.getD p 0 < Data.pieceHi.getD p 0 ∧
    Data.pieceHi.getD p 0 ≤ edges.getD (Data.pieceParent.getD p 0 + 1) 0 := by
  decide +kernel

end Erdos993Lean.Analytic.N48
