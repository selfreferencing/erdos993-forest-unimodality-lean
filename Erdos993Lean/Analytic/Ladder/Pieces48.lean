import Erdos993Lean.Analytic.Ladder.Pieces
import Erdos993Lean.Analytic.N48.Pieces

/-!
# Lane A20's n ≥ 48 pieces as a `Pieces` table (lane A21)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A21.  Source: lane A20's `N48.pieceOf` (`N48/Pieces.lean`: the 33
pieces at `n ≥ 48`, band 23 (0-based 22) split at `27/20`, band 26 (0-based 25) at `33/20` and `17/10`, the left piece
taking a common edge) and its tables `N48.Data.pieceLo`, `pieceHi`, `pieceParent`.

* `P48`: the same pieces as a `Ladder.Pieces` table (`first`, `nsub` per band); `P48_good` (kernel `decide`).
* **`N48_pieceOf_eq`**: lane A20's explicit `N48.pieceOf t` equals the count-based `P48.pieceOf t` for every `t` in
  range (a case split on the two split bands, using the tie-breaking facts of `Pieces.countOf_spec`).

With `Pieces.pieceOf_refines`, the finer tables of the steps `N = 45` and `N = 44` are then related to lane A20's
pieces by decidable table facts alone (`N45/Pieces.lean`, `N44/Pieces.lean`).
-/

namespace Erdos993Lean.Analytic.Ladder

open Profile30

/-- Lane A20's 33 pieces at `n ≥ 48` as a table: bands 0–21 are single pieces `0–21`, band 22 has the pieces `22, 23`,
bands 23, 24 the pieces `24, 25`, band 25 the pieces `26, 27, 28`, bands 26–29 the pieces `29–32`. -/
def P48 : Pieces where
  first := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 29, 30, 31, 32]
  nsub := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1]
  lo := N48.Data.pieceLo
  hi := N48.Data.pieceHi
  parent := N48.Data.pieceParent
  count := 33

/-- The table conditions of `P48` (kernel `decide`). -/
theorem P48_good : P48.Good := by decide +kernel

theorem P48_first_low : ∀ i < 22, P48.first.getD i 0 = i ∧ P48.nsub.getD i 0 = 1 := by decide +kernel
theorem P48_first_22 : P48.first.getD 22 0 = 22 ∧ P48.nsub.getD 22 0 = 2 := by decide +kernel
theorem P48_first_mid : ∀ i < 25, 23 ≤ i → P48.first.getD i 0 = i + 1 ∧ P48.nsub.getD i 0 = 1 := by decide +kernel
theorem P48_first_25 : P48.first.getD 25 0 = 26 ∧ P48.nsub.getD 25 0 = 3 := by decide +kernel
theorem P48_first_high : ∀ i < 30, 26 ≤ i → P48.first.getD i 0 = i + 3 ∧ P48.nsub.getD i 0 = 1 := by decide +kernel
theorem P48_hi_22 : P48.hi.getD 22 0 = 27 / 20 := by decide +kernel
theorem P48_hi_26 : P48.hi.getD 26 0 = 33 / 20 := by decide +kernel
theorem P48_hi_27 : P48.hi.getD 27 0 = 17 / 10 := by decide +kernel

/-- **Lane A20's piece of an activity is the count-based one.** -/
theorem N48_pieceOf_eq {t : ℝ} (ht : InRange t) : N48.pieceOf t = P48.pieceOf t := by
  obtain ⟨hi30, -, -⟩ := Atlas.bandOf_spec ht
  obtain ⟨hc1, hc2, hc3⟩ := Pieces.countOf_spec P48_good ht
  unfold Pieces.pieceOf Pieces.firstOf Pieces.nsubOf at *
  unfold N48.pieceOf
  generalize hi_def : bandOf t = i at *
  generalize hc_def : P48.countOf t = c at *
  rcases (show i < 22 ∨ i = 22 ∨ (23 ≤ i ∧ i < 25) ∨ i = 25 ∨ 26 ≤ i by omega) with h | h | h | h | h
  · obtain ⟨e1, e2⟩ := P48_first_low i h
    rw [e2] at hc1
    rw [if_pos h, e1]
    omega
  · subst h
    obtain ⟨e1, e2⟩ := P48_first_22
    rw [e2] at hc1 hc3
    rw [e1] at hc2 hc3 ⊢
    rw [if_neg (by omega), if_pos rfl]
    rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
    · have h0 := hc3 0 le_rfl (by omega)
      unfold Pieces.hiR at h0
      rw [add_zero, P48_hi_22] at h0
      rw [if_pos h0]
    · have h0 := hc2 0 (by omega)
      unfold Pieces.hiR at h0
      rw [add_zero, P48_hi_22] at h0
      rw [if_neg (not_le.mpr h0)]
  · obtain ⟨e1, e2⟩ := P48_first_mid i h.2 h.1
    rw [e2] at hc1
    rw [if_neg (by omega), if_neg (by omega), if_pos h.2, e1]
    omega
  · subst h
    obtain ⟨e1, e2⟩ := P48_first_25
    rw [e2] at hc1 hc3
    rw [e1] at hc2 hc3 ⊢
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
    rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega) with rfl | rfl | rfl
    · have h0 := hc3 0 le_rfl (by omega)
      unfold Pieces.hiR at h0
      rw [add_zero, P48_hi_26] at h0
      rw [if_pos h0]
    · have h0 := hc2 0 (by omega)
      have h1 := hc3 1 le_rfl (by omega)
      unfold Pieces.hiR at h0 h1
      rw [add_zero, P48_hi_26] at h0
      rw [show (26 : ℕ) + 1 = 27 by rfl, P48_hi_27] at h1
      rw [if_neg (not_le.mpr h0), if_pos h1]
    · have h0 := hc2 0 (by omega)
      have h1 := hc2 1 (by omega)
      unfold Pieces.hiR at h0 h1
      rw [add_zero, P48_hi_26] at h0
      rw [show (26 : ℕ) + 1 = 27 by rfl, P48_hi_27] at h1
      rw [if_neg (not_le.mpr h0), if_neg (not_le.mpr h1)]
  · obtain ⟨e1, e2⟩ := P48_first_high i hi30 h
    rw [e2] at hc1
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), e1]
    omega

end Erdos993Lean.Analytic.Ladder
