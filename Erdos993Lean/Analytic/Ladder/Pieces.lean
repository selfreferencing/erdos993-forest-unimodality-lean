import Erdos993Lean.Analytic.Atlas.Profile

/-!
# Pieces: refinements of Profile30's bands, located by counting edges (lane A21)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A21.  Sources: lane A9's `Atlas.bandOf` and `count_lt_spec`
(`Erdos993Lean/Analytic/Atlas/Profile.lean`: the band of an activity is the number of band edges strictly below it),
lane A20's `N48.pieceOf` (`N48/Pieces.lean`, an explicit case split of two bands).  The ladder steps `N = 45` and
`N = 44` split many bands into two or three pieces, and the pieces of one step refine those of the step above; this
module does the bookkeeping once, for arbitrary tables.

* `Pieces`: a refinement of the 30 bands, as tables: per band `i` its first piece `first i` and its number of pieces
  `nsub i`; per piece `p` its edges `lo p`, `hi p` and its parent band `parent p`; `count` pieces in all.
* **`Pieces.pieceOf t`**: the piece of an activity `t`: the first piece of the band of `t` (lane A9's `bandOf`), plus
  the number of upper edges of that band's pieces (all but the last) that lie strictly below `t`.  So the left piece
  takes a common edge, exactly as `bandOf` does for the bands, and the parent of the piece of `t` is `bandOf t` by
  construction.
* `Pieces.Good`: the decidable table conditions (each band has at least one piece, the pieces of a band tile it in
  order, consecutive pieces share an edge, every piece is nondegenerate, parents are right).
* **`Pieces.pieceOf_spec`**: for a good table and `t ∈ [1/3, 7/3]`: `pieceOf t < count`,
  `parent (pieceOf t) = bandOf t`, `lo (pieceOf t) ≤ t ≤ hi (pieceOf t)`; and the tie-breaking facts
  (`countOf_spec`): the counted edges are strictly below `t`, the others are at or above `t`.
* `Pieces.Refines Q P up`: the decidable conditions under which the finer table `Q` refines `P` band by band through
  the table `up` (piece of `Q` ↦ piece of `P` containing it).
* **`Pieces.pieceOf_refines`**: then `P.pieceOf t = up (Q.pieceOf t)` for every `t` in range, i.e. the two
  tie-breakings agree.

Scalarity check: no scalar is carried; the tables are the activity domains of the certificates and of the O5 floors
(consumed by `N45/*.lean`, `N44/*.lean`).
-/

namespace Erdos993Lean.Analytic.Ladder

open Profile30 Atlas

/-- A refinement of Profile30's 30 activity bands into pieces, as tables (0-based). -/
structure Pieces where
  /-- the first piece of each band -/
  first : List ℕ
  /-- the number of pieces of each band -/
  nsub : List ℕ
  /-- the lower edge of each piece -/
  lo : List ℚ
  /-- the upper edge of each piece -/
  hi : List ℚ
  /-- the parent band of each piece -/
  parent : List ℕ
  /-- the number of pieces -/
  count : ℕ

namespace Pieces

variable (P : Pieces)

/-- The lower edge of piece `p` as a real number. -/
noncomputable def loR (p : ℕ) : ℝ := ((P.lo.getD p 0 : ℚ) : ℝ)

/-- The upper edge of piece `p` as a real number. -/
noncomputable def hiR (p : ℕ) : ℝ := ((P.hi.getD p 0 : ℚ) : ℝ)

/-- The first piece of the band of `t`. -/
noncomputable def firstOf (t : ℝ) : ℕ := P.first.getD (bandOf t) 0

/-- The number of pieces of the band of `t`. -/
noncomputable def nsubOf (t : ℝ) : ℕ := P.nsub.getD (bandOf t) 0

/-- The number of upper edges of the pieces of the band of `t` (all but the last) strictly below `t`. -/
noncomputable def countOf (t : ℝ) : ℕ :=
  ((List.range (P.nsubOf t - 1)).filter fun j => decide (P.hiR (P.firstOf t + j) < t)).length

/-- **The piece of an activity**: the first piece of its band plus the count of the band's inner upper edges
strictly below it (the left piece takes a common edge). -/
noncomputable def pieceOf (t : ℝ) : ℕ := P.firstOf t + P.countOf t

/-- The decidable table conditions: every band has a piece and its pieces fit in `count`; the first piece of a band
starts at the band's lower edge and its last piece ends at the band's upper edge; parents are right; consecutive
pieces of a band share an edge; every piece is nondegenerate. -/
def Good : Prop :=
  (∀ i < 30, 1 ≤ P.nsub.getD i 0 ∧ P.first.getD i 0 + P.nsub.getD i 0 ≤ P.count) ∧
  (∀ i < 30, P.lo.getD (P.first.getD i 0) 0 = edges.getD i 0) ∧
  (∀ i < 30, P.hi.getD (P.first.getD i 0 + (P.nsub.getD i 0 - 1)) 0 = edges.getD (i + 1) 0) ∧
  (∀ i < 30, ∀ j < P.nsub.getD i 0, P.parent.getD (P.first.getD i 0 + j) 0 = i) ∧
  (∀ i < 30, ∀ j < P.nsub.getD i 0 - 1,
    P.hi.getD (P.first.getD i 0 + j) 0 = P.lo.getD (P.first.getD i 0 + (j + 1)) 0) ∧
  (∀ i < 30, ∀ j < P.nsub.getD i 0, P.lo.getD (P.first.getD i 0 + j) 0 < P.hi.getD (P.first.getD i 0 + j) 0)

instance : Decidable P.Good := by unfold Good; infer_instance

section Spec

variable {P}

/-- Within a band the upper edges of the pieces increase (rational). -/
theorem hi_le_hi (hG : P.Good) {i : ℕ} (hi : i < 30) {j j' : ℕ} (hjj : j ≤ j')
    (hj' : j' < P.nsub.getD i 0) :
    P.hi.getD (P.first.getD i 0 + j) 0 ≤ P.hi.getD (P.first.getD i 0 + j') 0 := by
  obtain ⟨-, -, -, -, hchain, hnd⟩ := hG
  induction j' with
  | zero =>
    have : j = 0 := by omega
    subst this
    exact le_rfl
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hjj with h | h
    · subst h; exact le_rfl
    · have h1 := ih (by omega) (by omega)
      have h2 := hchain i hi k (by omega)
      have h3 := hnd i hi (k + 1) hj'
      rw [h2] at h1
      exact h1.trans h3.le

/-- The count locates `t` among the inner upper edges of its band: it is at most the number of inner edges, the
counted edges are strictly below `t`, the others are at or above `t`. -/
theorem countOf_spec (hG : P.Good) {t : ℝ} (ht : InRange t) :
    P.countOf t + 1 ≤ P.nsubOf t ∧
    (∀ k, k < P.countOf t → P.hiR (P.firstOf t + k) < t) ∧
    (∀ k, P.countOf t ≤ k → k + 1 < P.nsubOf t → t ≤ P.hiR (P.firstOf t + k)) := by
  obtain ⟨hi30, -, -⟩ := Atlas.bandOf_spec ht
  obtain ⟨hcnt, -, -, -, hchain, hnd⟩ := hG
  unfold countOf firstOf nsubOf
  generalize hi_def : bandOf t = i at *
  have hn1 : 1 ≤ P.nsub.getD i 0 := (hcnt i hi30).1
  -- the monotone sequence `e 0 = lo f`, `e (k + 1) = hi (f + k)`
  let e : ℕ → ℝ := fun k =>
    if k = 0 then P.loR (P.first.getD i 0) else P.hiR (P.first.getD i 0 + (k - 1))
  have e0 : e 0 = P.loR (P.first.getD i 0) := by simp [e]
  have eS : ∀ k, e (k + 1) = P.hiR (P.first.getD i 0 + k) := by intro k; simp [e]
  have hstep : ∀ k, k < P.nsub.getD i 0 - 1 → e k ≤ e (k + 1) := by
    intro k hk
    rw [eS]
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rw [e0, add_zero]
      unfold loR hiR
      exact_mod_cast (hnd i hi30 0 (by omega)).le
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [eS]
      unfold hiR
      have h1 := hchain i hi30 k' (by omega)
      have h2 := hnd i hi30 (k' + 1) (by omega)
      rw [h1]
      exact_mod_cast h2.le
  have hmono : ∀ a b, a ≤ b → b ≤ P.nsub.getD i 0 - 1 → e a ≤ e b := by
    intro a b hab hb
    induction b with
    | zero =>
      have : a = 0 := by omega
      subst this
      exact le_rfl
    | succ b ih =>
      rcases Nat.eq_or_lt_of_le hab with h | h
      · subst h; exact le_rfl
      · exact (ih (by omega) (by omega)).trans (hstep b (by omega))
  have hcount : ((List.range (P.nsub.getD i 0 - 1)).filter fun j =>
        decide (P.hiR (P.first.getD i 0 + j) < t)).length =
      ((List.range (P.nsub.getD i 0 - 1)).filter fun j => decide (e (j + 1) < t)).length := by
    simp only [eS]
  obtain ⟨h1, h2, h3⟩ := count_lt_spec e t (P.nsub.getD i 0 - 1) hmono
  rw [← hcount] at h1 h2 h3
  refine ⟨by omega, fun k hk => ?_, fun k hk hk' => ?_⟩
  · have := h1 k hk
    rw [eS] at this
    exact this
  · have := h2 k hk (by omega)
    rw [eS] at this
    exact this

/-- **The piece of an activity in range**: it exists, its parent is the band of `t`, and it contains `t`. -/
theorem pieceOf_spec (hG : P.Good) {t : ℝ} (ht : InRange t) :
    P.pieceOf t < P.count ∧ P.parent.getD (P.pieceOf t) 0 = bandOf t ∧
      P.loR (P.pieceOf t) ≤ t ∧ t ≤ P.hiR (P.pieceOf t) := by
  obtain ⟨hi30, hlo, hhi⟩ := Atlas.bandOf_spec ht
  obtain ⟨hc1, hc2, hc3⟩ := countOf_spec hG ht
  obtain ⟨hcnt, hlo0, hhiN, hpar, hchain, -⟩ := hG
  have hlo' : ((edges.getD (bandOf t) 0 : ℚ) : ℝ) ≤ t := hlo
  have hhi' : t ≤ ((edges.getD (bandOf t + 1) 0 : ℚ) : ℝ) := hhi
  unfold pieceOf firstOf nsubOf at *
  generalize hi_def : bandOf t = i at *
  generalize hc_def : P.countOf t = c at *
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := (hcnt i hi30).2
    omega
  · exact hpar i hi30 c (by omega)
  · rcases Nat.eq_zero_or_pos c with h0 | hpos
    · rw [h0, add_zero]
      unfold loR
      rw [hlo0 i hi30]
      exact hlo'
    · have := hc2 (c - 1) (by omega)
      have e1 := hchain i hi30 (c - 1) (by omega)
      rw [show c - 1 + 1 = c by omega] at e1
      unfold hiR at this
      unfold loR
      rw [e1] at this
      exact this.le
  · rcases lt_or_ge (c + 1) (P.nsub.getD i 0) with hlt | hge
    · exact hc3 c le_rfl hlt
    · have hc : c = P.nsub.getD i 0 - 1 := by omega
      rw [hc]
      unfold hiR
      rw [hhiN i hi30]
      exact hhi'

theorem pieceOf_lt (hG : P.Good) {t : ℝ} (ht : InRange t) : P.pieceOf t < P.count :=
  (pieceOf_spec hG ht).1

theorem parent_pieceOf (hG : P.Good) {t : ℝ} (ht : InRange t) :
    P.parent.getD (P.pieceOf t) 0 = bandOf t :=
  (pieceOf_spec hG ht).2.1

theorem loR_pieceOf_le (hG : P.Good) {t : ℝ} (ht : InRange t) : P.loR (P.pieceOf t) ≤ t :=
  (pieceOf_spec hG ht).2.2.1

theorem le_hiR_pieceOf (hG : P.Good) {t : ℝ} (ht : InRange t) : t ≤ P.hiR (P.pieceOf t) :=
  (pieceOf_spec hG ht).2.2.2

end Spec

/-! ## Refinement -/

/-- The finer table `Q` refines `P` band by band through `up` (the piece of `P` containing a piece of `Q`): within
band `i`, the image of the `j`-th piece of `Q` is a piece of `P` of the same band; when it is not the first piece of
`P` in the band, the `Q`-piece is not the first either and the previous `P`-edge is at or below the previous
`Q`-edge; when it is not the last, the `Q`-piece is not the last either and the `Q`-edge is at or below the `P`-edge. -/
def Refines (Q P : Pieces) (up : List ℕ) : Prop :=
  ∀ i < 30, ∀ j < Q.nsub.getD i 0,
    P.first.getD i 0 ≤ up.getD (Q.first.getD i 0 + j) 0 ∧
    up.getD (Q.first.getD i 0 + j) 0 < P.first.getD i 0 + P.nsub.getD i 0 ∧
    (P.first.getD i 0 < up.getD (Q.first.getD i 0 + j) 0 →
      0 < j ∧ P.hi.getD (up.getD (Q.first.getD i 0 + j) 0 - 1) 0 ≤ Q.hi.getD (Q.first.getD i 0 + (j - 1)) 0) ∧
    (up.getD (Q.first.getD i 0 + j) 0 + 1 < P.first.getD i 0 + P.nsub.getD i 0 →
      j + 1 < Q.nsub.getD i 0 ∧ Q.hi.getD (Q.first.getD i 0 + j) 0 ≤ P.hi.getD (up.getD (Q.first.getD i 0 + j) 0) 0)

instance (Q P : Pieces) (up : List ℕ) : Decidable (Refines Q P up) := by unfold Refines; infer_instance

/-- **The two tie-breakings agree**: if `Q` refines `P` through `up`, the piece of `P` of an activity in range is the
image of its piece of `Q`. -/
theorem pieceOf_refines {Q P : Pieces} {up : List ℕ} (hQ : Q.Good) (hP : P.Good) (hR : Refines Q P up)
    {t : ℝ} (ht : InRange t) : P.pieceOf t = up.getD (Q.pieceOf t) 0 := by
  obtain ⟨hi30, -, -⟩ := Atlas.bandOf_spec ht
  obtain ⟨hcQ, hQ2, hQ3⟩ := countOf_spec hQ ht
  obtain ⟨hcP, hP2, hP3⟩ := countOf_spec hP ht
  unfold pieceOf firstOf nsubOf at *
  generalize hi_def : bandOf t = i at *
  generalize hcQ_def : Q.countOf t = cQ at *
  generalize hcP_def : P.countOf t = cP at *
  obtain ⟨hu1, hu2, hu3, hu4⟩ := hR i hi30 cQ (by omega)
  generalize hu_def : up.getD (Q.first.getD i 0 + cQ) 0 = u at *
  obtain ⟨d, rfl⟩ : ∃ d, u = P.first.getD i 0 + d := ⟨u - P.first.getD i 0, by omega⟩
  rcases lt_trichotomy cP d with hlt | heq | hgt
  · -- `cP < d`: the `P`-edge below `u` is below `t`, but `t ≤ hi (fP + cP) ≤` that edge
    exfalso
    obtain ⟨hcQpos, hle⟩ := hu3 (by omega)
    rw [show P.first.getD i 0 + d - 1 = P.first.getD i 0 + (d - 1) by omega] at hle
    have h1 : Q.hiR (Q.first.getD i 0 + (cQ - 1)) < t := hQ2 (cQ - 1) (by omega)
    have h2 : t ≤ P.hiR (P.first.getD i 0 + cP) := hP3 cP le_rfl (by omega)
    have h3 : P.hi.getD (P.first.getD i 0 + cP) 0 ≤ P.hi.getD (P.first.getD i 0 + (d - 1)) 0 :=
      hi_le_hi hP hi30 (by omega) (by omega)
    unfold hiR at h1 h2
    have h4 : ((P.hi.getD (P.first.getD i 0 + (d - 1)) 0 : ℚ) : ℝ) ≤
        ((Q.hi.getD (Q.first.getD i 0 + (cQ - 1)) 0 : ℚ) : ℝ) := by exact_mod_cast hle
    have h5 : ((P.hi.getD (P.first.getD i 0 + cP) 0 : ℚ) : ℝ) ≤
        ((P.hi.getD (P.first.getD i 0 + (d - 1)) 0 : ℚ) : ℝ) := by exact_mod_cast h3
    linarith
  · rw [heq]
  · -- `d < cP`: `t ≤ hi (fQ + cQ) ≤ hi (fP + d) ≤ hi (fP + cP − 1) < t`
    exfalso
    obtain ⟨hcQlt, hle⟩ := hu4 (by omega)
    have h1 : t ≤ Q.hiR (Q.first.getD i 0 + cQ) := hQ3 cQ le_rfl hcQlt
    have h2 : P.hiR (P.first.getD i 0 + (cP - 1)) < t := hP2 (cP - 1) (by omega)
    have h3 : P.hi.getD (P.first.getD i 0 + d) 0 ≤ P.hi.getD (P.first.getD i 0 + (cP - 1)) 0 :=
      hi_le_hi hP hi30 (by omega) (by omega)
    unfold hiR at h1 h2
    have h4 : ((Q.hi.getD (Q.first.getD i 0 + cQ) 0 : ℚ) : ℝ) ≤
        ((P.hi.getD (P.first.getD i 0 + d) 0 : ℚ) : ℝ) := by exact_mod_cast hle
    have h5 : ((P.hi.getD (P.first.getD i 0 + d) 0 : ℚ) : ℝ) ≤
        ((P.hi.getD (P.first.getD i 0 + (cP - 1)) 0 : ℚ) : ℝ) := by exact_mod_cast h3
    linarith

end Pieces

end Erdos993Lean.Analytic.Ladder
