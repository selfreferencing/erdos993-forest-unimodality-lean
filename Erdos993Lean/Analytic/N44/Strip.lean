import Erdos993Lean.Analytic.N44.Profile
import Erdos993Lean.Analytic.N45.Strip

/-!
# O4 for `P44` from the piece checks: the n ≥ 44 strip and `P45`

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A21.  Sources: lane A9's atlas checker and its soundness,
this lane's `N45/Strip.lean` (whose proofs are copied with `P45` in the role of `P48`), lane R4X's trial strips
`LEAN/r4x/atlas44_trial/` and this lane's strip on `[6/5, 49/40]` (the boxes over `[floor(n ≥ 44), floor(n ≥ 45)]` on the
27 pieces where the floor drops, with the piece's caps and rates and the box's upper activity as tail base).

* **`piece44_of_band`**: a piece passing `bandOK (piece44Band p) lamBox (piece44Cap p)` gives T1's explicit threshold
  for `P44` at every activity of piece `p` and every `m` from `P44`'s floor to `P45`'s (the strip top is the n ≥ 45
  floor of the containing piece, `pieceOf45_eq`).
* **`explicitThreshold_small_P44_of_checks`**: from the piece checks and the same statement for `P45`, transported by
  `N45.explicitThreshold_cap_mono` (`θ`, `D` at `n ≥ 44` are at most those at `n ≥ 45`) and lane A20's
  `explicitThreshold_tail_mono` (`tailFn44 ≤ tailFn45`).
* `hD44`, `hθ44`, `htail44`, **`thresholdNoValley_P44_of`**: O4 (`ThresholdNoValley P44`).

All results here use only `propext`, `Classical.choice`, `Quot.sound` (the checks are hypotheses).

Scalarity check: as `N45/Strip.lean`.
-/

namespace Erdos993Lean.Analytic.N44

open Profile30 Atlas

/-- The piece rates away from the ladder rows are the parent band's (kernel `decide`). -/
theorem rates44_old : ∀ p < 55, ∀ k < 5, (k ≠ 0 ∨ Data.newEll.getD p 0 = 0) →
    (Data.rates44.getD p []).getD k 0 = (bandAt (Data.pieceParent.getD p 0)).ell.getD k 0 := by
  decide +kernel

/-- On a ladder row the rate at `t = 0` is the row's rate (kernel `decide`). -/
theorem rates44_new : ∀ p < 55, Data.newEll.getD p 0 ≠ 0 →
    (Data.rates44.getD p []).getD 0 0 = Data.newEll.getD p 0 := by
  decide +kernel

/-- **A piece of the n ≥ 44 strip passing with the box tail base gives T1's explicit threshold for `P44`** at every
activity `t` of piece `p` and every `m ∈ [P44.mfloor t, P45.mfloor t]`. -/
theorem piece44_of_band {p : ℕ} (hp : p < 55) {boxes : List Box} {slabs : List Slab}
    (hok : bandOK (Data.piece44Band p) lamBox (Data.piece44Cap p) boxes slabs = true) {t : ℝ}
    (ht : InRange t) (htp : pieceOf t = p) {m : ℝ} (hm : P44.mfloor t ≤ m)
    (hm' : m ≤ N45.P45.mfloor t) :
    ExplicitThreshold (actQ t) m (P44.θb t) (P44.Db t) (P44.Tb t m) (P44.M1b t m) := by
  obtain ⟨-, hpar, hlo, hhi⟩ := pieceOf_spec ht
  have h45 := pieceOf45_eq ht
  rw [htp] at hpar hlo hhi h45
  unfold loR at hlo
  unfold hiR at hhi
  have hbi : bandOf t < 30 := (Atlas.bandOf_spec ht).1
  have ht0 : 0 ≤ t := by have := ht.1; linarith
  have hθ : P44.θb t = (((Data.piece44Band p).theta : ℚ) : ℝ) := by
    show ((Data.theta44.getD (pieceOf t) 0 : ℚ) : ℝ) = ((Data.theta44.getD p 0 : ℚ) : ℝ)
    rw [htp]
  have hD : P44.Db t = (((Data.piece44Band p).D : ℚ) : ℝ) := by
    show ((Data.D44.getD (pieceOf t) 0 : ℚ) : ℝ) = ((Data.D44.getD p 0 : ℚ) : ℝ)
    rw [htp]
  have hM1 : P44.M1b t m = ⌈m⌉₊ + 1 := rfl
  rw [hθ, hD, hM1]
  refine band_explicitThreshold (band := Data.piece44Band p) hok ?_ ?_ ?_ ?_ (P44.Tb t m) ?_ ?_
  · show actQ ((Data.pieceLo.getD p 0 : ℚ) : ℝ) ≤ actQ t
    have h0 : (0 : ℝ) ≤ ((Data.pieceLo.getD p 0 : ℚ) : ℝ) := by exact_mod_cast (pieceLo_pos p hp).le
    exact actQ_le_actQ h0 hlo
  · show actQ t ≤ actQ ((Data.pieceHi.getD p 0 : ℚ) : ℝ)
    exact actQ_le_actQ ht0 hhi
  · show ((Data.mmin44.getD p 0 : ℚ) : ℝ) ≤ m
    rw [P44_mfloor, htp] at hm
    exact hm
  · show m ≤ ((N45.Data.mmin45.getD (Data.pieceUp.getD p 0) 0 : ℚ) : ℝ)
    rw [N45.P45_mfloor, h45] at hm'
    exact hm'
  · intro r
    exact tailFn44_le_one t m r
  · intro b hb _ hqb' r k hk
    have hqh1 : ((b.qh : ℚ) : ℝ) < 1 := by exact_mod_cast (bandOK_boxes hok b hb).2
    have htΛ : t ≤ ((lamBox b : ℚ) : ℝ) := by
      have h1 := le_lam_of_actQ_le ht0 hqh1 hqb'
      unfold lamBox
      push_cast
      exact h1
    show tailFn44 t m r ≤ Real.exp (-((((Data.rates44.getD p []).getD k 0 : ℚ) : ℝ) * m)) *
      ((1 + ((lamBox b : ℚ) : ℝ)) / (1 + ((lamBox b : ℚ) : ℝ) * ((Atlas.tvals.getD k 0 : ℚ) : ℝ))) ^ r
    by_cases hnew : k = 0 ∧ Data.newEll.getD p 0 ≠ 0
    · obtain ⟨rfl, hne⟩ := hnew
      rw [rates44_new p hp hne]
      have hne' : Data.newEll.getD (pieceOf t) 0 ≠ 0 := by rw [htp]; exact hne
      have h1 := tailFn44_le_new hne' m r
      have e1 : newEllR t = ((Data.newEll.getD p 0 : ℚ) : ℝ) := by unfold newEllR; rw [htp]
      rw [e1] at h1
      have e2 : ((Atlas.tvals.getD 0 0 : ℚ) : ℝ) = 0 := by norm_num [Atlas.tvals]
      rw [e2, mul_zero, add_zero, div_one]
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
      exact pow_le_pow_left₀ (by linarith) (by linarith) r
    · have hold : k ≠ 0 ∨ Data.newEll.getD p 0 = 0 := by
        by_contra hc
        push_neg at hc
        exact hnew hc
      rw [rates44_old p hp k hk hold, hpar]
      have h := (tailFnAct_le ht0 hbi htΛ m r).2 k hk
      exact (tailFn44_le_act t m r).trans h

/-- **T1's explicit threshold for `P44` on bounded `m`**, from the n ≥ 44 piece checks (on the pieces whose floor
drops) and the same statement for `P45` (arbitrary data; standard axioms). -/
theorem explicitThreshold_small_P44_of_checks (sb : ℕ → List Box) (ss : ℕ → List Slab)
    (hs : ∀ p < 55, Data.mmin44.getD p 0 < Data.piece44Cap p →
      bandOK (Data.piece44Band p) lamBox (Data.piece44Cap p) (sb p) (ss p) = true)
    (h45 : ∀ t, InRange t → ∀ m, N45.P45.mfloor t ≤ m → m < 400 →
      ExplicitThreshold (actQ t) m (N45.P45.θb t) (N45.P45.Db t) (N45.P45.Tb t m) (N45.P45.M1b t m)) :
    ∀ t, InRange t → ∀ m, P44.mfloor t ≤ m → m < 400 →
      ExplicitThreshold (actQ t) m (P44.θb t) (P44.Db t) (P44.Tb t m) (P44.M1b t m) := by
  intro t ht m hm hm'
  obtain ⟨hp, -, -, -⟩ := pieceOf_spec ht
  have hq : 0 ≤ actQ t * (1 - actQ t) := by
    obtain ⟨h1, h2⟩ := actQ_mem_of_inRange ht
    nlinarith
  have hm0 : 0 ≤ m := (P44_mfloor_nonneg ht).trans hm
  have above : N45.P45.mfloor t ≤ m →
      ExplicitThreshold (actQ t) m (P44.θb t) (P44.Db t) (P44.Tb t m) (P44.M1b t m) := fun h => by
    have h1 := h45 t ht m h hm'
    have h2 := N45.explicitThreshold_cap_mono h1 hq hm0 (P44_θb_le ht) (P44_Db_le ht)
    exact N48.explicitThreshold_tail_mono h2 (fun M' _ => tailFn44_le_45 t m M')
  rcases le_total m (N45.P45.mfloor t) with h | h
  · rcases lt_or_ge (Data.mmin44.getD (pieceOf t) 0) (Data.piece44Cap (pieceOf t)) with hlt | hge
    · exact piece44_of_band hp (hs _ hp hlt) ht rfl hm h
    · apply above
      rw [N45.P45_mfloor, pieceOf45_eq ht]
      rw [P44_mfloor] at hm
      have hge' : ((Data.piece44Cap (pieceOf t) : ℚ) : ℝ) ≤ ((Data.mmin44.getD (pieceOf t) 0 : ℚ) : ℝ) := by
        exact_mod_cast hge
      unfold Data.piece44Cap at hge'
      exact hge'.trans hm
  · exact above h

/-- The profile's `D` at `n ≥ 44`: `0 ≤ D ≤ 8/5`. -/
theorem hD44 : ∀ t, InRange t → 0 ≤ P44.Db t ∧ P44.Db t ≤ 8 / 5 := fun t ht =>
  ⟨P44_Db_nonneg ht, (P44_Db_le ht).trans (N45.hD45 t ht).2⟩

/-- The profile's `θ` at `n ≥ 44`: at most that at `n ≥ 45`. -/
theorem hθ44 : ∀ t, InRange t → 0 ≤ P44.θb t ∧
    ((3 / 8 ≤ actQ t ∧ actQ t ≤ 8 / 13 ∧ P44.θb t ≤ 7 / 10) ∨
      ((actQ t ≤ 3 / 8 ∨ 8 / 13 ≤ actQ t) ∧ P44.θb t ≤ 1)) := by
  intro t ht
  obtain ⟨-, h⟩ := N45.hθ45 t ht
  refine ⟨P44_θb_nonneg ht, ?_⟩
  rcases h with ⟨a, b, c⟩ | ⟨a, c⟩
  · exact Or.inl ⟨a, b, (P44_θb_le ht).trans c⟩
  · exact Or.inr ⟨a, (P44_θb_le ht).trans c⟩

/-- **The third-mean tail of `P44`** (from `N45.htail45` and `tailFn44 ≤ tailFn45`). -/
theorem htail44 : ∀ t, InRange t → ∀ m, 400 ≤ m →
    ∃ r : ℕ, r < P44.M1b t m ∧ m / 3 ≤ (r : ℝ) + 1 ∧ P44.Tb t m r ≤ Real.exp (-(m / 30)) := by
  intro t ht m hm
  obtain ⟨r, hr, hr3, hT⟩ := N45.htail45 t ht m hm
  exact ⟨r, hr, hr3, (tailFn44_le_45 t m r).trans hT⟩

/-- **O4 for `P44`** (`ThresholdNoValley P44`). -/
theorem thresholdNoValley_P44_of
    (hsmall : ∀ t, InRange t → ∀ m, P44.mfloor t ≤ m → m < 400 →
      ExplicitThreshold (actQ t) m (P44.θb t) (P44.Db t) (P44.Tb t m) (P44.M1b t m)) :
    ThresholdNoValley P44 :=
  thresholdNoValley_of_split hsmall hD44 hθ44 htail44

end Erdos993Lean.Analytic.N44
