import Erdos993Lean.Analytic.N48.Profile
import Erdos993Lean.Analytic.N48.Mono
import Erdos993Lean.Analytic.N52.Strip

/-!
# O4 for `P48` from the piece checks: the n ≥ 48 strip, lane A19's n ≥ 52 strip and lane A9's atlas

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A20.  Sources: lane A9's atlas checker and its soundness
(`Erdos993Lean/Analytic/Atlas/{Checker,Sound,Profile,Hyps}.lean`, reused, not re-proved), lane A19's
`Erdos993Lean/Analytic/N52/Strip.lean` (`strip_of_band`, whose proof is adapted here to the pieces and the tail
`tailFn48`), lane R4X's trial strips `LEAN/r4x/atlas48_trial/` and `atlas45_trial/` (`REACH_BELOW_52.md` §5(e), §6: the
boxes over `[floor(n ≥ 48), floor(n ≥ 52)]` on the sub-band pieces, built with the box's upper activity as tail base and,
on the four pieces with a new O3 row, the new rate at `t = 0`).

* `rates48_old`, `rates48_new`: the piece rates are the parent band's, with the new rate at `t = 0` on the new rows.
* **`piece48_of_band`**: a piece passing `bandOK (piece48Band p) lamBox (piece48Cap p)` gives T1's explicit threshold
  for `P48` at every activity of piece `p` and every `m` from `P48`'s floor to `P52`'s.  The tail hypothesis of
  `Atlas.band_explicitThreshold`: for `t_0 = 0` on a new row, `tailFn48 ≤ e^{−ℓ_new m}(1 + t)^r ≤ e^{−ℓ_new m}(1 + Λ_b)^r`;
  otherwise `tailFn48 ≤ tailFnAct` and lane A9's `tailFnAct_le` with the base `Λ_b = lamBox b ≥ t`.
* **`explicitThreshold_small_P48_of_checks`**: T1's explicit threshold for `P48` at every activity in range and every
  `P48.mfloor t ≤ m < 400`, from the 31 piece checks (pieces 13 and 14 keep the n ≥ 52 floor) and the same statement for
  `P52` (lane A19's strip and lane A9's atlas), transported to the smaller tail `tailFn48 ≤ tailFnAct` by
  `explicitThreshold_tail_mono`.
* **`thresholdNoValley_P48_of`**: O4 (`ThresholdNoValley P48`) from T1 and the explicit threshold on `m < 400`, the
  large-mean theorem on `m ≥ 400` (`htail48`: lane A19's `htail52` and `tailFn48 ≤ tailFnAct`).

All results here use only `propext`, `Classical.choice`, `Quot.sound` (the checks are hypotheses).

Scalarity check: the strip floor `mmin48_p` (the expected free count `m`, produced by O5 at `n ≥ 48`) and the strip
top `mmin52` of the parent band (the lower edge of lane A19's strip) are consumed only as the `m`-range of the piece's
cover; each box's dual summarizes the fibre lower bound `h(M)` of T1's pointwise inequality (consumed by
`Atlas.box_explicitThreshold`); the tail base `Λ_b` and the rates summarize the Laplace transform of `M` (O3,
`N48/Tail.lean`).
-/

namespace Erdos993Lean.Analytic.N48

open Profile30 Atlas

/-- The piece rates away from the new rows are the parent band's (kernel `decide`). -/
theorem rates48_old : ∀ p < 33, ∀ k < 5, (k ≠ 0 ∨ Data.newEll.getD p 0 = 0) →
    (Data.rates48.getD p []).getD k 0 = (bandAt (Data.pieceParent.getD p 0)).ell.getD k 0 := by
  decide +kernel

/-- On a new row the rate at `t = 0` is the new rate (kernel `decide`). -/
theorem rates48_new : ∀ p < 33, Data.newEll.getD p 0 ≠ 0 →
    (Data.rates48.getD p []).getD 0 0 = Data.newEll.getD p 0 := by
  decide +kernel

/-- The piece edges are positive (kernel `decide`). -/
theorem pieceLo_pos : ∀ p < 33, 0 < Data.pieceLo.getD p 0 := by decide +kernel

/-- The checker's top of the strip of piece `p` is the n ≥ 52 floor of its parent band. -/
theorem piece48Cap_eq {p : ℕ} (hp : p < 33) :
    Data.piece48Cap p = N52.mmin52.getD (Data.pieceParent.getD p 0) 0 :=
  N52.stripFloor_eq _ (piece_in_parent p hp).1

/-- On pieces 13 and 14 the floor at `n ≥ 48` is the floor at `n ≥ 52` of the parent band (kernel `decide`). -/
theorem mmin48_eq_mmin52_1314 :
    Data.mmin48.getD 13 0 = N52.mmin52.getD (Data.pieceParent.getD 13 0) 0 ∧
      Data.mmin48.getD 14 0 = N52.mmin52.getD (Data.pieceParent.getD 14 0) 0 := by
  decide +kernel

/-- **A piece of the n ≥ 48 strip passing with the box tail base gives T1's explicit threshold for `P48`** at every
activity `t` of piece `p` and every `m ∈ [P48.mfloor t, P52.mfloor t]`. -/
theorem piece48_of_band {p : ℕ} (hp : p < 33) {boxes : List Box} {slabs : List Slab}
    (hok : bandOK (Data.piece48Band p) lamBox (Data.piece48Cap p) boxes slabs = true) {t : ℝ}
    (ht : InRange t) (htp : pieceOf t = p) {m : ℝ} (hm : P48.mfloor t ≤ m)
    (hm' : m ≤ N52.P52.mfloor t) :
    ExplicitThreshold (actQ t) m (P48.θb t) (P48.Db t) (P48.Tb t m) (P48.M1b t m) := by
  obtain ⟨-, hpar, hlo, hhi⟩ := pieceOf_spec ht
  rw [htp] at hpar hlo hhi
  unfold loR at hlo
  unfold hiR at hhi
  have hbi : bandOf t < 30 := (Atlas.bandOf_spec ht).1
  have hpi : Data.pieceParent.getD p 0 < 30 := (piece_in_parent p hp).1
  have hag := bandAt_eq _ hpi
  have ht0 : 0 ≤ t := by have := ht.1; linarith
  have hθ : P48.θb t = (((Data.piece48Band p).theta : ℚ) : ℝ) := by
    show ((θt.getD (bandOf t) 1 : ℚ) : ℝ) = (((bandAt (Data.pieceParent.getD p 0)).theta : ℚ) : ℝ)
    rw [← hpar, hag.2.1]
  have hD : P48.Db t = (((Data.piece48Band p).D : ℚ) : ℝ) := by
    show ((Dt.getD (bandOf t) (8 / 5) : ℚ) : ℝ) = (((bandAt (Data.pieceParent.getD p 0)).D : ℚ) : ℝ)
    rw [← hpar, hag.1]
  have hM1 : P48.M1b t m = ⌈m⌉₊ + 1 := rfl
  rw [hθ, hD, hM1]
  refine band_explicitThreshold (band := Data.piece48Band p) hok ?_ ?_ ?_ ?_ (P48.Tb t m) ?_ ?_
  · show actQ ((Data.pieceLo.getD p 0 : ℚ) : ℝ) ≤ actQ t
    have h0 : (0 : ℝ) ≤ ((Data.pieceLo.getD p 0 : ℚ) : ℝ) := by exact_mod_cast (pieceLo_pos p hp).le
    exact actQ_le_actQ h0 hlo
  · show actQ t ≤ actQ ((Data.pieceHi.getD p 0 : ℚ) : ℝ)
    exact actQ_le_actQ ht0 hhi
  · show ((Data.mmin48.getD p 0 : ℚ) : ℝ) ≤ m
    rw [P48_mfloor, htp] at hm
    exact hm
  · show m ≤ ((Data.piece48Cap p : ℚ) : ℝ)
    rw [piece48Cap_eq hp, hpar]
    rw [N52.P52_mfloor] at hm'
    exact hm'
  · intro r
    exact tailFn48_le_one t m r
  · intro b hb _ hqb' r k hk
    have hqh1 : ((b.qh : ℚ) : ℝ) < 1 := by exact_mod_cast (bandOK_boxes hok b hb).2
    have htΛ : t ≤ ((lamBox b : ℚ) : ℝ) := by
      have h1 := le_lam_of_actQ_le ht0 hqh1 hqb'
      unfold lamBox
      push_cast
      exact h1
    show tailFn48 t m r ≤ Real.exp (-((((Data.rates48.getD p []).getD k 0 : ℚ) : ℝ) * m)) *
      ((1 + ((lamBox b : ℚ) : ℝ)) / (1 + ((lamBox b : ℚ) : ℝ) * ((Atlas.tvals.getD k 0 : ℚ) : ℝ))) ^ r
    by_cases hnew : k = 0 ∧ Data.newEll.getD p 0 ≠ 0
    · -- the new row at `t_0 = 0`
      obtain ⟨rfl, hne⟩ := hnew
      rw [rates48_new p hp hne]
      have hne' : Data.newEll.getD (pieceOf t) 0 ≠ 0 := by rw [htp]; exact hne
      have h1 := tailFn48_le_new hne' m r
      have e1 : newEllR t = ((Data.newEll.getD p 0 : ℚ) : ℝ) := by unfold newEllR; rw [htp]
      rw [e1] at h1
      have e2 : ((Atlas.tvals.getD 0 0 : ℚ) : ℝ) = 0 := by norm_num [Atlas.tvals]
      rw [e2, mul_zero, add_zero, div_one]
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
      exact pow_le_pow_left₀ (by linarith) (by linarith) r
    · -- the parent's rates
      have hold : k ≠ 0 ∨ Data.newEll.getD p 0 = 0 := by
        by_contra hc
        push_neg at hc
        exact hnew hc
      rw [rates48_old p hp k hk hold, hpar]
      have h := (tailFnAct_le ht0 hbi htΛ m r).2 k hk
      exact (tailFn48_le_act t m r).trans h

/-- **T1's explicit threshold for `P48` on bounded `m`** (the `hsmall` hypothesis of `thresholdNoValley_of_split`),
from the n ≥ 48 piece checks and the same statement for `P52` (arbitrary data; standard axioms). -/
theorem explicitThreshold_small_P48_of_checks (sb : ℕ → List Box) (ss : ℕ → List Slab)
    (hs : ∀ p < 33, p ≠ 13 → p ≠ 14 →
      bandOK (Data.piece48Band p) lamBox (Data.piece48Cap p) (sb p) (ss p) = true)
    (h52 : ∀ t, InRange t → ∀ m, N52.P52.mfloor t ≤ m → m < 400 →
      ExplicitThreshold (actQ t) m (N52.P52.θb t) (N52.P52.Db t) (N52.P52.Tb t m) (N52.P52.M1b t m)) :
    ∀ t, InRange t → ∀ m, P48.mfloor t ≤ m → m < 400 →
      ExplicitThreshold (actQ t) m (P48.θb t) (P48.Db t) (P48.Tb t m) (P48.M1b t m) := by
  intro t ht m hm hm'
  obtain ⟨hp, hpar, -, -⟩ := pieceOf_spec ht
  have above : N52.P52.mfloor t ≤ m →
      ExplicitThreshold (actQ t) m (P48.θb t) (P48.Db t) (P48.Tb t m) (P48.M1b t m) := fun h =>
    explicitThreshold_tail_mono (h52 t ht m h hm') (fun M' _ => tailFn48_le_act t m M')
  rcases le_total m (N52.P52.mfloor t) with h | h
  · by_cases h1314 : pieceOf t = 13 ∨ pieceOf t = 14
    · -- the floors at 48 and 52 coincide on pieces 13 and 14
      apply above
      rw [N52.P52_mfloor, ← hpar]
      rw [P48_mfloor] at hm
      rcases h1314 with e | e
      · rw [e, ← mmin48_eq_mmin52_1314.1]
        rw [e] at hm
        exact hm
      · rw [e, ← mmin48_eq_mmin52_1314.2]
        rw [e] at hm
        exact hm
    · push_neg at h1314
      exact piece48_of_band hp (hs _ hp h1314.1 h1314.2) ht rfl hm h
  · exact above h

/-- **The third-mean tail of `P48`** (hypothesis `htail` of `thresholdNoValley_of_split`): for `m ≥ 400`, some
`r < M1` with `m/3 ≤ r + 1` has `T(λ, m, r) ≤ e^{−m/30}` (lane A19's `htail52` and `tailFn48 ≤ tailFnAct`). -/
theorem htail48 : ∀ t, InRange t → ∀ m, 400 ≤ m →
    ∃ r : ℕ, r < P48.M1b t m ∧ m / 3 ≤ (r : ℝ) + 1 ∧ P48.Tb t m r ≤ Real.exp (-(m / 30)) := by
  intro t ht m hm
  obtain ⟨r, hr, hr3, hT⟩ := N52.htail52 t ht m hm
  exact ⟨r, hr, hr3, (tailFn48_le_act t m r).trans hT⟩

/-- **O4 for `P48`** (`ThresholdNoValley P48`) from T1's explicit threshold on `m < 400` (the atlas) and the
large-mean theorem on `m ≥ 400` (Profile30's `D ≤ 8/5`, its `θ` targets and `htail48`). -/
theorem thresholdNoValley_P48_of
    (hsmall : ∀ t, InRange t → ∀ m, P48.mfloor t ≤ m → m < 400 →
      ExplicitThreshold (actQ t) m (P48.θb t) (P48.Db t) (P48.Tb t m) (P48.M1b t m)) :
    ThresholdNoValley P48 :=
  thresholdNoValley_of_split hsmall profile30_hD profile30_hθ htail48

end Erdos993Lean.Analytic.N48
