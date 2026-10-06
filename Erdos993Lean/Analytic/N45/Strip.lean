import Erdos993Lean.Analytic.N45.Profile
import Erdos993Lean.Analytic.N45.Mono
import Erdos993Lean.Analytic.N48.Strip

/-!
# O4 for `P45` from the piece checks: the n ≥ 45 strip and lane A20's `P48`

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A21.  Sources: lane A9's atlas checker and its soundness
(`Erdos993Lean/Analytic/Atlas/{Checker,Sound,Profile,Hyps}.lean`, reused, not re-proved), lane A20's
`Erdos993Lean/Analytic/N48/Strip.lean` (`piece48_of_band`, whose proof is adapted here to the piece-wise caps),
lane R4X's trial strips `LEAN/r4x/atlas45_trial/` and this lane's two strips (`REACH_BELOW_52.md` §5(e), §6: the boxes
over `[floor(n ≥ 45), floor(n ≥ 48)]` on the 30 pieces where the floor drops, with the piece's caps and rates and the
box's upper activity as tail base).

* `rates45_old`, `rates45_new`: the piece rates are the parent band's, with the ladder rate at `t = 0` on the rows.
* **`piece45_of_band`**: a piece passing `bandOK (piece45Band p) lamBox (piece45Cap p)` gives T1's explicit
  threshold for `P45` at every activity of piece `p` and every `m` from `P45`'s floor to `P48`'s (the strip top is
  the n ≥ 48 floor of the containing piece, `pieceOf48_eq`).  The tail hypothesis of `Atlas.band_explicitThreshold`:
  for `t_0 = 0` on a row, `tailFn45 ≤ e^{−ℓ_new m}(1 + t)^r ≤ e^{−ℓ_new m}(1 + Λ_b)^r`; otherwise
  `tailFn45 ≤ tailFn48 ≤ tailFnAct` and lane A9's `tailFnAct_le` with the base `Λ_b = lamBox b ≥ t`.
* **`explicitThreshold_small_P45_of_checks`**: T1's explicit threshold for `P45` at every activity in range and every
  `P45.mfloor t ≤ m < 400`, from the piece checks (where the floor drops) and the same statement for `P48` (lane A20's
  strip, lane A19's strip and lane A9's atlas), transported to the smaller caps by `explicitThreshold_cap_mono`
  (`θ`, `D` at `n ≥ 45` are at most Profile30's) and to the smaller tail `tailFn45 ≤ tailFn48` by lane A20's
  `explicitThreshold_tail_mono`.
* `hD45`, `hθ45`, `htail45`, **`thresholdNoValley_P45_of`**: O4 (`ThresholdNoValley P45`) from T1 and the explicit
  threshold on `m < 400`, the large-mean theorem on `m ≥ 400`.

All results here use only `propext`, `Classical.choice`, `Quot.sound` (the checks are hypotheses).

Scalarity check: the strip floor `mmin45_p` (the expected free count `m`, produced by O5 at `n ≥ 45`) and the strip
top `mmin48` of the containing piece (the lower edge of lane A20's strip) are consumed only as the `m`-range of the
piece's cover; each box's dual summarizes the fibre lower bound `h(M)` of T1's pointwise inequality (consumed by
`Atlas.box_explicitThreshold`); the tail base `Λ_b` and the rates summarize the Laplace transform of `M` (O3,
`N45/Tail.lean`); the caps `θ`, `D` are the O2/O1 objects of the piece (`N45/Analytic.lean`).
-/

namespace Erdos993Lean.Analytic.N45

open Profile30 Atlas

/-- The piece rates away from the ladder rows are the parent band's (kernel `decide`). -/
theorem rates45_old : ∀ p < 46, ∀ k < 5, (k ≠ 0 ∨ Data.newEll.getD p 0 = 0) →
    (Data.rates45.getD p []).getD k 0 = (bandAt (Data.pieceParent.getD p 0)).ell.getD k 0 := by
  decide +kernel

/-- On a ladder row the rate at `t = 0` is the row's rate (kernel `decide`). -/
theorem rates45_new : ∀ p < 46, Data.newEll.getD p 0 ≠ 0 →
    (Data.rates45.getD p []).getD 0 0 = Data.newEll.getD p 0 := by
  decide +kernel

/-- **A piece of the n ≥ 45 strip passing with the box tail base gives T1's explicit threshold for `P45`** at every
activity `t` of piece `p` and every `m ∈ [P45.mfloor t, P48.mfloor t]`. -/
theorem piece45_of_band {p : ℕ} (hp : p < 46) {boxes : List Box} {slabs : List Slab}
    (hok : bandOK (Data.piece45Band p) lamBox (Data.piece45Cap p) boxes slabs = true) {t : ℝ}
    (ht : InRange t) (htp : pieceOf t = p) {m : ℝ} (hm : P45.mfloor t ≤ m)
    (hm' : m ≤ N48.P48.mfloor t) :
    ExplicitThreshold (actQ t) m (P45.θb t) (P45.Db t) (P45.Tb t m) (P45.M1b t m) := by
  obtain ⟨-, hpar, hlo, hhi⟩ := pieceOf_spec ht
  have h48 := pieceOf48_eq ht
  rw [htp] at hpar hlo hhi h48
  unfold loR at hlo
  unfold hiR at hhi
  have hbi : bandOf t < 30 := (Atlas.bandOf_spec ht).1
  have ht0 : 0 ≤ t := by have := ht.1; linarith
  have hθ : P45.θb t = (((Data.piece45Band p).theta : ℚ) : ℝ) := by
    show ((Data.theta45.getD (pieceOf t) 0 : ℚ) : ℝ) = ((Data.theta45.getD p 0 : ℚ) : ℝ)
    rw [htp]
  have hD : P45.Db t = (((Data.piece45Band p).D : ℚ) : ℝ) := by
    show ((Data.D45.getD (pieceOf t) 0 : ℚ) : ℝ) = ((Data.D45.getD p 0 : ℚ) : ℝ)
    rw [htp]
  have hM1 : P45.M1b t m = ⌈m⌉₊ + 1 := rfl
  rw [hθ, hD, hM1]
  refine band_explicitThreshold (band := Data.piece45Band p) hok ?_ ?_ ?_ ?_ (P45.Tb t m) ?_ ?_
  · show actQ ((Data.pieceLo.getD p 0 : ℚ) : ℝ) ≤ actQ t
    have h0 : (0 : ℝ) ≤ ((Data.pieceLo.getD p 0 : ℚ) : ℝ) := by exact_mod_cast (pieceLo_pos p hp).le
    exact actQ_le_actQ h0 hlo
  · show actQ t ≤ actQ ((Data.pieceHi.getD p 0 : ℚ) : ℝ)
    exact actQ_le_actQ ht0 hhi
  · show ((Data.mmin45.getD p 0 : ℚ) : ℝ) ≤ m
    rw [P45_mfloor, htp] at hm
    exact hm
  · show m ≤ ((N48.Data.mmin48.getD (Data.pieceUp.getD p 0) 0 : ℚ) : ℝ)
    rw [N48.P48_mfloor, h48] at hm'
    exact hm'
  · intro r
    exact tailFn45_le_one t m r
  · intro b hb _ hqb' r k hk
    have hqh1 : ((b.qh : ℚ) : ℝ) < 1 := by exact_mod_cast (bandOK_boxes hok b hb).2
    have htΛ : t ≤ ((lamBox b : ℚ) : ℝ) := by
      have h1 := le_lam_of_actQ_le ht0 hqh1 hqb'
      unfold lamBox
      push_cast
      exact h1
    show tailFn45 t m r ≤ Real.exp (-((((Data.rates45.getD p []).getD k 0 : ℚ) : ℝ) * m)) *
      ((1 + ((lamBox b : ℚ) : ℝ)) / (1 + ((lamBox b : ℚ) : ℝ) * ((Atlas.tvals.getD k 0 : ℚ) : ℝ))) ^ r
    by_cases hnew : k = 0 ∧ Data.newEll.getD p 0 ≠ 0
    · -- the ladder row at `t_0 = 0`
      obtain ⟨rfl, hne⟩ := hnew
      rw [rates45_new p hp hne]
      have hne' : Data.newEll.getD (pieceOf t) 0 ≠ 0 := by rw [htp]; exact hne
      have h1 := tailFn45_le_new hne' m r
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
      rw [rates45_old p hp k hk hold, hpar]
      have h := (tailFnAct_le ht0 hbi htΛ m r).2 k hk
      exact (tailFn45_le_act t m r).trans h

/-- **T1's explicit threshold for `P45` on bounded `m`** (the `hsmall` hypothesis of `thresholdNoValley_of_split`),
from the n ≥ 45 piece checks (on the pieces whose floor drops) and the same statement for `P48` (arbitrary data;
standard axioms). -/
theorem explicitThreshold_small_P45_of_checks (sb : ℕ → List Box) (ss : ℕ → List Slab)
    (hs : ∀ p < 46, Data.mmin45.getD p 0 < Data.piece45Cap p →
      bandOK (Data.piece45Band p) lamBox (Data.piece45Cap p) (sb p) (ss p) = true)
    (h48 : ∀ t, InRange t → ∀ m, N48.P48.mfloor t ≤ m → m < 400 →
      ExplicitThreshold (actQ t) m (N48.P48.θb t) (N48.P48.Db t) (N48.P48.Tb t m) (N48.P48.M1b t m)) :
    ∀ t, InRange t → ∀ m, P45.mfloor t ≤ m → m < 400 →
      ExplicitThreshold (actQ t) m (P45.θb t) (P45.Db t) (P45.Tb t m) (P45.M1b t m) := by
  intro t ht m hm hm'
  obtain ⟨hp, -, -, -⟩ := pieceOf_spec ht
  have hq : 0 ≤ actQ t * (1 - actQ t) := by
    obtain ⟨h1, h2⟩ := actQ_mem_of_inRange ht
    nlinarith
  have hm0 : 0 ≤ m := (P45_mfloor_nonneg ht).trans hm
  have above : N48.P48.mfloor t ≤ m →
      ExplicitThreshold (actQ t) m (P45.θb t) (P45.Db t) (P45.Tb t m) (P45.M1b t m) := fun h => by
    have h1 := h48 t ht m h hm'
    have h2 := explicitThreshold_cap_mono h1 hq hm0 (P45_θb_le ht) (P45_Db_le ht)
    exact N48.explicitThreshold_tail_mono h2 (fun M' _ => tailFn45_le_48 t m M')
  rcases le_total m (N48.P48.mfloor t) with h | h
  · rcases lt_or_ge (Data.mmin45.getD (pieceOf t) 0) (Data.piece45Cap (pieceOf t)) with hlt | hge
    · exact piece45_of_band hp (hs _ hp hlt) ht rfl hm h
    · -- the floor does not drop on this piece: `m ≥ mmin45 ≥ cap = P48.mfloor t`
      apply above
      rw [N48.P48_mfloor, pieceOf48_eq ht]
      rw [P45_mfloor] at hm
      have hge' : ((Data.piece45Cap (pieceOf t) : ℚ) : ℝ) ≤ ((Data.mmin45.getD (pieceOf t) 0 : ℚ) : ℝ) := by
        exact_mod_cast hge
      unfold Data.piece45Cap at hge'
      exact hge'.trans hm
  · exact above h

/-- The profile's `D` at `n ≥ 45` (hypothesis `hD` of `thresholdNoValley_of_split`): `0 ≤ D ≤ 8/5`. -/
theorem hD45 : ∀ t, InRange t → 0 ≤ P45.Db t ∧ P45.Db t ≤ 8 / 5 := fun t ht =>
  ⟨P45_Db_nonneg ht, (P45_Db_le ht).trans (profile30_hD t ht).2⟩

/-- The profile's `θ` at `n ≥ 45` (hypothesis `hθ` of `thresholdNoValley_of_split`): at most Profile30's. -/
theorem hθ45 : ∀ t, InRange t → 0 ≤ P45.θb t ∧
    ((3 / 8 ≤ actQ t ∧ actQ t ≤ 8 / 13 ∧ P45.θb t ≤ 7 / 10) ∨
      ((actQ t ≤ 3 / 8 ∨ 8 / 13 ≤ actQ t) ∧ P45.θb t ≤ 1)) := by
  intro t ht
  obtain ⟨-, h⟩ := profile30_hθ t ht
  refine ⟨P45_θb_nonneg ht, ?_⟩
  rcases h with ⟨a, b, c⟩ | ⟨a, c⟩
  · exact Or.inl ⟨a, b, (P45_θb_le ht).trans c⟩
  · exact Or.inr ⟨a, (P45_θb_le ht).trans c⟩

/-- **The third-mean tail of `P45`** (hypothesis `htail` of `thresholdNoValley_of_split`): for `m ≥ 400`, some
`r < M1` with `m/3 ≤ r + 1` has `T(λ, m, r) ≤ e^{−m/30}` (lane A20's `htail48` and `tailFn45 ≤ tailFn48`). -/
theorem htail45 : ∀ t, InRange t → ∀ m, 400 ≤ m →
    ∃ r : ℕ, r < P45.M1b t m ∧ m / 3 ≤ (r : ℝ) + 1 ∧ P45.Tb t m r ≤ Real.exp (-(m / 30)) := by
  intro t ht m hm
  obtain ⟨r, hr, hr3, hT⟩ := N48.htail48 t ht m hm
  exact ⟨r, hr, hr3, (tailFn45_le_48 t m r).trans hT⟩

/-- **O4 for `P45`** (`ThresholdNoValley P45`) from T1's explicit threshold on `m < 400` (the atlas) and the
large-mean theorem on `m ≥ 400`. -/
theorem thresholdNoValley_P45_of
    (hsmall : ∀ t, InRange t → ∀ m, P45.mfloor t ≤ m → m < 400 →
      ExplicitThreshold (actQ t) m (P45.θb t) (P45.Db t) (P45.Tb t m) (P45.M1b t m)) :
    ThresholdNoValley P45 :=
  thresholdNoValley_of_split hsmall hD45 hθ45 htail45

end Erdos993Lean.Analytic.N45
