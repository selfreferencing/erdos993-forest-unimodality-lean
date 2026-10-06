import Erdos993Lean.Analytic.N52.Profile
import Erdos993Lean.Analytic.N52.Data.Params
import Erdos993Lean.Analytic.Atlas.Hyps
import Erdos993Lean.Analytic.AssemblyCore

/-!
# O4 for `P52` from the band checks: the n ≥ 52 strip and lane A9's atlas

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A19.  Sources: lane A9's atlas checker and its soundness
(`Erdos993Lean/Analytic/Atlas/{Checker,Sound,Profile,Hyps}.lean`, reused, not re-proved), lane R52's strip
(`LEAN/r52/REQUIREMENTS_52.md` §7: the boxes over `[floor(n ≥ 52), floor(n ≥ 61)]` on the 30 bands, built with the
box's own upper activity as tail base, `atlas_arb_r52.py: t_upper(m_l, q_h, …)`), and the large-mean theorem
(`thresholdNoValley_of_split`, `Erdos993Lean/Analytic/Assembly.lean`).

* `stripFloor_eq`: the checker's strip floor (`Data.stripFloor`, core Lean) is `mmin52` (kernel `decide`).
* **`strip_of_band`**: a strip band passing `bandOK (stripBand i) lamBox (stripCap i)` gives T1's explicit
  threshold for `P52` at every activity of band `i` and every `m` from `P52`'s floor to Profile30's.  The tail
  hypothesis of `Atlas.band_explicitThreshold` for a box `b` containing `q = q(t)` is lane A9's `Atlas.tailFnAct_le`
  with the base `Λ_b = lamBox b = q_h/(1 − q_h) ≥ t`.
* **`explicitThreshold_small_P52_of_checks`**: T1's explicit threshold for `P52` at every activity in range and every
  `P52.mfloor t ≤ m < 400`: the strip below Profile30's floor, lane A9's lower and upper atlases above it (through
  `Atlas.explicitThreshold_small_of_checks` for `Atlas.P30act`, which agrees with `P52` except for the floor).
* `tailFnAct_le_tailFn`, `htail52`: the third-mean tail of `P52` for `m ≥ 400` (lane A9's `profile30_htail` and the
  actual-activity tail below the band-edge tail).
* **`thresholdNoValley_P52_of`**: O4 (`ThresholdNoValley P52`) from T1 and the explicit threshold on `m < 400`, the
  large-mean theorem on `m ≥ 400`.

All results here use only `propext`, `Classical.choice`, `Quot.sound` (the band checks are hypotheses).

Scalarity check: the strip floor `mmin52_i` (the expected free count `m`, produced by O5 at `n ≥ 52`) and the strip
top `mmin_i` (Profile30's floor, the lower edge of lane A9's atlas) are consumed only as the `m`-range of the strip's
cover; each box's dual summarizes the fibre lower bound `h(M)` of T1's pointwise inequality and is consumed by
`Atlas.box_explicitThreshold`; the tail base `Λ_b` summarizes the Laplace transform of `M` at the actual activity
(O3's `tailFnAct`, `Inputs.lean`).
-/

namespace Erdos993Lean.Analytic.N52

open Profile30 Atlas

/-- The checker's strip floor is `mmin52` (kernel `decide`). -/
theorem stripFloor_eq : ∀ i < 30, Data.stripFloor.getD i 0 = mmin52.getD i 0 := by
  decide +kernel

/-- **A strip band passing with the box tail base gives T1's explicit threshold for `P52`** at every activity `t`
of band `i` and every `m ∈ [P52.mfloor t, Profile30.P.mfloor t]`. -/
theorem strip_of_band {i : ℕ} (hi : i < 30) {boxes : List Box} {slabs : List Slab}
    (hok : bandOK (Data.stripBand i) lamBox (Data.stripCap i) boxes slabs = true) {t : ℝ}
    (ht : InRange t) (hti : bandOf t = i) {m : ℝ} (hm : P52.mfloor t ≤ m)
    (hm' : m ≤ Profile30.P.mfloor t) :
    ExplicitThreshold (actQ t) m (P52.θb t) (P52.Db t) (P52.Tb t m) (P52.M1b t m) := by
  obtain ⟨-, hlo, hhi⟩ := Atlas.bandOf_spec ht
  have hag := bandAt_eq i hi
  rw [hti] at hlo hhi
  have ht0 : 0 ≤ t := le_trans (edgeR_pos i (by omega)).le hlo
  have hbi : bandOf t < 30 := by rw [hti]; exact hi
  have hθ : P52.θb t = (((Data.stripBand i).theta : ℚ) : ℝ) := by
    show ((θt.getD (bandOf t) 1 : ℚ) : ℝ) = (((bandAt i).theta : ℚ) : ℝ)
    rw [hti, hag.2.1]
  have hD : P52.Db t = (((Data.stripBand i).D : ℚ) : ℝ) := by
    show ((Dt.getD (bandOf t) (8 / 5) : ℚ) : ℝ) = (((bandAt i).D : ℚ) : ℝ)
    rw [hti, hag.1]
  have hM1 : P52.M1b t m = ⌈m⌉₊ + 1 := rfl
  rw [hθ, hD, hM1]
  refine band_explicitThreshold (band := Data.stripBand i) hok ?_ ?_ ?_ ?_ (P52.Tb t m) ?_ ?_
  · show actQ (((bandAt i).lamLo : ℚ) : ℝ) ≤ actQ t
    rw [hag.2.2.2.1]
    exact actQ_le_actQ (edgeR_pos i (by omega)).le hlo
  · show actQ t ≤ actQ (((bandAt i).lamHi : ℚ) : ℝ)
    rw [hag.2.2.2.2.1]
    exact actQ_le_actQ ht0 hhi
  · show ((Data.stripFloor.getD i 0 : ℚ) : ℝ) ≤ m
    rw [stripFloor_eq i hi]
    rw [P52_mfloor, hti] at hm
    exact hm
  · show m ≤ (((bandAt i).mmin : ℚ) : ℝ)
    rw [hag.2.2.2.2.2]
    have e : Profile30.P.mfloor t = ((mmin.getD (bandOf t) 0 : ℚ) : ℝ) := rfl
    rw [e, hti] at hm'
    exact hm'
  · intro r
    exact (tailFnAct_le ht0 hbi le_rfl m r).1
  · intro b hb _ hqb' r k hk
    have hqh1 : ((b.qh : ℚ) : ℝ) < 1 := by exact_mod_cast (bandOK_boxes hok b hb).2
    have htΛ : t ≤ ((lamBox b : ℚ) : ℝ) := by
      have h1 := le_lam_of_actQ_le ht0 hqh1 hqb'
      unfold lamBox
      push_cast
      exact h1
    have h := (tailFnAct_le ht0 hbi htΛ m r).2 k hk
    rw [hti] at h
    exact h

/-- **T1's explicit threshold for `P52` on bounded `m`** (the `hsmall` hypothesis of `thresholdNoValley_of_split`),
from the strip checks and lane A9's lower and upper band checks (arbitrary data; standard axioms). -/
theorem explicitThreshold_small_P52_of_checks (sb : ℕ → List Box) (ss : ℕ → List Slab)
    (hs : ∀ i < 30, bandOK (Data.stripBand i) lamBox (Data.stripCap i) (sb i) (ss i) = true)
    (lb : ℕ → List Box) (ls : ℕ → List Slab) (ub : ℕ → List Box) (us : ℕ → List Slab)
    (hl : ∀ i < 30, bandOK (bandAt i) (fun _ => (bandAt i).lamHi) 50 (lb i) (ls i) = true)
    (hu : ∀ i < 30, bandOK { bandAt i with mmin := 50 } (fun _ => (bandAt i).lamHi) 400 (ub i)
      (us i) = true) :
    ∀ t, InRange t → ∀ m, P52.mfloor t ≤ m → m < 400 →
      ExplicitThreshold (actQ t) m (P52.θb t) (P52.Db t) (P52.Tb t m) (P52.M1b t m) := by
  intro t ht m hm hm'
  have hi := (Atlas.bandOf_spec ht).1
  rcases le_total m (Profile30.P.mfloor t) with h | h
  · exact strip_of_band hi (hs _ hi) ht rfl hm h
  · exact explicitThreshold_small_of_checks lb ls ub us hl hu atlasProfile_P30act t ht m h hm'

/-- The actual-activity tail lies below Profile30's band-edge tail. -/
theorem tailFnAct_le_tailFn {t : ℝ} (ht : InRange t) (m : ℝ) (r : ℕ) :
    tailFnAct t m r ≤ tailFn t m r := by
  obtain ⟨hi, hlo, hhi⟩ := Atlas.bandOf_spec ht
  have ht0 : 0 ≤ t := le_trans (edgeR_pos _ (by omega)).le hlo
  have h := tailFnAct_le ht0 hi (Λ := hiEdge t) hhi m r
  have key : ∀ k < 5, tailFnAct t m r ≤ tailTerm t m r k := by
    intro k hk
    refine (h.2 k hk).trans (le_of_eq ?_)
    unfold tailTerm
    rw [ell_eq hi, tvals_getD]
  unfold tailFn
  exact le_min h.1 (le_min (key 0 (by norm_num)) (le_min (key 1 (by norm_num))
    (le_min (key 2 (by norm_num)) (le_min (key 3 (by norm_num)) (key 4 (by norm_num))))))

/-- **The third-mean tail of `P52`** (hypothesis `htail` of `thresholdNoValley_of_split`): for `m ≥ 400`, some
`r < M1` with `m/3 ≤ r + 1` has `T(λ, m, r) ≤ e^{−m/30}` (lane A9's `profile30_htail` and `tailFnAct_le_tailFn`). -/
theorem htail52 : ∀ t, InRange t → ∀ m, 400 ≤ m →
    ∃ r : ℕ, r < P52.M1b t m ∧ m / 3 ≤ (r : ℝ) + 1 ∧ P52.Tb t m r ≤ Real.exp (-(m / 30)) := by
  intro t ht m hm
  obtain ⟨r, hr, hr3, hT⟩ := profile30_htail t ht m hm
  exact ⟨r, hr, hr3, (tailFnAct_le_tailFn ht m r).trans hT⟩

/-- **O4 for `P52`** (`ThresholdNoValley P52`) from T1's explicit threshold on `m < 400` (the atlas) and the
large-mean theorem on `m ≥ 400` (Profile30's `D ≤ 8/5`, its `θ` targets and `htail52`). -/
theorem thresholdNoValley_P52_of
    (hsmall : ∀ t, InRange t → ∀ m, P52.mfloor t ≤ m → m < 400 →
      ExplicitThreshold (actQ t) m (P52.θb t) (P52.Db t) (P52.Tb t m) (P52.M1b t m)) :
    ThresholdNoValley P52 :=
  thresholdNoValley_of_split hsmall profile30_hD profile30_hθ htail52

end Erdos993Lean.Analytic.N52
