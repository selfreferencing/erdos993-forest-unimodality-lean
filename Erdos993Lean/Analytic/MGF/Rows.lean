import Erdos993Lean.Analytic.MGF.Criterion
import Erdos993Lean.Analytic.MGF.Pieces
import Erdos993Lean.Analytic.N44.Tail
import Erdos993Lean.Analytic.N44.Strip

/-!
# The forest input in MGF form: the O3 rows of the n ≥ 44 pieces before the Markov step (lane A22, milestone L2)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A22.  Sources: `LEAN/atlas_mgf/SPEC.md` §2 (the tail rows
`E[(1 − q + q t_k)^M] ≤ e^{−ℓ_k m}` for each certified band and tilt, taken from the O3 route BEFORE the Markov step),
lane A3's `Tail/Weight.lean` (`t3_reduction_mixture`: Theorem T3-2 in mixture form, whose only hypothesis is the reduced
unit inequality `T3UNonneg`), lane A10's `TailCert/Glue.lean` (`bandCertificates`, `band_facts`,
`leafCondition_of_isMaxWeight`) and lane A21's `N44/Tail.lean` (`newRows`, `newRows_facts`, `row_table`: the ladder rows
at `t = 0`) and `N44/Strip.lean` (`rates44_old`, `rates44_new`: the piece rates are the parent band's, with the ladder rate
at `t = 0` on the rows).

The N44 route (`N44/Tail.lean` `tailNew`, `N52/Inputs.lean` `tailBound_act_all`) takes the same certificates through
`Tail.tail_t3 = cdfM_le_laplace ∘ t3_reduction_mixture` (`Tail/Markov.lean`), i.e. as CDF bounds.  This file stops at
`t3_reduction_mixture`: the Laplace bound itself is the row.

* `tiltsQ44 p` (`MGF/Pieces.lean`): the five certified tilts `(t_k, ℓ_k)` of piece `p` (`Atlas.tvals`,
  `N44.Data.rates44`, verbatim from lane R4X's `config_N44_final.json` as lane A21 transcribed it); `tilts44 p` their
  real form; `tilts44R t` the tilts of the piece of the activity `t`.
* **`row44`**: for every forest, every activity in range, every maximum-weight `B` and every `k < 5`:
  `E[(1 − q + q t_k)^M] ≤ e^{−ℓ_k m}` with the piece's `k`-th rate.
* **`tailMGF44_all`**, **`tailBoundMGF44 : TailBoundMGF N tilts44R`** for every `N` (the size is not used).

Trust: lane A10's 30 band checks and the 26 ladder row checks (`native_decide`, inherited through the imports);
the proofs here use only `propext`, `Classical.choice`, `Quot.sound`.

Scalarity check: each `ℓ_k` summarizes the Laplace transform of the free count `M` at `s_k = 1 − q + q t_k` (the object
`E[s_k^M]`, produced by the certificate `T3UNonneg λ t_k a ℓ_k` of the band or ladder row through
`t3_reduction_mixture`); its consumer is `NoValleyAtMGF2` through `mgfRows` (the rows `(s_k, e^{−ℓ_k m})`).
-/

namespace Erdos993Lean.Analytic.MGF

open Profile30 Erdos993Lean.Analytic.N44

/-- The five certified tilts of piece `p` as reals (`tiltsQ44` of `MGF/Pieces.lean`). -/
noncomputable def tilts44 (p : ℕ) : List (ℝ × ℝ) := castTilts (tiltsQ44 p)

/-- **The tilt profile at `n ≥ 44`**: the tilts of the piece of the activity. -/
noncomputable def tilts44R (t : ℝ) : List (ℝ × ℝ) := tilts44 (pieceOf t)

/-- **One row of the n ≥ 44 profile in MGF form**: for every forest, every activity `t` in range, every maximum-weight
independent set `B` and every `k < 5`, `E[(1 − q + q t_k)^M] ≤ e^{−ℓ_k m}` with the `k`-th rate of the piece of `t`
(`q = t/(1 + t)`, `m = E M`).  The certificate is the parent band's (`TailCert.bandCertificates`) or, at `t = 0` on a
piece with a ladder row, the row's (`N44.newRows`); the Laplace bound is lane A3's `t3_reduction_mixture`. -/
theorem row44 (F : FiniteForest) {t : ℝ} (ht : InRange t) {B : Finset (Fin F.n)} (hB : IsMaxWeight F t B)
    {k : ℕ} (hk : k < 5) :
    (forestMixture F B t).expect (fun M _ => (1 - actQ t + actQ t * ((Atlas.tvals.getD k 0 : ℚ) : ℝ)) ^ M) ≤
      Real.exp (-((((N44.Data.rates44.getD (pieceOf t) []).getD k 0 : ℚ) : ℝ) * (forestMixture F B t).meanM)) := by
  obtain ⟨hp, hpar, hlo, hhi⟩ := pieceOf_spec ht
  unfold loR at hlo
  unfold hiR at hhi
  have ht0 : 0 < t := by have := ht.1; linarith
  have ht6 : t ≤ 6 := by have := ht.2; linarith
  have hleaf := TailCert.leafCondition_of_isMaxWeight ht0 hB
  have hbi : bandOf t < 30 := (Atlas.bandOf_spec ht).1
  by_cases hnew : k = 0 ∧ N44.Data.newEll.getD (pieceOf t) 0 ≠ 0
  · -- the ladder row at `t = 0`
    obtain ⟨rfl, hne⟩ := hnew
    rw [rates44_new _ hp hne]
    have hc := newRows (pieceOf t) hp hne
    obtain ⟨-, hrlo, hrhi, -, -⟩ := row_table (pieceOf t) hp hne
    obtain ⟨hl0, hl1, ha, hexp⟩ := newRows_facts (pieceOf t) hp hne
    have hlo' : ((Ladder.O3.rowLo.getD (N44.Data.rowOf.getD (pieceOf t) 0) 0 : ℚ) : ℝ) ≤ t :=
      le_trans (by exact_mod_cast hrlo) hlo
    have hhi' : t ≤ ((Ladder.O3.rowHi.getD (N44.Data.rowOf.getD (pieceOf t) 0) 0 : ℚ) : ℝ) :=
      le_trans hhi (by exact_mod_cast hrhi)
    have hU := TailCert.checkBand_sound hc t hlo' hhi'
    have hz : ((0 : ℚ) : ℝ) = 0 := Rat.cast_zero
    have hiso : ((N44.Data.newEll.getD (pieceOf t) 0 : ℚ) : ℝ) ≤
        Real.log ((1 + t) / (1 + t * ((0 : ℚ) : ℝ))) := by
      rw [hz, mul_zero, add_zero, div_one, Real.le_log_iff_exp_le (by linarith)]
      have h1 := TailCert.exp_le_expUp5 hl0 hl1
      have h2 : ((TailCert.expUp5 (N44.Data.newEll.getD (pieceOf t) 0) : ℚ) : ℝ) ≤
          1 + ((N44.Data.pieceLo.getD (pieceOf t) 0 : ℚ) : ℝ) := by
        exact_mod_cast hexp
      linarith
    have h := Tail.t3_reduction_mixture F B hB.1 hleaf ht0 ht6 (by norm_num) (by norm_num)
      (by exact_mod_cast ha) hiso hU
    have e0 : ((Atlas.tvals.getD 0 0 : ℚ) : ℝ) = ((0 : ℚ) : ℝ) := by norm_num [Atlas.tvals]
    rw [e0, ← neg_mul]
    exact h
  · -- the parent band's certificate
    have hold : k ≠ 0 ∨ N44.Data.newEll.getD (pieceOf t) 0 = 0 := by
      by_contra hc
      push_neg at hc
      exact hnew hc
    rw [rates44_old _ hp k hk hold, hpar, (Atlas.bandAt_eq _ hbi).2.2.1]
    obtain ⟨ha, hz0, hz1, hiso⟩ := TailCert.band_facts hbi hk
    obtain ⟨-, hlo2, hhi2⟩ := TailCert.bandOf_spec ht
    have h := Tail.t3_reduction_mixture F B hB.1 hleaf ht0 ht6 hz0 hz1 ha (hiso t hlo2)
      (TailCert.bandCertificates (bandOf t) hbi k hk t hlo2 hhi2)
    have htv : ((Atlas.tvals.getD k 0 : ℚ) : ℝ) = TailCert.tR k := by
      unfold TailCert.tR
      rw [Atlas.tvals_eq]
    rw [htv, ← neg_mul]
    exact h

/-- **O3 in MGF form for every forest at the n ≥ 44 pieces' rows**: every row of `mgfRows (tilts44R t) q m` holds
for the forest mixture at every activity in range and every maximum-weight independent set. -/
theorem tailMGF44_all (F : FiniteForest) {t : ℝ} (ht : InRange t) {B : Finset (Fin F.n)}
    (hB : IsMaxWeight F t B) :
    ∀ r ∈ mgfRows (tilts44R t) (actQ t) (forestMixture F B t).meanM,
      (forestMixture F B t).expect (fun M _ => r.1 ^ M) ≤ r.2 := by
  intro r hr
  unfold tilts44R tilts44 at hr
  rw [mem_mgfRows_castTilts] at hr
  obtain ⟨x, hx, rfl⟩ := hr
  unfold tiltsQ44 at hx
  rw [List.mem_map] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  rw [List.mem_range] at hk
  exact row44 F ht hB hk

/-- **O3 in MGF form at every size threshold `N`** for the tilt profile `tilts44R` (`TailBoundMGF N tilts44R`). -/
theorem tailBoundMGF44 (N : ℕ) : TailBoundMGF N tilts44R :=
  fun F _ _ ht _ _ hB => tailMGF44_all F ht hB

end Erdos993Lean.Analytic.MGF
