import Erdos993Lean.Analytic.MGF.Rows
import Erdos993Lean.Analytic.MGF.N25.Density
import Erdos993Lean.Analytic.HandVariance.Main
import Erdos993Lean.Analytic.N44.Analytic

/-!
# Paper v2.1: the two Laplace-rate families retained by Theorem 5.8

Sources: TWIN_v2.1/s4_part_d.tex, Theorem 4.40 (`p2:thm:O3`),
and s5_part_b.tex, Theorem 5.8 (`p2:thm:O4`).
The subinterval rates are `MGF.tilts44R`. The band rates below deliberately
retain the parent band's rates even on subintervals with a stronger zero-tilt
row. This supplies both families required by the paper. No CDF criterion or
variance-cover theorem is used by these declarations.
-/

namespace Erdos993Lean.Analytic.V21

open Profile30 N44

/-- Source: Theorem 4.40, the five Laplace rates of the actual activity band. -/
noncomputable def bandTilts (t : ℝ) : List (ℝ × ℝ) :=
  castTilts ((List.range 5).map fun k =>
    (Atlas.tvals.getD k 0, (Profile30.rates.getD (bandOf t) []).getD k 0))

/-- Source: Theorem 4.40; the band certificate is used directly, including on
subintervals having stronger zero-tilt rows. -/
theorem band_row (F : FiniteForest) {t : ℝ} (ht : InRange t)
    {B : Finset (Fin F.n)} (hB : IsMaxWeight F t B) {k : ℕ} (hk : k < 5) :
    (forestMixture F B t).expect
      (fun M _ => (1 - actQ t + actQ t * ((Atlas.tvals.getD k 0 : ℚ) : ℝ)) ^ M) ≤
    Real.exp (-((((Profile30.rates.getD (bandOf t) []).getD k 0 : ℚ) : ℝ) *
      (forestMixture F B t).meanM)) := by
  have ht0 : 0 < t := by have := ht.1; linarith
  have ht6 : t ≤ 6 := by have := ht.2; linarith
  have hleaf := TailCert.leafCondition_of_isMaxWeight ht0 hB
  have hbi : bandOf t < 30 := (Atlas.bandOf_spec ht).1
  obtain ⟨ha, hz0, hz1, hiso⟩ := TailCert.band_facts hbi hk
  obtain ⟨-, hlo, hhi⟩ := TailCert.bandOf_spec ht
  have h := Tail.t3_reduction_mixture F B hB.1 hleaf ht0 ht6 hz0 hz1 ha (hiso t hlo)
    (TailCert.bandCertificates (bandOf t) hbi k hk t hlo hhi)
  have htv : ((Atlas.tvals.getD k 0 : ℚ) : ℝ) = TailCert.tR k := by
    unfold TailCert.tR
    rw [Atlas.tvals_eq]
  rw [htv, ← neg_mul]
  exact h

/-- Source: Theorem 4.40, all five band Laplace rows in the MGF consumer's form. -/
theorem bandMGF_all (F : FiniteForest) {t : ℝ} (ht : InRange t)
    {B : Finset (Fin F.n)} (hB : IsMaxWeight F t B) :
    ∀ r ∈ mgfRows (bandTilts t) (actQ t) (forestMixture F B t).meanM,
      (forestMixture F B t).expect (fun M _ => r.1 ^ M) ≤ r.2 := by
  intro r hr
  unfold bandTilts at hr
  rw [mem_mgfRows_castTilts] at hr
  obtain ⟨x, hx, rfl⟩ := hr
  rw [List.mem_map] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  rw [List.mem_range] at hk
  exact band_row F ht hB hk

end Erdos993Lean.Analytic.V21
