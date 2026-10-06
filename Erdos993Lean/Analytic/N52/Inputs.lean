import Erdos993Lean.Analytic.N52.Defs
import Erdos993Lean.Analytic.N52.Profile
import Erdos993Lean.Analytic.Reserve.Cert.Bands
import Erdos993Lean.Analytic.Reserve.UpperCert.Main
import Erdos993Lean.Analytic.O2.Final
import Erdos993Lean.Analytic.O2.Cert.Main
import Erdos993Lean.Analytic.TailCert.Main

/-!
# O1, O2, O3 for every forest, and at `n ≥ 52` for `P52`

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A19.  The three certified inputs of the route are stated in
`Defs.lean` for forests with `n ≥ 61` (`VarianceBound`, `VarianceRatioBound`, `TailBound`), but their proofs do not
use the size (lane R52, `LEAN/r52/REQUIREMENTS_52.md` §8 item 3; the headers of `Reserve/O1Profile30.lean` and
`O2/Main.lean` say so).  This file restates them for **every** finite forest, from the all-forest lemmas the n ≥ 61
wrappers use; the wrappers' proofs are copied with the size hypothesis removed (and nothing else changed):

* **`varianceBound_all`** (O1): `Var M ≤ D(λ) m` — the proof of `Reserve.varianceBound_profile30`
  (`Reserve/O1Profile30.lean`, lane A14) with the proved band theorems `Reserve.bandVar_band0_proved` …
  `bandVar_band3_proved` (lanes A11–A13, `Reserve/Cert/Bands.lean`) and `Reserve.bandVar_upper_of_box` with lane A15's
  `Reserve.UpperCert.upperBoxOK`;
* **`varianceRatioBound_all`** (O2): `V ≤ (1 + θ(λ))(1 − q) W` — the proof of `O2.varianceRatioBound_profile30_of_ok`
  (`O2/Main.lean`, lane A16) with the certificates `O2.Cert.localPaymentOK_all`, `O2.Cert.leafOK_all` (lane A18) and
  `O2.smallMessageOK_bands`;
* **`tailBound_act_all`** (O3, actual-activity form): `P(M ≤ r) ≤ tailFnAct(λ, m, r)` — the proof of
  `TailCert.tailBound_profile30_of_certificates` (`TailCert/Glue.lean`, lane A10) without its last step (the Laplace
  base is kept at the actual activity `λ` instead of being raised to the band's upper edge), with lane A10's
  `TailCert.bandCertificates` and lane A3's `Tail.tail_t3`;
* `varianceBound52`, `varianceRatioBound52`, `tailBound52`: the inputs at `n ≥ 52` for `P52`.

Trust: the `native_decide` checks inherited from the imports (O1: lane A12's 4 box checks and lane A15's 9 piece
checks; O2: lane A18's 168 root-box checks; O3: lane A10's 30 band checks); the proofs here use only `propext`,
`Classical.choice`, `Quot.sound`.

Scalarity check: no new scalar.  `D(λ)` (O1's cap on `Var M / E M`), `θ(λ)` (O2's cap on the second moment of `δ`)
and the rates `ℓ(λ, t_j)` (O3's Laplace transform of `M`) are Profile30's outputs of the named certificates; their
consumer is O4 (T1's no-valley lemma) through `P52`.
-/

namespace Erdos993Lean.Analytic.N52

open Profile30

/-! ## O1 for every forest -/

/-- **O1 for every forest** (`Var M ≤ D(λ) m`, `D = Profile30.P.Db`): every activity in `[1/3, 7/3]` and every
maximum-weight independent set.  The proof of `Reserve.varianceBound_profile30`, whose hypotheses `61 ≤ F.n` and
`AtInteriorRank` are unused, with the proved band theorems. -/
theorem varianceBound_all (F : FiniteForest) {t : ℝ} (ht : InRange t) {B : Finset (Fin F.n)}
    (hB : IsMaxWeight F t B) :
    (forestMixture F B t).varM ≤ Profile30.P.Db t * (forestMixture F B t).meanM := by
  obtain ⟨hi, hlo, hhi⟩ := Atlas.bandOf_spec ht
  have hlo' : ((edges.getD (bandOf t) 0 : ℚ) : ℝ) ≤ t := hlo
  have hhi' : t ≤ ((edges.getD (bandOf t + 1) 0 : ℚ) : ℝ) := hhi
  have hDb : Profile30.P.Db t = ((Dt.getD (bandOf t) (8 / 5) : ℚ) : ℝ) := rfl
  rw [hDb]
  have b0 := Reserve.profile30_bands0 (bandOf t) hi
  have b1 := Reserve.profile30_bands1 (bandOf t) hi
  have b2 := Reserve.profile30_bands2 (bandOf t) hi
  have b3 := Reserve.profile30_bands3 (bandOf t) hi
  have b4 := Reserve.profile30_bandsU (bandOf t) hi
  rcases (show bandOf t ≤ 5 ∨ (6 ≤ bandOf t ∧ bandOf t ≤ 9) ∨ (10 ≤ bandOf t ∧ bandOf t ≤ 21) ∨
      (22 ≤ bandOf t ∧ bandOf t ≤ 24) ∨ 25 ≤ bandOf t by omega) with h | h | h | h | h
  · obtain ⟨e1, e2, e3⟩ := b0 h
    rw [e3]
    exact Reserve.bandVar_band0_proved F t (le_trans (Rat.cast_le.mpr e1) hlo')
      (le_trans hhi' (Rat.cast_le.mpr e2)) B hB
  · obtain ⟨e1, e2, e3⟩ := b1 h.1 h.2
    rw [e3]
    exact Reserve.bandVar_band1_proved F t (le_trans (Rat.cast_le.mpr e1) hlo')
      (le_trans hhi' (Rat.cast_le.mpr e2)) B hB
  · obtain ⟨e1, e2, e3⟩ := b2 h.1 h.2
    rw [e3]
    exact Reserve.bandVar_band2_proved F t (le_trans (Rat.cast_le.mpr e1) hlo')
      (le_trans hhi' (Rat.cast_le.mpr e2)) B hB
  · obtain ⟨e1, e2, e3⟩ := b3 h.1 h.2
    rw [e3]
    exact Reserve.bandVar_band3_proved F t (le_trans (Rat.cast_le.mpr e1) hlo')
      (le_trans hhi' (Rat.cast_le.mpr e2)) B hB
  · obtain ⟨e1, e2, e3⟩ := b4 h
    rw [e3]
    have c1 : (((8 / 5 : ℚ)) : ℝ) = 8 / 5 := by norm_num
    have c2 : (((7 / 3 : ℚ)) : ℝ) = 7 / 3 := by norm_num
    have h1 : ((8 / 5 : ℚ) : ℝ) ≤ t := le_trans (Rat.cast_le.mpr e1) hlo'
    have h2 : t ≤ ((7 / 3 : ℚ) : ℝ) := le_trans hhi' (Rat.cast_le.mpr e2)
    rw [c1] at h1 ⊢
    rw [c2] at h2
    exact Reserve.bandVar_upper_of_box Reserve.UpperCert.upperBoxOK F t h1 h2 B hB

/-! ## O2 for every forest -/

/-- **O2 for every forest** (`V ≤ (1 + θ(λ))(1 − q) W`, `θ = Profile30.P.θb`): every activity in `[1/3, 7/3]` and
every maximum-weight independent set.  The proof of `O2.varianceRatioBound_profile30_of_ok`, whose hypotheses
`61 ≤ F.n` and `AtInteriorRank` are unused, with the certificates of the 14 O2 rows. -/
theorem varianceRatioBound_all (F : FiniteForest) {t : ℝ} (ht : InRange t) {B : Finset (Fin F.n)}
    (hB : IsMaxWeight F t B) :
    hardCoreVar F t ≤ (1 + Profile30.P.θb t) * (1 - actQ t) * weightW F t B := by
  have hok : ∀ b ∈ O2.bands, b.OK := fun b hb =>
    ⟨O2.guards_bands b hb, O2.Cert.localPaymentOK_all b hb, O2.Cert.leafOK_all b hb,
      O2.smallMessageOK_bands b hb⟩
  have mem : ∀ b, b ∈ [O2.low, O2.L1, O2.L23, O2.L4e, O2.central0, O2.central1, O2.central2,
      O2.central3, O2.upperShoulder, O2.H1, O2.H2b, O2.H3b, O2.H4b, O2.H8] → b ∈ O2.bands :=
    fun b hb => hb
  obtain ⟨hi, hlo, hhi⟩ := Atlas.bandOf_spec ht
  have hlo' : ((Profile30.edges.getD (Profile30.bandOf t) 0 : ℚ) : ℝ) ≤ t := hlo
  have hhi' : t ≤ ((Profile30.edges.getD (Profile30.bandOf t + 1) 0 : ℚ) : ℝ) := hhi
  have hθb : Profile30.P.θb t = ((Profile30.θt.getD (Profile30.bandOf t) 1 : ℚ) : ℝ) := rfl
  rw [hθb]
  rcases (show Profile30.bandOf t ≤ 5 ∨ (6 ≤ Profile30.bandOf t ∧ Profile30.bandOf t ≤ 9) ∨
      (10 ≤ Profile30.bandOf t ∧ Profile30.bandOf t ≤ 21) ∨
      (22 ≤ Profile30.bandOf t ∧ Profile30.bandOf t ≤ 24) ∨ 25 ≤ Profile30.bandOf t by omega)
    with h | h | h | h | h
  · obtain ⟨e1, e2, e3⟩ := O2.o2_bands0 _ hi h
    rw [e3]
    have h1 : ((1 / 3 : ℚ) : ℝ) ≤ t := le_trans (Rat.cast_le.mpr e1) hlo'
    have h2 : t ≤ ((3 / 5 : ℚ) : ℝ) := le_trans hhi' (Rat.cast_le.mpr e2)
    exact O2.vrb_of_band (hok O2.low (mem _ (by simp))) ⟨h1, h2⟩ (by norm_num [O2.low]) hB
  · obtain ⟨e1, e2, e3⟩ := O2.o2_bands1 _ hi h.1 h.2
    rw [e3]
    have h1 : ((3 / 5 : ℚ) : ℝ) ≤ t := le_trans (Rat.cast_le.mpr e1) hlo'
    have h2 : t ≤ ((4 / 5 : ℚ) : ℝ) := le_trans hhi' (Rat.cast_le.mpr e2)
    by_cases c1 : t ≤ ((13 / 20 : ℚ) : ℝ)
    · exact O2.vrb_of_band (hok O2.L1 (mem _ (by simp))) ⟨h1, c1⟩ (by norm_num [O2.L1]) hB
    by_cases c2 : t ≤ ((3 / 4 : ℚ) : ℝ)
    · exact O2.vrb_of_band (hok O2.L23 (mem _ (by simp))) ⟨(not_le.mp c1).le, c2⟩
        (by norm_num [O2.L23]) hB
    · exact O2.vrb_of_band (hok O2.L4e (mem _ (by simp))) ⟨(not_le.mp c2).le, h2⟩
        (by norm_num [O2.L4e]) hB
  · obtain ⟨e1, e2, e3⟩ := O2.o2_bands2 _ hi h.1 h.2
    rw [e3]
    have h1 : ((4 / 5 : ℚ) : ℝ) ≤ t := le_trans (Rat.cast_le.mpr e1) hlo'
    have h2 : t ≤ ((13 / 10 : ℚ) : ℝ) := le_trans hhi' (Rat.cast_le.mpr e2)
    by_cases c1 : t ≤ ((9 / 10 : ℚ) : ℝ)
    · exact O2.vrb_of_band (hok O2.central0 (mem _ (by simp))) ⟨h1, c1⟩
        (by norm_num [O2.central0]) hB
    by_cases c2 : t ≤ ((1 : ℚ) : ℝ)
    · exact O2.vrb_of_band (hok O2.central1 (mem _ (by simp))) ⟨(not_le.mp c1).le, c2⟩
        (by norm_num [O2.central1]) hB
    by_cases c3 : t ≤ ((23 / 20 : ℚ) : ℝ)
    · exact O2.vrb_of_band (hok O2.central2 (mem _ (by simp))) ⟨(not_le.mp c2).le, c3⟩
        (by norm_num [O2.central2]) hB
    · exact O2.vrb_of_band (hok O2.central3 (mem _ (by simp))) ⟨(not_le.mp c3).le, h2⟩
        (by norm_num [O2.central3]) hB
  · obtain ⟨e1, e2, e3⟩ := O2.o2_bands3 _ hi h.1 h.2
    rw [e3]
    have h1 : ((13 / 10 : ℚ) : ℝ) ≤ t := le_trans (Rat.cast_le.mpr e1) hlo'
    have h2 : t ≤ ((8 / 5 : ℚ) : ℝ) := le_trans hhi' (Rat.cast_le.mpr e2)
    exact O2.vrb_of_band (hok O2.upperShoulder (mem _ (by simp))) ⟨h1, h2⟩
      (by norm_num [O2.upperShoulder]) hB
  · obtain ⟨e1, e2, e3⟩ := O2.o2_bands4 _ hi h
    rw [e3]
    have h1 : ((8 / 5 : ℚ) : ℝ) ≤ t := le_trans (Rat.cast_le.mpr e1) hlo'
    have h2 : t ≤ ((7 / 3 : ℚ) : ℝ) := le_trans hhi' (Rat.cast_le.mpr e2)
    by_cases c1 : t ≤ ((17 / 10 : ℚ) : ℝ)
    · exact O2.vrb_of_band (hok O2.H1 (mem _ (by simp))) ⟨h1, c1⟩ (by norm_num [O2.H1]) hB
    by_cases c2 : t ≤ ((19 / 10 : ℚ) : ℝ)
    · exact O2.vrb_of_band (hok O2.H2b (mem _ (by simp))) ⟨(not_le.mp c1).le, c2⟩
        (by norm_num [O2.H2b]) hB
    by_cases c3 : t ≤ ((21 / 10 : ℚ) : ℝ)
    · exact O2.vrb_of_band (hok O2.H3b (mem _ (by simp))) ⟨(not_le.mp c2).le, c3⟩
        (by norm_num [O2.H3b]) hB
    by_cases c4 : t ≤ ((9 / 4 : ℚ) : ℝ)
    · exact O2.vrb_of_band (hok O2.H4b (mem _ (by simp))) ⟨(not_le.mp c3).le, c4⟩
        (by norm_num [O2.H4b]) hB
    · exact O2.vrb_of_band (hok O2.H8 (mem _ (by simp))) ⟨(not_le.mp c4).le, h2⟩
        (by norm_num [O2.H8]) hB

/-! ## O3 for every forest, with the actual activity in the Laplace base -/

/-- **O3 for every forest, actual-activity form**: `P(M ≤ r) ≤ min(1, min_j e^{−ℓ_j m} ((1 + λ)/(1 + λ t_j))^r)`
(`Atlas.tailFnAct`) at every activity in `[1/3, 7/3]` and every maximum-weight independent set.  The proof of
`TailCert.tailBound_profile30_of_certificates` (lane A10's glue) with lane A10's band certificates, stopping before
the base is raised to the band edge. -/
theorem tailBound_act_all (F : FiniteForest) {t : ℝ} (ht : InRange t) {B : Finset (Fin F.n)}
    (hB : IsMaxWeight F t B) (M' : ℕ) :
    (forestMixture F B t).cdfM M' ≤ Atlas.tailFnAct t (forestMixture F B t).meanM M' := by
  obtain ⟨hi30, hlo, hhi⟩ := TailCert.bandOf_spec ht
  have ht0 : 0 < t := by have := ht.1; linarith
  have hleaf := TailCert.leafCondition_of_isMaxWeight ht0 hB
  have hBi := hB.1
  have hterm : ∀ j < 5, (forestMixture F B t).cdfM M' ≤
      Atlas.tailTermAct t (forestMixture F B t).meanM M' j := by
    intro j hj
    obtain ⟨ha, hz0, hz1, hiso⟩ := TailCert.band_facts hi30 hj
    have h := Tail.tail_t3 F B hBi hleaf ht0 (by have := ht.2; linarith) hz0 hz1 ha
      (hiso t hlo) (TailCert.bandCertificates (bandOf t) hi30 j hj t hlo hhi) M'
    refine h.trans (le_of_eq ?_)
    unfold Atlas.tailTermAct
    rw [neg_mul]
    rfl
  have h1 := TailCert.cdfM_le_one F hBi ht0 M'
  unfold Atlas.tailFnAct
  exact le_min h1 (le_min (hterm 0 (by norm_num)) (le_min (hterm 1 (by norm_num))
    (le_min (hterm 2 (by norm_num)) (le_min (hterm 3 (by norm_num)) (hterm 4 (by norm_num))))))

/-! ## The inputs at `n ≥ 52` for `P52` -/

/-- **O1 at `n ≥ 52`** for `P52`. -/
theorem varianceBound52 : VarianceBoundN 52 P52 :=
  fun F _ _ ht _ _ hB => varianceBound_all F ht hB

/-- **O2 at `n ≥ 52`** for `P52`. -/
theorem varianceRatioBound52 : VarianceRatioBoundN 52 P52 :=
  fun F _ _ ht _ _ hB => varianceRatioBound_all F ht hB

/-- **O3 at `n ≥ 52`** for `P52` (the actual-activity tail). -/
theorem tailBound52 : TailBoundN 52 P52 :=
  fun F _ _ ht _ _ hB M' _ => tailBound_act_all F ht hB M'

end Erdos993Lean.Analytic.N52
