import Erdos993Lean.Analytic.N44.Profile
import Erdos993Lean.Analytic.N44.Records
import Erdos993Lean.Analytic.N48.Records
import Erdos993Lean.Analytic.N52.Defs
import Erdos993Lean.Analytic.Density.Main

/-!
# O5 at `n ≥ 44`: the floor of the expected free count for `P44`, on the 55 pieces

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A21.  Sources: lane R4X's `LEAN/r4x/REACH_BELOW_52.md` §5 (the O5
band rule at `N = 44` on the sub-band edges), this lane's `N45/Density.lean` (whose proofs are copied with `44` for `45`,
`55` pieces for `46`, the rank `12` on pieces 0–18 and `recOf44` for `recOf45`), lane A8's density machinery.

**Theorem** (`densityBound44 : DensityBoundN 44 P44`): for every forest with `n ≥ 44`, every `t ∈ [1/3, 7/3]` at an
interior rank `μ_F(t) = k` and every maximum-weight independent set `B`, `m ≥ mmin44_p = k_p/(2 q(pieceHi_p))` on the
piece `p` of `t`.

* Pieces 0–18 (bands 1–14 up to `93/100`): `k_p = 12 ≤ k` because `k > ⌈44/4⌉ = 11`.
* Pieces 19–54 (`rank_high44`): the record `recOf44 p` — `x = 23/25` (lane A20's `N48.rec2325`) on the pieces of
  bands 14–15 from `93/100`, `x = 8/5` (`N44/Records.lean`, the only new record of the step) on `[33/20, 17/10]`,
  `x = 7/5` on `[17/10, 7/4]`, `x = 57/50` on `[7/4, 9/5]`, `x = 11/10` on `[49/40, 13/10]` and `[9/5, 37/20]`,
  `x = 1` on the others — and the activity transfer from the rational check `(k_p − 1)² < (q(pieceLo_p)/q(x)) (44 r + h)²`
  (`band_checks44`, kernel `decide`).  Tightest: `[33/20, 17/10]` with `x = 8/5`, `√(q_a/q_x) L = 14.038 > 14`.

Scalarity check: as `N45/Density.lean`, with the records `x ∈ {1, 11/10, 57/50, 7/5, 23/25, 8/5}`.
-/

namespace Erdos993Lean.Analytic.N44

open Profile30 Density N52

/-- The record used on piece `p` at `n ≥ 44`. -/
def recOf44 (p : ℕ) : Record :=
  if p = 45 then rec85
  else if p = 46 then N51.rec75
  else if p = 47 then N51.rec5750
  else if 19 ≤ p ∧ p ≤ 23 then N48.rec2325
  else if p = 36 ∨ p = 37 ∨ p = 48 then rec11
  else rec1

theorem recOf44_valid (p : ℕ) : (recOf44 p).Valid := by
  unfold recOf44
  split_ifs
  · exact rec85_valid
  · exact N51.rec75_valid
  · exact N51.rec5750_valid
  · exact N48.rec2325_valid
  · exact rec11_valid
  · exact rec1_valid

/-- On pieces 0–18 the rank at `n ≥ 44` is `12`. -/
theorem kmin44_low : ∀ p < 19, Data.kmin44.getD p 0 = 12 := by decide +kernel

/-- `mmin44_p = k_p / (2 q(pieceHi_p))` on every piece (kernel `decide`). -/
theorem mmin44_eq : ∀ p < 55, Data.mmin44.getD p 0 =
    (Data.kmin44.getD p 0 : ℚ) / (2 * (Data.pieceHi.getD p 0 / (1 + Data.pieceHi.getD p 0))) := by
  decide +kernel

/-- **The piece checks at `N = 44`** (kernel `decide`): on pieces 19–54, `k_p ≥ 1`, the record's activity lies below
the lower edge `pieceLo_p`, and `(k_p − 1)² < (q(pieceLo_p)/q(x)) (44 r + h)²`. -/
theorem band_checks44 : ∀ p < 55, 19 ≤ p →
    1 ≤ Data.kmin44.getD p 0 ∧ (recOf44 p).x ≤ Data.pieceLo.getD p 0 ∧
    ((Data.kmin44.getD p 0 : ℚ) - 1) ^ 2 <
      (Data.pieceLo.getD p 0 / (1 + Data.pieceLo.getD p 0)) / ((recOf44 p).x / (1 + (recOf44 p).x)) *
        (44 * (recOf44 p).r + (recOf44 p).h) ^ 2 := by
  decide +kernel

/-- **The rank bound on pieces 19–54 at `n ≥ 44`** from the density records and the activity transfer. -/
theorem rank_high44 {F : FiniteForest} (hn : 44 ≤ F.n) {t : ℝ} (hR : InRange t)
    (hp : 19 ≤ pieceOf t) {k : ℕ} (hμ : hardCoreMean F t = k) : Data.kmin44.getD (pieceOf t) 0 ≤ k := by
  obtain ⟨hp55, -, hlo, -⟩ := pieceOf_spec hR
  obtain ⟨hK1, hxe, hchk⟩ := band_checks44 (pieceOf t) hp55 hp
  have hRv : (recOf44 (pieceOf t)).Valid := recOf44_valid (pieceOf t)
  have hx : (0 : ℝ) < (recOf44 (pieceOf t)).x := by exact_mod_cast hRv.x_pos
  have hxa : ((recOf44 (pieceOf t)).x : ℝ) ≤ loR (pieceOf t) := by
    unfold loR
    exact_mod_cast hxe
  have hμx := hRv.hardCoreMean_ge F (by omega)
  have hr : (0 : ℝ) ≤ (recOf44 (pieceOf t)).r := by exact_mod_cast hRv.r_nonneg
  have hh : (0 : ℝ) ≤ (recOf44 (pieceOf t)).h := by
    exact_mod_cast hRv.s0_nonneg.trans (hRv.s0_le_g.trans hRv.g_le_h)
  have hn' : (44 : ℝ) ≤ F.n := by exact_mod_cast hn
  have hL : (((44 * (recOf44 (pieceOf t)).r + (recOf44 (pieceOf t)).h : ℚ)) : ℝ) ≤
      hardCoreMean F (recOf44 (pieceOf t)).x := by
    push_cast
    nlinarith
  have hL0 : (0 : ℝ) ≤ (((44 * (recOf44 (pieceOf t)).r + (recOf44 (pieceOf t)).h : ℚ)) : ℝ) := by
    push_cast
    positivity
  apply le_of_transfer F hx hxa hlo hL0 hL hμ hK1
  have hq : actQ (loR (pieceOf t)) / actQ ((recOf44 (pieceOf t)).x : ℝ) =
      (((Data.pieceLo.getD (pieceOf t) 0 / (1 + Data.pieceLo.getD (pieceOf t) 0)) /
        ((recOf44 (pieceOf t)).x / (1 + (recOf44 (pieceOf t)).x)) : ℚ) : ℝ) := by
    unfold actQ loR
    push_cast
    ring
  rw [hq]
  exact_mod_cast hchk

/-- On pieces 0–18 the rank bound at `n ≥ 44` is the interior-rank condition: `k > ⌈44/4⌉ = 11`. -/
theorem kmin44_le_of_low {F : FiniteForest} (hn : 44 ≤ F.n) {t : ℝ} (hp : pieceOf t < 19) {k : ℕ}
    (hk : (F.n + 3) / 4 < k) : Data.kmin44.getD (pieceOf t) 0 ≤ k := by
  rw [kmin44_low _ hp]
  omega

/-- The floor of the piece of `t` as a real number: `k_p / (2 q(pieceHi_p))`. -/
theorem mfloor44_eq {t : ℝ} (hR : InRange t) :
    P44.mfloor t = (Data.kmin44.getD (pieceOf t) 0 : ℝ) / (2 * actQ (hiR (pieceOf t))) := by
  have hp := (pieceOf_spec hR).1
  have h := mmin44_eq (pieceOf t) hp
  rw [P44_mfloor, h]
  unfold actQ hiR
  push_cast
  ring

/-- **The O5 floor at `n ≥ 44` from an integer rank**. -/
theorem densityBound44_of_rank
    (hrank : ∀ F : FiniteForest, 44 ≤ F.n → ∀ t : ℝ, InRange t → ∀ k : ℕ, (F.n + 3) / 4 < k →
      hardCoreMean F t = k → Data.kmin44.getD (pieceOf t) 0 ≤ k) :
    DensityBoundN 44 P44 := by
  intro F hn t hR hI B hB
  obtain ⟨k, hk1, -, hμ⟩ := hI
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) hR.1
  obtain ⟨-, -, -, hhi⟩ := pieceOf_spec hR
  have hkr : (Data.kmin44.getD (pieceOf t) 0 : ℝ) ≤ k := by exact_mod_cast hrank F hn t hR k hk1 hμ
  have h2 := two_mul_actQ_mul_meanM_ge F ht hB
  rw [hμ] at h2
  have hq : 0 < actQ t := HardCore.actQ_pos ht
  have hqle : actQ t ≤ actQ (hiR (pieceOf t)) := Density.actQ_le_actQ ht.le hhi
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  set m := (forestMixture F B t).meanM with hm
  have hm0 : 0 ≤ m := by
    by_contra hneg
    push_neg at hneg
    nlinarith
  rw [mfloor44_eq hR, div_le_iff₀ (by linarith)]
  nlinarith

/-- **O5 at `n ≥ 44` for `P44` (all 55 pieces).** -/
theorem densityBound44 : DensityBoundN 44 P44 := by
  apply densityBound44_of_rank
  intro F hn t hR k hk hμ
  rcases Nat.lt_or_ge (pieceOf t) 19 with hp | hp
  · exact kmin44_le_of_low hn hp hk
  · exact rank_high44 hn hR hp hμ

end Erdos993Lean.Analytic.N44
