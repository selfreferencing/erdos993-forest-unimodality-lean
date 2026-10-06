import Erdos993Lean.Analytic.Window
import Erdos993Lean.Analytic.HardCore.Weight

/-!
# The mean floor at order 25 from the interior window alone (lane B, L2)

Source: `LEAN/certfree/act1_test/REPORT.md`, "What would change in the paper", the order-25
replacement of Theorem `p2:thm:O5`; independently confirmed in
`LEAN/certfree/referee_act1_test/REFEREE.md`, claim (iii).

At an interior rank the retained forest `F` has mean `k` with `(F.n + 3) / 4 < k`.
For `F.n >= 25` this implies `8 <= k`.  The maximum-weight independent set `B` and the
forest mixture remain the same objects: the existing bipartite weight theorem gives
`k <= 2 q(t) E M`.  No density record, activity-transfer certificate or numerical
compiled evaluation is used.

Named consumer: `MGF.N25.densityBound25`, and the future order-25 instance of
`MGF.noWeakValley_of_strips` / `MGF.N25.noWeakValley_of_strips_caps` in lane L5.
This installs only the stated analytic input; it assigns no campaign promotion verdict.
-/

namespace Erdos993Lean.Analytic.Density

/-- The order-25 window rank is at least eight (Theorem `p2:thm:O5` as restated in
`certfree/act1_test`, confirmed by `referee_act1_test`, claim (iii)); pure integer arithmetic. -/
theorem rank_ge_eight_of_ge25 {n k : ℕ} (hn : 25 <= n) (hk : (n + 3) / 4 < k) :
    8 <= k := by
  omega

/-- The mean bound of the order-25 version of Theorem `p2:thm:O5` from
`certfree/act1_test`: at an interior rank of the retained forest and for the retained
maximum-weight independent set, `E M >= 8/(2q(t))`.  No density certificates. -/
theorem meanM_ge_window25 (F : FiniteForest) (hn : 25 <= F.n) {t : ℝ} (ht : 0 < t)
    (hI : AtInteriorRank F t) {B : Finset (Fin F.n)} (hB : IsMaxWeight F t B) :
    8 / (2 * actQ t) <= (forestMixture F B t).meanM := by
  obtain ⟨k, hk, -, hmu⟩ := hI
  have hk8 : (8 : ℝ) <= (k : ℝ) := by
    exact_mod_cast rank_ge_eight_of_ge25 hn hk
  have h2 := two_mul_actQ_mul_meanM_ge F ht hB
  rw [hmu] at h2
  have hq : 0 < actQ t := HardCore.actQ_pos ht
  rw [div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hq)]
  nlinarith

end Erdos993Lean.Analytic.Density
