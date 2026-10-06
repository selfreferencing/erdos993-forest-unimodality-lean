import Erdos993Lean.Analytic.Density.Window25
import Erdos993Lean.Analytic.MGF.N25.Data
import Erdos993Lean.Analytic.N44.Pieces

/-!
# O5 at order 25 on every subinterval, from the window alone (lane B, L2)

Source: `LEAN/certfree/act1_test/REPORT.md`, "What would change in the paper",
Theorem `p2:thm:O5` restated for `n >= 25`; referee confirmation in
`LEAN/certfree/referee_act1_test/REFEREE.md`, claim (iii).

For every forest with at least 25 vertices, every activity in `[1/3,7/3]` at an interior
rank and every maximum-weight independent set `B`, its forest mixture satisfies
`E M >= 8/(2q(pieceHi_p))` on the subinterval containing the activity.

`Density.meanM_ge_window25` gives the floor `8/(2q(t))` directly from the window.
Monotonicity of `q` transports it to the upper edge of the same retained subinterval.
All rank floors are eight.  This proof imports no density record or transfer certificates.

The explicit floor expression in `densityBound25` is definitionally
`MGF.mfloorR Data.mmin25 t`; the heavy assembly module is deliberately unnecessary for
this theorem.  Named consumer: the order-25 instance of `MGF.noWeakValley_of_strips` /
`MGF.N25.noWeakValley_of_strips_caps` in lane L5.  No new `native_decide` occurs.
-/

namespace Erdos993Lean.Analytic.MGF.N25

open Erdos993Lean.Analytic.N44

/-- The real form of the floor in Theorem `p2:thm:O5` restated for order 25
(`certfree/act1_test`), on the subinterval containing the activity. -/
theorem mfloor25_eq {t : ℝ} (hR : InRange t) :
    ((Data.mmin25.getD (pieceOf t) 0 : ℚ) : ℝ) =
      8 / (2 * actQ (hiR (pieceOf t))) := by
  have hp := (pieceOf_spec hR).1
  have h := Data.mmin25_eq (pieceOf t) hp
  rw [h, Data.kmin25_eight (pieceOf t) hp]
  unfold actQ hiR
  push_cast
  ring

/-- **Theorem `p2:thm:O5` at order 25** (`certfree/act1_test`, refereed in
`referee_act1_test`, claim (iii)): the expected free count of every maximum-weight
forest mixture lies above the rank-eight floor of its subinterval, for every forest
with at least 25 vertices.  The window alone proves this; no density certificates. -/
theorem densityBound25 : ∀ F : FiniteForest, 25 <= F.n → ∀ t : ℝ,
    InRange t → AtInteriorRank F t → ∀ B, IsMaxWeight F t B →
      ((Data.mmin25.getD (pieceOf t) 0 : ℚ) : ℝ) <= (forestMixture F B t).meanM := by
  intro F hn t hR hI B hB
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) hR.1
  obtain ⟨-, -, -, hhi⟩ := pieceOf_spec hR
  have hq : 0 < actQ t := HardCore.actQ_pos ht
  have hqle : actQ t <= actQ (hiR (pieceOf t)) := Atlas.actQ_le_actQ ht.le hhi
  rw [mfloor25_eq hR]
  refine le_trans ?_ (Density.meanM_ge_window25 F hn ht hI hB)
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)

end Erdos993Lean.Analytic.MGF.N25
