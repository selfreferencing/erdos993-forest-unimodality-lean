import Erdos993Lean.Analytic.N44.Data.Params

/-!
# The order-25 window-only O5 rank and floor tables (lane B, L2)

Source: `LEAN/certfree/act1_test/REPORT.md`, the order-25 version of Theorem `p2:thm:O5`:
`k_p = 8` on every subinterval.  Confirmed by `referee_act1_test/REFEREE.md`, claim (iii).
The activity edges are the unchanged 55-piece table `N44.Data.pieceHi`.  Each floor is
`8 / (2 q(pieceHi_p))`, with `q(t) = t/(1+t)`; no density records are used.

The explicit rational entries were checked against
`lane_b/CHECKS/window25_expected_floors.json`.  The formula, list lengths and every
rank entry are additionally checked by Lean's kernel using `decide +kernel`.
Named consumer: `MGF.N25.densityBound25` and the order-25 MGF covering lists.
-/

namespace Erdos993Lean.Analytic.MGF.N25.Data

private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- The rank floor of Theorem `p2:thm:O5` restated at order 25 in `certfree/act1_test`:
eight on all 55 subintervals. -/
def kmin25 : List Nat := List.replicate 55 8

/-- The window-only order-25 mean floors of Theorem `p2:thm:O5`, as restated in
`certfree/act1_test`: `8/(2q(pieceHi_p))` on each of the 55 subintervals. -/
def mmin25 : List Rat :=
[
    R (136) 9, R (14) 1, R (116) 9, R (12) 1, R (124) 11, R (32) 3,
    R (132) 13, R (68) 7, R (28) 3, R (356) 39, R (9) 1, R (184) 21,
    R (372) 43, R (748) 87, R (94) 11, R (756) 89, R (764) 91, R (192) 23,
    R (772) 93, R (388) 47, R (49) 6, R (788) 97, R (796) 99, R (8) 1,
    R (812) 103, R (102) 13, R (164) 21, R (828) 107, R (208) 27, R (84) 11,
    R (53) 7, R (428) 57, R (216) 29, R (436) 59, R (22) 3, R (356) 49,
    R (36) 5, R (92) 13, R (188) 27, R (48) 7, R (388) 57, R (196) 29,
    R (20) 3, R (13) 2, R (212) 33, R (108) 17, R (44) 7, R (56) 9,
    R (228) 37, R (116) 19, R (236) 39, R (6) 1, R (244) 41, R (52) 9,
    R (40) 7]

/-- The rank table has the 55 subintervals of order-25 O5 (`certfree/act1_test`),
checked by the kernel. -/
theorem kmin25_length : kmin25.length = 55 := by decide +kernel

/-- The floor table has the 55 subintervals of order-25 O5 (`certfree/act1_test`),
checked by the kernel. -/
theorem mmin25_length : mmin25.length = 55 := by decide +kernel

/-- Every order-25 O5 rank is eight (`certfree/act1_test`, Theorem `p2:thm:O5`),
checked by the kernel. -/
theorem kmin25_eight : ∀ p < 55, kmin25.getD p 0 = 8 := by decide +kernel

/-- The exact floor formula of the order-25 version of Theorem `p2:thm:O5`
(`certfree/act1_test`), checked on every subinterval by the kernel. -/
theorem mmin25_eq : ∀ p < 55, mmin25.getD p 0 =
    (kmin25.getD p 0 : Rat) /
      (2 * (N44.Data.pieceHi.getD p 0 / (1 + N44.Data.pieceHi.getD p 0))) := by
  decide +kernel

end Erdos993Lean.Analytic.MGF.N25.Data
