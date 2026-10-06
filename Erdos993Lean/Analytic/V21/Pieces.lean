import Erdos993Lean.Analytic.MGF.Pieces

/-! Paper v2.1 Lemma 5.4 and Theorem 5.8: the exact caps and rectangle edges.
Source: supplement/twin_v2.1_data.txt, Part 1. The existing activity, theta
and five-rate tables are compared entry by entry by coverage_generate.py. -/

namespace Erdos993Lean.Analytic.V21

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Paper v2.1 Part 1: the hand-variance cap D(iota). -/
def dCaps : List Rat := [R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (6) 5, R (7) 5, R (7) 5, R (7) 5, R (7) 5, R (7) 5, R (8) 5, R (8) 5, R (8) 5, R (8) 5, R (9) 5, R (9) 5, R (9) 5, R (9) 5, R (9) 5, R (21) 10, R (21) 10, R (21) 10]

/-- Paper v2.1 Part 1: lower mean edges m25(iota). -/
def m25 : List Rat := [R (136) 9, R (14) 1, R (116) 9, R (12) 1, R (124) 11, R (32) 3, R (132) 13, R (68) 7, R (28) 3, R (356) 39, R (9) 1, R (184) 21, R (372) 43, R (748) 87, R (94) 11, R (756) 89, R (764) 91, R (192) 23, R (772) 93, R (388) 47, R (49) 6, R (788) 97, R (796) 99, R (8) 1, R (812) 103, R (102) 13, R (164) 21, R (828) 107, R (208) 27, R (84) 11, R (53) 7, R (428) 57, R (216) 29, R (436) 59, R (22) 3, R (356) 49, R (36) 5, R (92) 13, R (188) 27, R (48) 7, R (388) 57, R (196) 29, R (20) 3, R (13) 2, R (212) 33, R (108) 17, R (44) 7, R (56) 9, R (228) 37, R (116) 19, R (236) 39, R (6) 1, R (244) 41, R (52) 9, R (40) 7]

/-- Paper v2.1 Part 1: the split points m*(iota). -/
def mstar : List Rat := [R (68) 3, R (21) 1, R (58) 3, R (18) 1, R (186) 11, R (16) 1, R (198) 13, R (102) 7, R (14) 1, R (178) 13, R (27) 2, R (92) 7, R (558) 43, R (374) 29, R (141) 11, R (1134) 89, R (312) 23, R (288) 23, R (637) 48, R (1261) 94, R (637) 48, R (2561) 194, R (2587) 198, R (13) 1, R (2639) 206, R (51) 4, R (533) 42, R (2691) 214, R (338) 27, R (273) 22, R (689) 56, R (1391) 114, R (351) 29, R (1417) 118, R (143) 12, R (1157) 98, R (63) 5, R (161) 13, R (96) 7, R (96) 7, R (679) 57, R (343) 29, R (35) 3, R (221) 16, R (187) 14, R (405) 34, R (165) 14, R (493) 38, R (493) 38, R (493) 38, R (1037) 82, R (1037) 82, R (1037) 82, R (221) 18, R (90) 7]

/-- Paper v2.1 Lemma 5.4: activity and rates retained, D at the hand cap. -/
def pieceV21 (p : Nat) : MPiece := { piece44 p with D := dCaps.getD p 0 }

end Erdos993Lean.Analytic.V21
