import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_21, subinterval 21

The paper's activity rectangle is [24/25, 97/100], its exact mean
rectangle is [2561/194, 50]. The 7 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/band14_to50/strip_21/box_000000.json`; sha256 `d1da5c5645fce084d0389bee7026224e5ef987f09ea36a2cee1ed3aebd8166f3`. -/
def boxTo50_21_000 : MBox :=
  ⟨R (24) 49, R (97) 197, R (31661) 776, R (50) 1, R (70461) 1552,
   R (161047369) 250000000000, R (687373197) 1000000000000,
   R (2566307392591922711960277717559350869947955528361) 340282366920938463463374607431768211456000000000000,
   R (47309451) 1000000000000, R (15427777) 1000000000000, R (1) 1, R (450796749269) 500000000000,
   [R (372827389636353) 100000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 376⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/band14_to50/strip_21/box_000001.json`; sha256 `09a3040b179a18da5721411e888b52fa7781257e893b7672df1014a7bcd1da0f`. -/
def boxTo50_21_001 : MBox :=
  ⟨R (24) 49, R (97) 197, R (12261) 388, R (31661) 776, R (56183) 1552,
   R (1322798309) 1000000000000, R (785524443) 1000000000000,
   R (8024316611992187602876723189772803879501340443199) 680564733841876926926749214863536422912000000000000,
   R (0) 1, R (8578877) 250000000000, R (1) 1, R (926550872977) 1000000000000,
   [R (251821857810129) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 304⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/band14_to50/strip_21/box_000002.json`; sha256 `3b7abd63042898aa5271ff1b67fb0f8b61d6f3b30ef8f2f309100eeff5eea59c`. -/
def boxTo50_21_002 : MBox :=
  ⟨R (24) 49, R (97) 197, R (41905) 1552, R (12261) 388, R (90949) 3104,
   R (1903895283) 1000000000000, R (773919521) 1000000000000,
   R (4923966149798639946110977060033293330001354890063) 340282366920938463463374607431768211456000000000000,
   R (68084189) 500000000000, R (12359199) 200000000000, R (1) 1, R (235822795377) 250000000000,
   [R (5666166016609) 200000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 248⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/band14_to50/strip_21/box_000003.json`; sha256 `f1f3d40b22121ab4da79864d9c3dc931a87f04a80bd646c131b9c52a192bf216`. -/
def boxTo50_21_003 : MBox :=
  ⟨R (24) 49, R (97) 197, R (17383) 776, R (41905) 1552, R (76671) 3104,
   R (4720313) 1562500000, R (53658647) 125000000000,
   R (13145085498866703948151846634661308556494201013493) 680564733841876926926749214863536422912000000000000,
   R (186401197) 1000000000000, R (111189111) 1000000000000, R (1) 1, R (978741424299) 1000000000000,
   [R (3832218303171) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 208⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/band14_to50/strip_21/box_000004.json`; sha256 `f985309a6ee0b8d2f3c6fdbed63ad3a2f3a90e5f40a09a62ba0fd7b753e12cba`. -/
def boxTo50_21_004 : MBox :=
  ⟨R (24) 49, R (97) 197, R (27627) 1552, R (17383) 776, R (62393) 3104,
   R (5066487877) 1000000000000, R (1437084283) 500000000000,
   R (138402381273248021323022284257636672192618970069) 5316911983139663491615228241121378304000000000000,
   R (27457481) 250000000000, R (48897993) 250000000000, R (1) 1, R (882451153311) 1000000000000,
   [R (3399205122409) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 176⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/band14_to50/strip_21/box_000005.json`; sha256 `24054e18bb1755fc3048a7bd40147382776af754fb072f5e5c3070bdb282db7c`. -/
def boxTo50_21_005 : MBox :=
  ⟨R (24) 49, R (97) 197, R (48115) 3104, R (27627) 1552, R (103369) 6208,
   R (6919022139) 1000000000000, R (86508337) 50000000000,
   R (10661171698709013493842122906195060679872323884253) 340282366920938463463374607431768211456000000000000,
   R (847335333) 1000000000000, R (325935611) 1000000000000, R (1) 1, R (941948819739) 1000000000000,
   [R (1335383288197) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 144⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/band14_to50/strip_21/box_000006.json`; sha256 `039e7e0795c6873a16e089d35d7dd27e9ba042940511e1094e72a7a8784daf63`. -/
def boxTo50_21_006 : MBox :=
  ⟨R (24) 49, R (97) 197, R (2561) 194, R (48115) 3104, R (89091) 6208,
   R (516678259) 50000000000, R (5188611) 100000000000,
   R (6858231221721372612390562044310430525547610601991) 170141183460469231731687303715884105728000000000000,
   R (846995761) 1000000000000, R (125025539) 250000000000, R (123831475593) 125000000000, R (1) 1,
   [R (559763008303) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 64⟩
/-- Lemma 5.4: the exact 7 boxes of To50_21. -/
def boxesTo50_21 : List MBox := [
  boxTo50_21_000,
  boxTo50_21_001,
  boxTo50_21_002,
  boxTo50_21_003,
  boxTo50_21_004,
  boxTo50_21_005,
  boxTo50_21_006
]

/-- Lemma 5.4: the exact cover chains of To50_21. -/
def slabsTo50_21 : List Atlas.Slab := [
  ⟨R (24) 49, R (97) 197, [6, 5, 4, 3, 2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_21 : Rat := R (2561) 194

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_21 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
