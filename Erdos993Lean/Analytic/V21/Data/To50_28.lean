import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_28, subinterval 28

The paper's activity rectangle is [107/100, 27/25], its exact mean
rectangle is [338/27, 50]. The 7 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_28/box_000000.json`; sha256 `b919d2411cf1cfd01dabf0759f4113d3188df7041c282ca2f94275bf452a37e4`. -/
def boxTo50_28_000 : MBox :=
  ⟨R (107) 207, R (27) 52, R (1097) 27, R (50) 1, R (2447) 54,
   R (173321163) 250000000000, R (-910388167) 500000000000,
   R (752208272233516873278700055688473711929657181911) 85070591730234615865843651857942052864000000000000,
   R (49827071) 1000000000000, R (17752949) 1000000000000, R (183725833973) 250000000000, R (1) 1,
   [R (4254003720346419) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 376⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_28/box_000001.json`; sha256 `0cef0bb9daeb87deeb7e553628ee5f656c49f708d3c96ccd118a9e8d0ce6055d`. -/
def boxTo50_28_001 : MBox :=
  ⟨R (107) 207, R (27) 52, R (844) 27, R (1097) 27, R (647) 18,
   R (244710401) 200000000000, R (-71643799) 40000000000,
   R (163770845163650468018548266592739757198614045633) 13611294676837538538534984297270728458240000000000,
   R (30034337) 1000000000000, R (4798943) 125000000000, R (12852420659) 15625000000, R (1) 1,
   [R (158075004250419) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 296⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_28/box_000002.json`; sha256 `73101f68f7c7f7c6a983a4fb09cc70a91f20823b7f34a043bf887968e0dee56e`. -/
def boxTo50_28_002 : MBox :=
  ⟨R (107) 207, R (27) 52, R (1435) 54, R (844) 27, R (347) 12,
   R (1012084541) 500000000000, R (-1621048329) 500000000000,
   R (1367444393302353074825810995511298589797752039783) 85070591730234615865843651857942052864000000000000,
   R (34711357) 200000000000, R (2822301) 40000000000, R (380609660413) 500000000000, R (1) 1,
   [R (41963033135817) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 240⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_28/box_000003.json`; sha256 `12ac61f5719e6a42402f70ade70118a7cb143d71a9bd27d1f1e32c1b3a238203`. -/
def boxTo50_28_003 : MBox :=
  ⟨R (107) 207, R (27) 52, R (197) 9, R (1435) 54, R (2617) 108,
   R (639477273) 200000000000, R (-865602249) 250000000000,
   R (443166938839166392645678803670110885150289368789) 21267647932558653966460912964485513216000000000000,
   R (62435491) 500000000000, R (116391057) 1000000000000, R (810493831713) 1000000000000, R (1) 1,
   [R (3667256619153) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 208⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_28/box_000004.json`; sha256 `c61496084f046aca92d5f6fb381bd111d983384086be62f88ff75960b61c7635`. -/
def boxTo50_28_004 : MBox :=
  ⟨R (107) 207, R (27) 52, R (929) 54, R (197) 9, R (2111) 108,
   R (1356153499) 250000000000, R (-195027163) 100000000000,
   R (4812023767175021387325048376602256009211584612469) 170141183460469231731687303715884105728000000000000,
   R (54701303) 250000000000, R (57787229) 250000000000, R (464501560099) 500000000000, R (1) 1,
   [R (99875918281) 31250000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 168⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_28/box_000005.json`; sha256 `59a172c5ac1a4f4958ebcae9bf9f9c2833b7e69b9beaa19c97ee7f15887a7294`. -/
def boxTo50_28_005 : MBox :=
  ⟨R (107) 207, R (27) 52, R (535) 36, R (929) 54, R (3463) 216,
   R (8293954493) 1000000000000, R (-2517606777) 500000000000,
   R (3101060425055085730641648288921963011605883861743) 85070591730234615865843651857942052864000000000000,
   R (224734831) 500000000000, R (109282737) 250000000000, R (847910033927) 1000000000000, R (1) 1,
   [R (362943936487) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 72⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_28/box_000006.json`; sha256 `28566b8a1bbd65914fb10c1af830052ae065a9089fca4acfff9d79c228e5ddd5`. -/
def boxTo50_28_006 : MBox :=
  ⟨R (107) 207, R (27) 52, R (338) 27, R (535) 36, R (2957) 216,
   R (11456036281) 1000000000000, R (-7424349927) 500000000000,
   R (1804431732116000162314396859656440055370000348707) 42535295865117307932921825928971026432000000000000,
   R (579245989) 1000000000000, R (587597413) 1000000000000, R (158139897101) 250000000000, R (1) 1,
   [R (989386320207) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 60⟩
/-- Lemma 5.4: the exact 7 boxes of To50_28. -/
def boxesTo50_28 : List MBox := [
  boxTo50_28_000,
  boxTo50_28_001,
  boxTo50_28_002,
  boxTo50_28_003,
  boxTo50_28_004,
  boxTo50_28_005,
  boxTo50_28_006
]

/-- Lemma 5.4: the exact cover chains of To50_28. -/
def slabsTo50_28 : List Atlas.Slab := [
  ⟨R (107) 207, R (27) 52, [6, 5, 4, 3, 2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_28 : Rat := R (338) 27

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_28 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
