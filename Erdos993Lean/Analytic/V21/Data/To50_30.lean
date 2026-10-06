import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_30, subinterval 30

The paper's activity rectangle is [11/10, 28/25], its exact mean
rectangle is [689/56, 50]. The 8 boxes and
2 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_30/box_000000.json`; sha256 `ae3b3503b8a038a3b9e638b67257fb93458c9751a20b39ff0cfcb58b8bb1298d`. -/
def boxTo50_30_000 : MBox :=
  ⟨R (1171) 2226, R (28) 53, R (9089) 224, R (50) 1, R (20289) 448,
   R (27133673) 40000000000, R (-463932429) 200000000000,
   R (687496161333009084408153216155190707237765111127) 68056473384187692692674921486353642291200000000000,
   R (94201529) 1000000000000, R (19877669) 1000000000000, R (316134041513) 500000000000, R (1) 1,
   [R (1578813778707069) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 376⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_30/box_000001.json`; sha256 `3917e65e26dc909440596eb233ec2eebf9b60af6849855ef5a701c0c620248b3`. -/
def boxTo50_30_001 : MBox :=
  ⟨R (1171) 2226, R (28) 53, R (3489) 112, R (9089) 224, R (16067) 448,
   R (40896703) 31250000000, R (-3874438841) 1000000000000,
   R (2446161959406521823063165339023985296579053013471) 170141183460469231731687303715884105728000000000000,
   R (29985117) 500000000000, R (22350159) 500000000000, R (119721857429) 200000000000, R (1) 1,
   [R (374670193187) 2000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 296⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_30/box_000002.json`; sha256 `413e07044a39e6e3eac5af4d56cc8e99868191e6240f9b12afbf286ebd0211af`. -/
def boxTo50_30_002 : MBox :=
  ⟨R (11) 21, R (1171) 2226, R (9089) 224, R (50) 1, R (20289) 448,
   R (651837001) 1000000000000, R (-426106689) 250000000000,
   R (1584448717394232257193219937495082179381311087927) 170141183460469231731687303715884105728000000000000,
   R (13287571) 200000000000, R (18803391) 1000000000000, R (368832208507) 500000000000, R (1) 1,
   [R (1231530522148307) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 376⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_30/box_000003.json`; sha256 `ba0a954905246e933a6a81d37852573450336140129c246b22e15c8135348d1e`. -/
def boxTo50_30_003 : MBox :=
  ⟨R (11) 21, R (1171) 2226, R (3489) 112, R (9089) 224, R (16067) 448,
   R (1351238499) 1000000000000, R (-3206195577) 1000000000000,
   R (2401382171690518813119573078005543025833648757931) 170141183460469231731687303715884105728000000000000,
   R (2041477) 200000000000, R (44721793) 1000000000000, R (684043710573) 1000000000000, R (1) 1,
   [R (165443094393701) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 296⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_30/box_000004.json`; sha256 `96a78e5bf7af99f8bcff45189d6de285ce26271c60bf73e4d0feada30f001906`. -/
def boxTo50_30_004 : MBox :=
  ⟨R (11) 21, R (28) 53, R (4867) 224, R (3489) 112, R (11845) 448,
   R (547497079) 200000000000, R (-1669434457) 500000000000,
   R (170517475745750679057829816784947367016161153757) 8507059173023461586584365185794205286400000000000,
   R (0) 1, R (10915631) 100000000000, R (798088516743) 1000000000000, R (1) 1,
   [R (2033618806687) 200000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 224⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_30/box_000005.json`; sha256 `1d7237f1891a2d51a24e6af519049566b20c1f8a13aaeb6068fc12db2e1a55e1`. -/
def boxTo50_30_005 : MBox :=
  ⟨R (11) 21, R (28) 53, R (1089) 64, R (4867) 224, R (17357) 896,
   R (1461703383) 250000000000, R (-11397649713) 1000000000000,
   R (1311218143571797446967596687618714435903737210169) 42535295865117307932921825928971026432000000000000,
   R (37548177) 500000000000, R (62100467) 250000000000, R (69005971067) 125000000000, R (1) 1,
   [R (4633983229947) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 168⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_30/box_000006.json`; sha256 `9899268860e440f9f68b530789b2c33e4e5f2c2121775001b02f2a9b656b747f`. -/
def boxTo50_30_006 : MBox :=
  ⟨R (11) 21, R (28) 53, R (13135) 896, R (1089) 64, R (28381) 1792,
   R (1939752303) 250000000000, R (-12681816601) 1000000000000,
   R (23475531887324417278451248550608072420321608837) 664613997892457936451903530140172288000000000000,
   R (253530261) 250000000000, R (45625379) 125000000000, R (293305100521) 500000000000, R (1) 1,
   [R (910489480937) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 136⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_30/box_000007.json`; sha256 `850e6d02ea24d4377640a9ba0d500550ca4f7c804ea86cd1d330cf73ff3757f6`. -/
def boxTo50_30_007 : MBox :=
  ⟨R (11) 21, R (28) 53, R (689) 56, R (13135) 896, R (24159) 1792,
   R (11810528981) 1000000000000, R (-724590121) 62500000000,
   R (1925487418605404953084629394943449097932850986337) 42535295865117307932921825928971026432000000000000,
   R (799187633) 1000000000000, R (151181423) 250000000000, R (722356116557) 1000000000000, R (1) 1,
   [R (1025420405757) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 60⟩
/-- Lemma 5.4: the exact 8 boxes of To50_30. -/
def boxesTo50_30 : List MBox := [
  boxTo50_30_000,
  boxTo50_30_001,
  boxTo50_30_002,
  boxTo50_30_003,
  boxTo50_30_004,
  boxTo50_30_005,
  boxTo50_30_006,
  boxTo50_30_007
]

/-- Lemma 5.4: the exact cover chains of To50_30. -/
def slabsTo50_30 : List Atlas.Slab := [
  ⟨R (11) 21, R (1171) 2226, [7, 6, 5, 4, 3, 2]⟩,
  ⟨R (1171) 2226, R (28) 53, [7, 6, 5, 4, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_30 : Rat := R (689) 56

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_30 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
