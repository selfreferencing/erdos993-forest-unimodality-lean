import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_20, subinterval 20

The paper's activity rectangle is [47/50, 24/25], its exact mean
rectangle is [637/48, 50]. The 7 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_20/box_000000.json`; sha256 `bf1f191ef60edc16556b070f571b2ced5ce5b4a0a120c19208edee4c2bb36810`. -/
def boxTo50_20_000 : MBox :=
  ⟨R (47) 97, R (24) 49, R (7837) 192, R (50) 1, R (17437) 384,
   R (648434761) 1000000000000, R (13759631) 15625000000,
   R (105526245970787310669893130860431812917576490429) 13611294676837538538534984297270728458240000000000,
   R (51086551) 1000000000000, R (8252321) 500000000000, R (1) 1, R (174305540857) 200000000000,
   [R (998014327060017) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 376⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_20/box_000001.json`; sha256 `a42183049d01871fdd597f6099083efe1dc7577bcc0fb434140e4eeb49e2384a`. -/
def boxTo50_20_001 : MBox :=
  ⟨R (47) 97, R (24) 49, R (3037) 96, R (7837) 192, R (4637) 128,
   R (644171721) 500000000000, R (1647612523) 1000000000000,
   R (988215799244681315909780791108315553985339085989) 85070591730234615865843651857942052864000000000000,
   R (0) 1, R (17963441) 500000000000, R (1) 1, R (84187905899) 100000000000,
   [R (32988228214751) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 304⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_20/box_000002.json`; sha256 `c9afe73cc1c01a09f30b2c454eb9c3cc792debb04237b09d36cb1b75b63da611`. -/
def boxTo50_20_002 : MBox :=
  ⟨R (47) 97, R (24) 49, R (10385) 384, R (3037) 96, R (7511) 256,
   R (938163373) 500000000000, R (627949491) 1000000000000,
   R (1225613916042503753364280420978067204348931168619) 85070591730234615865843651857942052864000000000000,
   R (50905377) 250000000000, R (6864381) 125000000000, R (1) 1, R (238768622567) 250000000000,
   [R (43230822181561) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 248⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_20/box_000003.json`; sha256 `e35eaa4771ee1542ac0eaf4dc9cd20ffe5bd592040655812229af4a5e7f32201`. -/
def boxTo50_20_003 : MBox :=
  ⟨R (47) 97, R (24) 49, R (1437) 64, R (10385) 384, R (19007) 768,
   R (76518349) 25000000000, R (732051729) 250000000000,
   R (3294170578275517045074982659491517237162747355009) 170141183460469231731687303715884105728000000000000,
   R (32761767) 200000000000, R (54640091) 500000000000, R (1) 1, R (33372497731) 40000000000,
   [R (7953654008291) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 208⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_20/box_000004.json`; sha256 `efecb4a4868eb18b96c57b3ef8bea3409f336d4b7b6b47c3629f376e20d8161b`. -/
def boxTo50_20_004 : MBox :=
  ⟨R (47) 97, R (24) 49, R (6859) 384, R (1437) 64, R (15481) 768,
   R (5087781361) 1000000000000, R (473725983) 250000000000,
   R (1118449764246866688559642820859894840476541692353) 42535295865117307932921825928971026432000000000000,
   R (63154901) 1000000000000, R (201925801) 1000000000000, R (1) 1, R (185141419239) 200000000000,
   [R (61743903053) 20000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 176⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_20/box_000005.json`; sha256 `2fe0417e92391065b92d3f1a7a618b936a809b1d97f44a944ac968ae0cb4df25`. -/
def boxTo50_20_005 : MBox :=
  ⟨R (47) 97, R (24) 49, R (3985) 256, R (6859) 384, R (25673) 1536,
   R (1786909683) 250000000000, R (1674469649) 1000000000000,
   R (5462069993030219875257941129906079562316501961327) 170141183460469231731687303715884105728000000000000,
   R (753634571) 1000000000000, R (163846757) 500000000000, R (1) 1, R (473434021863) 500000000000,
   [R (690627213731) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 144⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_20/box_000006.json`; sha256 `11c2fd45028a13d9b84a1f5520a403caa6ee1fe0166ca584d9606dd5dad896c4`. -/
def boxTo50_20_006 : MBox :=
  ⟨R (47) 97, R (24) 49, R (637) 48, R (3985) 256, R (22147) 1536,
   R (10918923757) 1000000000000, R (151138547) 125000000000,
   R (3533202281015879181587970162365112934568467597733) 85070591730234615865843651857942052864000000000000,
   R (488695297) 1000000000000, R (63650349) 125000000000, R (1) 1, R (984646685281) 1000000000000,
   [R (1131818449229) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 64⟩
/-- Lemma 5.4: the exact 7 boxes of To50_20. -/
def boxesTo50_20 : List MBox := [
  boxTo50_20_000,
  boxTo50_20_001,
  boxTo50_20_002,
  boxTo50_20_003,
  boxTo50_20_004,
  boxTo50_20_005,
  boxTo50_20_006
]

/-- Lemma 5.4: the exact cover chains of To50_20. -/
def slabsTo50_20 : List Atlas.Slab := [
  ⟨R (47) 97, R (24) 49, [6, 5, 4, 3, 2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_20 : Rat := R (637) 48

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_20 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
