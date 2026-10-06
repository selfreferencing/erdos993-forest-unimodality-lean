import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_19, subinterval 19

The paper's activity rectangle is [93/100, 47/50], its exact mean
rectangle is [1261/94, 50]. The 7 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_19/box_000000.json`; sha256 `fa0566cf800d29c3b1af7d3da2e0b2fc5e662435ed7db406d47561e7fbea4a1f`. -/
def boxTo50_19_000 : MBox :=
  ⟨R (93) 193, R (47) 97, R (15361) 376, R (50) 1, R (34161) 752,
   R (343022549) 500000000000, R (1853665561) 1000000000000,
   R (183006420316318011290443195553161673398647083) 21267647932558653966460912964485513216000000000,
   R (12318243) 250000000000, R (17720259) 1000000000000, R (1) 1, R (728911156861) 1000000000000,
   [R (1920101013575869) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 376⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_19/box_000001.json`; sha256 `cac779930634fc7bc3fbb1daaab931a9495b4a9802df455e428d6f2fc9f19bb1`. -/
def boxTo50_19_001 : MBox :=
  ⟨R (93) 193, R (47) 97, R (5961) 188, R (15361) 376, R (27283) 752,
   R (48504491) 40000000000, R (1509649229) 1000000000000,
   R (4018136087194280590753080472508423709066160765829) 340282366920938463463374607431768211456000000000000,
   R (35100991) 1000000000000, R (2226957) 62500000000, R (1) 1, R (849003646017) 1000000000000,
   [R (107065468664911) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 304⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_19/box_000002.json`; sha256 `92f8523b3bc78db9d4cfb1f25383decb19f29a2511f64eaba4b9c88328478413`. -/
def boxTo50_19_002 : MBox :=
  ⟨R (93) 193, R (47) 97, R (20405) 752, R (5961) 188, R (44249) 1504,
   R (455833527) 250000000000, R (1043445629) 500000000000,
   R (2518344366367622227518249829809460767361615224393) 170141183460469231731687303715884105728000000000000,
   R (91447793) 500000000000, R (7790097) 125000000000, R (1) 1, R (839045758661) 1000000000000,
   [R (36543034742599) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 248⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_19/box_000003.json`; sha256 `ef8c623ea1737923cb656bfae87d50fc1ad4bcb6e85cda6f38e8e4f43438c9e9`. -/
def boxTo50_19_003 : MBox :=
  ⟨R (93) 193, R (47) 97, R (8483) 376, R (20405) 752, R (37371) 1504,
   R (2958662497) 1000000000000, R (64087171) 15625000000,
   R (1671482373166240521956664247888297903910156693319) 85070591730234615865843651857942052864000000000000,
   R (30881143) 200000000000, R (21521291) 200000000000, R (1) 1, R (762944104559) 1000000000000,
   [R (3709264530063) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 208⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_19/box_000004.json`; sha256 `34ec161f19ee9208414fa2ad925e5cf17f88b53a08e58c797806b2f316289637`. -/
def boxTo50_19_004 : MBox :=
  ⟨R (93) 193, R (47) 97, R (13527) 752, R (8483) 376, R (30493) 1504,
   R (4633145999) 1000000000000, R (1725216159) 1000000000000,
   R (2154924162479613880245877822179232350218883181113) 85070591730234615865843651857942052864000000000000,
   R (89355603) 250000000000, R (180490367) 1000000000000, R (1) 1, R (232486815441) 250000000000,
   [R (2844488877361) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 176⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_19/box_000005.json`; sha256 `d94878cecd4da2244ae51474f52f37eebdb26a91d7bdb6766f44832e4d9d585b`. -/
def boxTo50_19_005 : MBox :=
  ⟨R (93) 193, R (47) 97, R (23615) 1504, R (13527) 752, R (50669) 3008,
   R (6363779501) 1000000000000, R (2312422879) 1000000000000,
   R (5141559984428301224953141364377848354469779682579) 170141183460469231731687303715884105728000000000000,
   R (235202287) 250000000000, R (289400073) 1000000000000, R (1) 1, R (461642541689) 500000000000,
   [R (873535392607) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 144⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_19/box_000006.json`; sha256 `c1fb2e1f53035dab09cbb3abd5b0cdc2b1701d09f1238e55457df3975bc2bc44`. -/
def boxTo50_19_006 : MBox :=
  ⟨R (93) 193, R (47) 97, R (1261) 94, R (23615) 1504, R (43791) 3008,
   R (10453351991) 1000000000000, R (2482028283) 250000000000,
   R (3502170253023187300080531995366356838418198647081) 85070591730234615865843651857942052864000000000000,
   R (0) 1, R (513354639) 1000000000000, R (1) 1, R (36904478379) 50000000000,
   [R (140504142471) 125000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 64⟩
/-- Lemma 5.4: the exact 7 boxes of To50_19. -/
def boxesTo50_19 : List MBox := [
  boxTo50_19_000,
  boxTo50_19_001,
  boxTo50_19_002,
  boxTo50_19_003,
  boxTo50_19_004,
  boxTo50_19_005,
  boxTo50_19_006
]

/-- Lemma 5.4: the exact cover chains of To50_19. -/
def slabsTo50_19 : List Atlas.Slab := [
  ⟨R (93) 193, R (47) 97, [6, 5, 4, 3, 2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_19 : Rat := R (1261) 94

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_19 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
