import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_17, subinterval 17

The paper's activity rectangle is [91/100, 23/25], its exact mean
rectangle is [288/23, 50]. The 6 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_17/box_000000.json`; sha256 `5aae19babba64c3f392bdf04bbb813a75de72e840ef32f8275b423cbe78c01d5`. -/
def boxTo50_17_000 : MBox :=
  ⟨R (91) 191, R (23) 48, R (1869) 46, R (50) 1, R (4169) 92,
   R (331891463) 500000000000, R (389555633) 250000000000,
   R (3060186297885428787409437700979238584868895942859) 340282366920938463463374607431768211456000000000000,
   R (35753731) 500000000000, R (8366511) 500000000000, R (1) 1, R (765617460019) 1000000000000,
   [R (443104378939887) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 376⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_17/box_000001.json`; sha256 `1a99352116c2cb6790bea15ff29dc6ac0eb1f8bce7ea8768345b4a89ce32f20f`. -/
def boxTo50_17_001 : MBox :=
  ⟨R (91) 191, R (23) 48, R (719) 23, R (1869) 46, R (3307) 92,
   R (336869423) 250000000000, R (362278657) 100000000000,
   R (289023718438713672355708035078037723270370945931) 21267647932558653966460912964485513216000000000000,
   R (12415341) 500000000000, R (40758013) 1000000000000, R (1) 1, R (641638340011) 1000000000000,
   [R (29952724515773) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 296⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_17/box_000002.json`; sha256 `89de036fb2394c80a85c1dabb2e32288c555abf1f31526a826a20f11d44c89ec`. -/
def boxTo50_17_002 : MBox :=
  ⟨R (91) 191, R (23) 48, R (1007) 46, R (719) 23, R (2445) 92,
   R (2843674059) 1000000000000, R (678234527) 200000000000,
   R (1708798072814309101098017865889203347971543148187) 85070591730234615865843651857942052864000000000000,
   R (0) 1, R (93643271) 1000000000000, R (1) 1, R (399003177759) 500000000000,
   [R (2022736200881) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 224⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_17/box_000003.json`; sha256 `5d9f4d476ef86a91894e94849b9ce23f954ff9f308f212f8d4111dfe0698c0b2`. -/
def boxTo50_17_003 : MBox :=
  ⟨R (91) 191, R (23) 48, R (1583) 92, R (1007) 46, R (3597) 184,
   R (2792384319) 500000000000, R (1188764329) 200000000000,
   R (1003529570414528339512567654762758482451557599573) 34028236692093846346337460743176821145600000000000,
   R (45641663) 500000000000, R (243673197) 1000000000000, R (1) 1, R (384864995473) 500000000000,
   [R (964250396361) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 168⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_17/box_000004.json`; sha256 `0b7f11afebffca972c74b877169a9f9d21b4e931ad9302f74605173749cea95a`. -/
def boxTo50_17_004 : MBox :=
  ⟨R (91) 191, R (23) 48, R (2735) 184, R (1583) 92, R (5901) 368,
   R (7988240569) 1000000000000, R (12316789567) 1000000000000,
   R (3031516243051688960464825693781404674922545868279) 85070591730234615865843651857942052864000000000000,
   R (272046603) 500000000000, R (2679241) 7812500000, R (1) 1, R (121562820669) 200000000000,
   [R (188459772011) 125000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 72⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_17/box_000005.json`; sha256 `2ef1d4368dafdde394cf8005e27ca7364ead14499d1c07d7e7d6e8a6521c8660`. -/
def boxTo50_17_005 : MBox :=
  ⟨R (91) 191, R (23) 48, R (288) 23, R (2735) 184, R (5039) 368,
   R (11253271711) 1000000000000, R (5569101351) 500000000000,
   R (1458348509701401854565079956766854444545713997) 33230699894622896822595176507008614400000000000,
   R (2287331) 4000000000, R (538365917) 1000000000000, R (1) 1, R (45067145639) 62500000000,
   [R (456641380623) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 60⟩
/-- Lemma 5.4: the exact 6 boxes of To50_17. -/
def boxesTo50_17 : List MBox := [
  boxTo50_17_000,
  boxTo50_17_001,
  boxTo50_17_002,
  boxTo50_17_003,
  boxTo50_17_004,
  boxTo50_17_005
]

/-- Lemma 5.4: the exact cover chains of To50_17. -/
def slabsTo50_17 : List Atlas.Slab := [
  ⟨R (91) 191, R (23) 48, [5, 4, 3, 2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_17 : Rat := R (288) 23

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_17 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
