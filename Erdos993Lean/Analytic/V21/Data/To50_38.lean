import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_38, subinterval 38

The paper's activity rectangle is [13/10, 27/20], its exact mean
rectangle is [96/7, 50]. The 5 boxes and
2 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_38/box_000000.json`; sha256 `9480b6d3ee48ffde588dda077396a76fe6ce6a5029a5a45c16a642e33e03fb52`. -/
def boxTo50_38_000 : MBox :=
  ⟨R (13) 23, R (27) 47, R (223) 7, R (50) 1, R (573) 14,
   R (1082345553) 1000000000000, R (-410121417) 100000000000,
   R (248472482210705066660450560896605067473582214967) 10633823966279326983230456482242756608000000000000,
   R (37572023) 500000000000, R (22225419) 500000000000, R (5397821789) 20000000000, R (1) 1,
   [R (288994238970161) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 336⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_38/box_000001.json`; sha256 `511dd931a93b8dc09d206d6f083a141bfd4af18517f10407ed41ee83196410c3`. -/
def boxTo50_38_001 : MBox :=
  ⟨R (13) 23, R (27) 47, R (319) 14, R (223) 7, R (765) 28,
   R (187304121) 62500000000, R (-4889585629) 500000000000,
   R (32730608508037322934025012026596268557458297723) 850705917302346158658436518579420528640000000000,
   R (319095411) 500000000000, R (68007077) 500000000000, R (158562671867) 1000000000000, R (1) 1,
   [R (1714318921647) 100000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 232⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_38/box_000002.json`; sha256 `077dfd60a3374b29b524c2533a3feae4fbcf51cbb1caac484ec438f65d6a8964`. -/
def boxTo50_38_002 : MBox :=
  ⟨R (616) 1081, R (27) 47, R (96) 7, R (319) 14, R (73) 4,
   R (2421400321) 250000000000, R (-24817094757) 1000000000000,
   R (89970860866815209417853629949432651937706644167) 1329227995784915872903807060280344576000000000000,
   R (45684137) 200000000000, R (432684113) 1000000000000, R (22476077321) 200000000000, R (1) 1,
   [R (116965053499) 50000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 80⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_38/box_000003.json`; sha256 `98890a2230c3057f1fe51b63db32220ed7ca2d8b322c80e57706a8e45f5563c3`. -/
def boxTo50_38_003 : MBox :=
  ⟨R (13) 23, R (616) 1081, R (73) 4, R (319) 14, R (1149) 56,
   R (4628931159) 1000000000000, R (-13559187719) 1000000000000,
   R (1862894028068812000891192684771079468552650841303) 42535295865117307932921825928971026432000000000000,
   R (1574677287) 1000000000000, R (249900213) 1000000000000, R (189459426853) 1000000000000, R (1) 1,
   [R (4846612182741) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 176⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_38/box_000004.json`; sha256 `8410fb9c0109991274ae6078f90eb5b83f5b225437842ebba4fe462452af5f57`. -/
def boxTo50_38_004 : MBox :=
  ⟨R (13) 23, R (616) 1081, R (96) 7, R (73) 4, R (895) 56,
   R (9577177857) 1000000000000, R (-5170347561) 200000000000,
   R (667357032914934640288965258221176653926301548779) 10633823966279326983230456482242756608000000000000,
   R (2048487907) 1000000000000, R (476654053) 1000000000000, R (31902434347) 500000000000, R (1) 1,
   [R (2123589023011) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 68⟩
/-- Lemma 5.4: the exact 5 boxes of To50_38. -/
def boxesTo50_38 : List MBox := [
  boxTo50_38_000,
  boxTo50_38_001,
  boxTo50_38_002,
  boxTo50_38_003,
  boxTo50_38_004
]

/-- Lemma 5.4: the exact cover chains of To50_38. -/
def slabsTo50_38 : List Atlas.Slab := [
  ⟨R (13) 23, R (616) 1081, [4, 3, 1, 0]⟩,
  ⟨R (616) 1081, R (27) 47, [2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_38 : Rat := R (96) 7

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_38 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
