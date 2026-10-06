import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_15, subinterval 15

The paper's activity rectangle is [22/25, 89/100], its exact mean
rectangle is [1134/89, 50]. The 4 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_15/box_000000.json`; sha256 `86aaab17252f0c819100a53c8105b896ebdbf9b52edef130086e9642b14f6019`. -/
def boxTo50_15_000 : MBox :=
  ⟨R (22) 47, R (89) 189, R (2792) 89, R (50) 1, R (3621) 89,
   R (593989857) 500000000000, R (3332090857) 1000000000000,
   R (2464520834622059836198470057992028689158056294597) 170141183460469231731687303715884105728000000000000,
   R (0) 1, R (5864197) 200000000000, R (1) 1, R (312386643069) 500000000000,
   [R (4975863652227) 40000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 336⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_15/box_000001.json`; sha256 `688fd2d339a74425cb02070736801f0ce0b05f8fecd674f07ec752260825b7a8`. -/
def boxTo50_15_001 : MBox :=
  ⟨R (22) 47, R (89) 189, R (1963) 89, R (2792) 89, R (4755) 178,
   R (728376259) 250000000000, R (687311847) 100000000000,
   R (484605941701834371932553081402096390631817257307) 21267647932558653966460912964485513216000000000000,
   R (0) 1, R (53502099) 500000000000, R (1) 1, R (11430491123) 20000000000,
   [R (4395942665039) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 224⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_15/box_000002.json`; sha256 `eb6dddfb1e8c5cb7cc315f201e94d9a0af9aa1ab015e999802cfc5d83dd9c577`. -/
def boxTo50_15_002 : MBox :=
  ⟨R (22) 47, R (89) 189, R (3097) 178, R (1963) 89, R (7023) 356,
   R (5295611849) 1000000000000, R (433319019) 40000000000,
   R (1313666839040094127105532791591683819836620191379) 42535295865117307932921825928971026432000000000000,
   R (14343071) 50000000000, R (28145291) 125000000000, R (1) 1, R (271868898439) 500000000000,
   [R (1017327765899) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 168⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_15/box_000003.json`; sha256 `421b344d9a18d401c17b566dd2a52444da99178838cf942ad2d5cf098a0b25e2`. -/
def boxTo50_15_003 : MBox :=
  ⟨R (22) 47, R (89) 189, R (1134) 89, R (3097) 178, R (5365) 356,
   R (5048144691) 500000000000, R (5244966973) 500000000000,
   R (730572923586635770823979188104427285118833047501) 17014118346046923173168730371588410572800000000000,
   R (102260371) 500000000000, R (210405083) 500000000000, R (1) 1, R (725352672561) 1000000000000,
   [R (462152280947) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 68⟩
/-- Lemma 5.4: the exact 4 boxes of To50_15. -/
def boxesTo50_15 : List MBox := [
  boxTo50_15_000,
  boxTo50_15_001,
  boxTo50_15_002,
  boxTo50_15_003
]

/-- Lemma 5.4: the exact cover chains of To50_15. -/
def slabsTo50_15 : List Atlas.Slab := [
  ⟨R (22) 47, R (89) 189, [3, 2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_15 : Rat := R (1134) 89

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_15 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
