import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_14, subinterval 14

The paper's activity rectangle is [87/100, 22/25], its exact mean
rectangle is [141/11, 50]. The 4 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_14/box_000000.json`; sha256 `4c99eaced7b8ad5b18b2cf1f206d249224810f239814b3fa7b95ffc2237d2f55`. -/
def boxTo50_14_000 : MBox :=
  ⟨R (87) 187, R (22) 47, R (691) 22, R (50) 1, R (1791) 44,
   R (230535971) 200000000000, R (609353477) 200000000000,
   R (156785899897047245259573638981276689089258197273) 10633823966279326983230456482242756608000000000000,
   R (0) 1, R (14887629) 500000000000, R (1) 1, R (323830022683) 500000000000,
   [R (13033358160583) 125000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 336⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_14/box_000001.json`; sha256 `2ba863216d4cb10879bdcc5261edcfe34ac31e35626b538ea5a04e7bc4a68607`. -/
def boxTo50_14_001 : MBox :=
  ⟨R (87) 187, R (22) 47, R (973) 44, R (691) 22, R (2355) 88,
   R (1582370723) 500000000000, R (8256619971) 1000000000000,
   R (2110712812894122233755056032349259738787781977821) 85070591730234615865843651857942052864000000000000,
   R (0) 1, R (50250191) 500000000000, R (1) 1, R (247462148653) 500000000000,
   [R (5385175138499) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 224⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_14/box_000002.json`; sha256 `fd5200d3fa57db1b11676383d9953a9d77cb2e1138148394dec0e2d99eba6f9c`. -/
def boxTo50_14_002 : MBox :=
  ⟨R (87) 187, R (22) 47, R (1537) 88, R (973) 44, R (3483) 176,
   R (1016004333) 200000000000, R (10397914131) 1000000000000,
   R (2639274030561646517422521035831542376648602610389) 85070591730234615865843651857942052864000000000000,
   R (425467807) 1000000000000, R (218281171) 1000000000000, R (1) 1, R (547814125383) 1000000000000,
   [R (1937777960219) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 168⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_14/box_000003.json`; sha256 `ef7a5f0c12d0bf990bca6669b9f2d7caa1a2f2c482c6fe56fab2e72271861656`. -/
def boxTo50_14_003 : MBox :=
  ⟨R (87) 187, R (22) 47, R (141) 11, R (1537) 88, R (2665) 176,
   R (2059618127) 200000000000, R (9616033359) 1000000000000,
   R (1873453472966761129580581126471276300622353501339) 42535295865117307932921825928971026432000000000000,
   R (4451671) 50000000000, R (207043353) 500000000000, R (1) 1, R (75654797437) 100000000000,
   [R (928380333801) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 68⟩
/-- Lemma 5.4: the exact 4 boxes of To50_14. -/
def boxesTo50_14 : List MBox := [
  boxTo50_14_000,
  boxTo50_14_001,
  boxTo50_14_002,
  boxTo50_14_003
]

/-- Lemma 5.4: the exact cover chains of To50_14. -/
def slabsTo50_14 : List Atlas.Slab := [
  ⟨R (87) 187, R (22) 47, [3, 2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_14 : Rat := R (141) 11

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_14 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
