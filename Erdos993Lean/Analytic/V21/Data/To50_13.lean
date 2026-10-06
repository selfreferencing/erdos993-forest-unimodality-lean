import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_13, subinterval 13

The paper's activity rectangle is [43/50, 87/100], its exact mean
rectangle is [374/29, 50]. The 4 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_13/box_000000.json`; sha256 `ebcfa24b5be26d0a412b1ff83ee0329e3050a40b58c01b5b1860d28425b254cd`. -/
def boxTo50_13_000 : MBox :=
  ⟨R (43) 93, R (87) 187, R (912) 29, R (50) 1, R (1181) 29,
   R (231673007) 200000000000, R (101954081) 31250000000,
   R (2647653498370605720714388680489549035161676137193) 170141183460469231731687303715884105728000000000000,
   R (0) 1, R (244427) 7812500000, R (1) 1, R (616510775809) 1000000000000,
   [R (99035588991307) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 336⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_13/box_000001.json`; sha256 `fa8bfd59500fa5a319142ba93489c12b131840df84756179367bd24e5c2d05ea`. -/
def boxTo50_13_001 : MBox :=
  ⟨R (43) 93, R (87) 187, R (643) 29, R (912) 29, R (1555) 58,
   R (606684891) 200000000000, R (8088698323) 1000000000000,
   R (85919392944307466943824643507625506969071075249) 3402823669209384634633746074317682114560000000000,
   R (9993191) 1000000000000, R (5407847) 50000000000, R (1) 1, R (19397667807) 40000000000,
   [R (1058399055471) 125000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 224⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_13/box_000002.json`; sha256 `e6bd554ce66d9dfa7ea5edb8cff72d42aed2dc7db01b39f3856ce673ce182d14`. -/
def boxTo50_13_002 : MBox :=
  ⟨R (43) 93, R (87) 187, R (1017) 58, R (643) 29, R (2303) 116,
   R (1018966689) 200000000000, R (9674514541) 1000000000000,
   R (1356699114150251949233663597327632100456542659697) 42535295865117307932921825928971026432000000000000,
   R (428607053) 1000000000000, R (212330889) 1000000000000, R (1) 1, R (580374306309) 1000000000000,
   [R (376575061613) 200000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 168⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_13/box_000003.json`; sha256 `a21c4145a209116ef356395f2f910073208b2941c1f732f817e5cad257f1c109`. -/
def boxTo50_13_003 : MBox :=
  ⟨R (43) 93, R (87) 187, R (374) 29, R (1017) 58, R (1765) 116,
   R (4671703743) 500000000000, R (1159913391) 125000000000,
   R (55884150969050713070445205531487722872234010911) 1329227995784915872903807060280344576000000000000,
   R (524242241) 1000000000000, R (374441257) 1000000000000, R (1) 1, R (753694994317) 1000000000000,
   [R (464679099909) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 136⟩
/-- Lemma 5.4: the exact 4 boxes of To50_13. -/
def boxesTo50_13 : List MBox := [
  boxTo50_13_000,
  boxTo50_13_001,
  boxTo50_13_002,
  boxTo50_13_003
]

/-- Lemma 5.4: the exact cover chains of To50_13. -/
def slabsTo50_13 : List Atlas.Slab := [
  ⟨R (43) 93, R (87) 187, [3, 2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_13 : Rat := R (374) 29

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_13 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
