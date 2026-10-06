import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_35, subinterval 35

The paper's activity rectangle is [6/5, 49/40], its exact mean
rectangle is [1157/98, 50]. The 4 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_35/box_000000.json`; sha256 `091e6b0fd2362efee4b537840817bd165604f58e87e5c270242b1324c100f120`. -/
def boxTo50_35_000 : MBox :=
  ⟨R (6) 11, R (49) 89, R (6057) 196, R (50) 1, R (15857) 392,
   R (697233213) 500000000000, R (-4840407899) 1000000000000,
   R (359609245459047765803955663504255169223234783971) 17014118346046923173168730371588410572800000000000,
   R (0) 1, R (42483991) 1000000000000, R (41235526771) 100000000000, R (1) 1,
   [R (0) 1, R (54851743844719) 500000000000, R (0) 1, R (0) 1, R (0) 1], 336⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_35/box_000001.json`; sha256 `90037478698e88639611df616fec3a75bcc3bf4a5790a8dbf5f0b306f4f7adb4`. -/
def boxTo50_35_001 : MBox :=
  ⟨R (6) 11, R (49) 89, R (8371) 392, R (6057) 196, R (20485) 784,
   R (3204681699) 1000000000000, R (-4537945007) 500000000000,
   R (1263177703992528771470760791833134923098564025161) 42535295865117307932921825928971026432000000000000,
   R (0) 1, R (18855703) 125000000000, R (404964527741) 1000000000000, R (1) 1,
   [R (4058145950339) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 112⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_35/box_000002.json`; sha256 `fc33fa1cea49de54a65e750483d84c9e944a513bc14e1e20df94f6e3192e44f0`. -/
def boxTo50_35_002 : MBox :=
  ⟨R (6) 11, R (49) 89, R (1857) 112, R (8371) 392, R (29741) 1568,
   R (5267741919) 1000000000000, R (-10167738047) 1000000000000,
   R (1527950267820706343023625508290642518024922292237) 42535295865117307932921825928971026432000000000000,
   R (792480371) 1000000000000, R (286796573) 1000000000000, R (4322446707) 7812500000, R (1) 1,
   [R (2694473703143) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 160⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_35/box_000003.json`; sha256 `0174b885a22de9b092aa227bbf4f8210c721c816726a266824ac527abfe19c7d`. -/
def boxTo50_35_003 : MBox :=
  ⟨R (6) 11, R (49) 89, R (1157) 98, R (1857) 112, R (22255) 1568,
   R (13698680069) 1000000000000, R (-29173884253) 1000000000000,
   R (630756093942757395050759325838760496093459779889) 10633823966279326983230456482242756608000000000000,
   R (0) 1, R (628634421) 1000000000000, R (282620653567) 1000000000000, R (1) 1,
   [R (362942936719) 200000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 64⟩
/-- Lemma 5.4: the exact 4 boxes of To50_35. -/
def boxesTo50_35 : List MBox := [
  boxTo50_35_000,
  boxTo50_35_001,
  boxTo50_35_002,
  boxTo50_35_003
]

/-- Lemma 5.4: the exact cover chains of To50_35. -/
def slabsTo50_35 : List Atlas.Slab := [
  ⟨R (6) 11, R (49) 89, [3, 2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_35 : Rat := R (1157) 98

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_35 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
