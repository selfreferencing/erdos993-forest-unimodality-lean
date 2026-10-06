import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_31, subinterval 31

The paper's activity rectangle is [28/25, 57/50], its exact mean
rectangle is [1391/114, 50]. The 5 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_31/box_000000.json`; sha256 `edfb4f1015850b2db9bd255dad3b81e04fd2793bdea0aaa64d08b881b474c3f9`. -/
def boxTo50_31_000 : MBox :=
  ⟨R (28) 53, R (57) 107, R (7091) 228, R (50) 1, R (18491) 456,
   R (305326947) 250000000000, R (-141592381) 40000000000,
   R (24748815703749362946556664231558087307794724597) 1701411834604692317316873037158841057280000000000,
   R (0) 1, R (16259047) 500000000000, R (605079256543) 1000000000000, R (1) 1,
   [R (0) 1, R (123167340616581) 1000000000000, R (0) 1, R (0) 1, R (0) 1], 336⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_31/box_000001.json`; sha256 `c47256bc1c6fc38bf9ad01b6e3291ef317d20d00bd777eaeeb0701159c43904f`. -/
def boxTo50_31_001 : MBox :=
  ⟨R (28) 53, R (57) 107, R (3291) 152, R (7091) 228, R (24055) 912,
   R (11565583) 4000000000, R (-2718673271) 500000000000,
   R (377076423516687622210384922662066919554667508203) 17014118346046923173168730371588410572800000000000,
   R (0) 1, R (2418427) 20000000000, R (665215433511) 1000000000000, R (1) 1,
   [R (5718792159653) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 224⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_31/box_000002.json`; sha256 `4623b522f48fde65851cf09e7747998fa1b518c1da9ca4bae1f2fada5359f509`. -/
def boxTo50_31_002 : MBox :=
  ⟨R (28) 53, R (57) 107, R (15437) 912, R (3291) 152, R (35183) 1824,
   R (1494620961) 250000000000, R (-322066533) 31250000000,
   R (2782678279194931237822408880467565831281529238719) 85070591730234615865843651857942052864000000000000,
   R (82010219) 1000000000000, R (62872887) 250000000000, R (119879535763) 200000000000, R (1) 1,
   [R (2363831737301) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 84⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_31/box_000003.json`; sha256 `4d21dfe7650b6a8572c29f1312835d759345bc369dd44fb1738179358eec07ea`. -/
def boxTo50_31_003 : MBox :=
  ⟨R (28) 53, R (57) 107, R (8855) 608, R (15437) 912, R (57439) 3648,
   R (770191943) 100000000000, R (-5782974339) 500000000000,
   R (778846705885194294713597824886570498770908293989) 21267647932558653966460912964485513216000000000000,
   R (109292201) 100000000000, R (376863227) 1000000000000, R (622316918339) 1000000000000, R (1) 1,
   [R (1821538239581) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 136⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_31/box_000004.json`; sha256 `5aaa8aa492b66b3dc31b5203bbcbfc55f4e081d5fc117eac489581c83f0bf98b`. -/
def boxTo50_31_004 : MBox :=
  ⟨R (28) 53, R (57) 107, R (1391) 114, R (8855) 608, R (48821) 3648,
   R (2331071383) 200000000000, R (-10040253513) 1000000000000,
   R (7850131335301644800847588380227047645243719273) 170141183460469231731687303715884105728000000000,
   R (128369613) 125000000000, R (620022483) 1000000000000, R (380148034137) 500000000000, R (1) 1,
   [R (1022748985587) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 60⟩
/-- Lemma 5.4: the exact 5 boxes of To50_31. -/
def boxesTo50_31 : List MBox := [
  boxTo50_31_000,
  boxTo50_31_001,
  boxTo50_31_002,
  boxTo50_31_003,
  boxTo50_31_004
]

/-- Lemma 5.4: the exact cover chains of To50_31. -/
def slabsTo50_31 : List Atlas.Slab := [
  ⟨R (28) 53, R (57) 107, [4, 3, 2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_31 : Rat := R (1391) 114

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_31 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
