import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_52, subinterval 52

The paper's activity rectangle is [2, 41/20], its exact mean
rectangle is [1037/82, 50]. The 3 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_52/box_000000.json`; sha256 `728395922de5ecf7c979021034bc0b12472342b8387fff98f339ca51897cf8fa`. -/
def boxTo50_52_000 : MBox :=
  ⟨R (2) 3, R (41) 61, R (5137) 164, R (50) 1, R (13337) 328,
   R (579389857) 1000000000000, R (-116517003) 100000000000,
   R (2644424463924836530015952391904934843088131052433) 85070591730234615865843651857942052864000000000000,
   R (256338309) 500000000000, R (13996861) 500000000000, R (0) 1, R (1) 1,
   [R (0) 1, R (0) 1, R (3278047218911) 25000000000, R (0) 1, R (0) 1], 336⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_52/box_000001.json`; sha256 `90a15eaec8e99c5324b5332f0ce28646710239333664914ff96574427e8ff4c9`. -/
def boxTo50_52_001 : MBox :=
  ⟨R (2) 3, R (41) 61, R (7211) 328, R (5137) 164, R (17485) 656,
   R (1747014921) 1000000000000, R (-3363320379) 1000000000000,
   R (1103932510337302527331867988777524141819539960409) 21267647932558653966460912964485513216000000000000,
   R (389211391) 250000000000, R (105676737) 1000000000000, R (0) 1, R (1) 1,
   [R (5082043724633) 200000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 224⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_52/box_000002.json`; sha256 `320d6bda973d5e10612b6ba6a79d58addbc580f833a0e85b9118d29d5ab71ab8`. -/
def boxTo50_52_002 : MBox :=
  ⟨R (2) 3, R (41) 61, R (1037) 82, R (7211) 328, R (11359) 656,
   R (10224926609) 1000000000000, R (-17155089239) 1000000000000,
   R (1433452897881067952830953860215565983897338180307) 10633823966279326983230456482242756608000000000000,
   R (4704776227) 1000000000000, R (91379) 200000000, R (0) 1, R (1) 1,
   [R (1476215068099) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 76⟩
/-- Lemma 5.4: the exact 3 boxes of To50_52. -/
def boxesTo50_52 : List MBox := [
  boxTo50_52_000,
  boxTo50_52_001,
  boxTo50_52_002
]

/-- Lemma 5.4: the exact cover chains of To50_52. -/
def slabsTo50_52 : List Atlas.Slab := [
  ⟨R (2) 3, R (41) 61, [2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_52 : Rat := R (1037) 82

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_52 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
