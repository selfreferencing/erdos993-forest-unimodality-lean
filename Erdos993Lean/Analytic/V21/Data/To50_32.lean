import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_32, subinterval 32

The paper's activity rectangle is [57/50, 29/25], its exact mean
rectangle is [351/29, 50]. The 5 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_32/box_000000.json`; sha256 `42af2cbe2acd4babe0d32ec9e5220f23844386ceb97c567e1c80685d2868c547`. -/
def boxTo50_32_000 : MBox :=
  ⟨R (57) 107, R (29) 54, R (1801) 58, R (50) 1, R (4701) 116,
   R (284912551) 250000000000, R (-3297668039) 1000000000000,
   R (1268776617413241794771702881303796111957799568901) 85070591730234615865843651857942052864000000000000,
   R (0) 1, R (16727909) 500000000000, R (610090623933) 1000000000000, R (1) 1,
   [R (0) 1, R (8354564934003) 50000000000, R (0) 1, R (0) 1, R (0) 1], 336⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_32/box_000001.json`; sha256 `edb6c3a2ef8f95692f766b69c50ba087919da16f510703e894e4196133d1729d`. -/
def boxTo50_32_001 : MBox :=
  ⟨R (57) 107, R (29) 54, R (2503) 116, R (1801) 58, R (6105) 232,
   R (99737671) 31250000000, R (-3679130517) 500000000000,
   R (42441878055946692236292240928483782583792000639) 1701411834604692317316873037158841057280000000000,
   R (0) 1, R (15362603) 125000000000, R (558512066703) 1000000000000, R (1) 1,
   [R (3582957279031) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 224⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_32/box_000002.json`; sha256 `21ee330d5af84cd8b33ac4ace1a3d1ffa0c0117ee906765f8c104c1378dfac6f`. -/
def boxTo50_32_002 : MBox :=
  ⟨R (57) 107, R (29) 54, R (3907) 232, R (2503) 116, R (8913) 464,
   R (5712428801) 1000000000000, R (-1513267981) 125000000000,
   R (71042525124234897842029324303321451195903657809) 2126764793255865396646091296448551321600000000000,
   R (487535669) 1000000000000, R (68359771) 250000000000, R (50423577031) 100000000000, R (1) 1,
   [R (2467883270391) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 84⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_32/box_000003.json`; sha256 `46bebaa747511fa17121380f8c7a0888131f3cfaac5e95abc1cefd1ca4222739`. -/
def boxTo50_32_003 : MBox :=
  ⟨R (57) 107, R (29) 54, R (6715) 464, R (3907) 232, R (501) 32,
   R (3850513657) 500000000000, R (-10373898399) 1000000000000,
   R (32176184500427111373951032002914115505304066223) 850705917302346158658436518579420528640000000000,
   R (591768989) 500000000000, R (380812141) 1000000000000, R (663236452013) 1000000000000, R (1) 1,
   [R (1855203684779) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 136⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_32/box_000004.json`; sha256 `458f7d3d4f7436542f506da770810a2dae0abdd7d3fd50d8ca8c9d6e25158849`. -/
def boxTo50_32_004 : MBox :=
  ⟨R (57) 107, R (29) 54, R (351) 29, R (6715) 464, R (12331) 928,
   R (277414017) 25000000000, R (-280903657) 31250000000,
   R (773897623465658730491903064776783661209222063359) 17014118346046923173168730371588410572800000000000,
   R (195061001) 125000000000, R (299388383) 500000000000, R (778123536001) 1000000000000, R (1) 1,
   [R (1053949190499) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 60⟩
/-- Lemma 5.4: the exact 5 boxes of To50_32. -/
def boxesTo50_32 : List MBox := [
  boxTo50_32_000,
  boxTo50_32_001,
  boxTo50_32_002,
  boxTo50_32_003,
  boxTo50_32_004
]

/-- Lemma 5.4: the exact cover chains of To50_32. -/
def slabsTo50_32 : List Atlas.Slab := [
  ⟨R (57) 107, R (29) 54, [4, 3, 2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_32 : Rat := R (351) 29

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_32 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
