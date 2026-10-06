import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_34, subinterval 34

The paper's activity rectangle is [59/50, 6/5], its exact mean
rectangle is [143/12, 50]. The 5 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_34/box_000000.json`; sha256 `70931d1cb28a62b760e5fecfc1f2cf4e5d2818a45949d95793f0fd120eed6eab`. -/
def boxTo50_34_000 : MBox :=
  ⟨R (59) 109, R (6) 11, R (743) 24, R (50) 1, R (1943) 48,
   R (314897207) 250000000000, R (-1158802273) 250000000000,
   R (797893933491227110864979113349253504498225686579) 42535295865117307932921825928971026432000000000000,
   R (0) 1, R (5330247) 125000000000, R (416748205757) 1000000000000, R (1) 1,
   [R (0) 1, R (8979139371523) 100000000000, R (0) 1, R (0) 1, R (0) 1], 336⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_34/box_000001.json`; sha256 `75305e848e87a6da19ffc3ab152a0d9d894af04677353a1fcc12d3419b6ed20e`. -/
def boxTo50_34_001 : MBox :=
  ⟨R (59) 109, R (6) 11, R (343) 16, R (743) 24, R (2515) 96,
   R (846674743) 250000000000, R (-4320005121) 500000000000,
   R (2458700323514595700652934400141534656551631139613) 85070591730234615865843651857942052864000000000000,
   R (0) 1, R (15854101) 125000000000, R (476401446679) 1000000000000, R (1) 1,
   [R (17483219626369) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 224⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_34/box_000002.json`; sha256 `4bd9d16ef161039748ee986819e08f380073b55c6879cc826a8033dc2c794328`. -/
def boxTo50_34_002 : MBox :=
  ⟨R (59) 109, R (6) 11, R (1601) 96, R (343) 16, R (3659) 192,
   R (5409221041) 1000000000000, R (-2035252859) 200000000000,
   R (2975895515890240511206299355167649724168732757719) 85070591730234615865843651857942052864000000000000,
   R (737904059) 1000000000000, R (67915709) 250000000000, R (280988741379) 500000000000, R (1) 1,
   [R (1305009935539) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 84⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_34/box_000003.json`; sha256 `2eeb2842cc13acd0accc97d232b12ff61c57c721434f5b452a0c028736a8df72`. -/
def boxTo50_34_003 : MBox :=
  ⟨R (59) 109, R (6) 11, R (915) 64, R (1601) 96, R (5947) 384,
   R (1449066717) 200000000000, R (-12041630877) 1000000000000,
   R (1674236554168400910839642762341896081035128266787) 42535295865117307932921825928971026432000000000000,
   R (1614776761) 1000000000000, R (468086591) 1000000000000, R (7292074417) 12500000000, R (1) 1,
   [R (247829170367) 200000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 68⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_34/box_000004.json`; sha256 `38a4727f377deea848ce188d9360864953f0d7bcd4d5757ba4350347ffa50347`. -/
def boxTo50_34_004 : MBox :=
  ⟨R (59) 109, R (6) 11, R (143) 12, R (915) 64, R (5033) 384,
   R (1494720931) 125000000000, R (-10028061177) 500000000000,
   R (2232921718723667780490506997014071722298756827531) 42535295865117307932921825928971026432000000000000,
   R (42744297) 25000000000, R (738152263) 1000000000000, R (484729458353) 1000000000000, R (1) 1,
   [R (611590770077) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 60⟩
/-- Lemma 5.4: the exact 5 boxes of To50_34. -/
def boxesTo50_34 : List MBox := [
  boxTo50_34_000,
  boxTo50_34_001,
  boxTo50_34_002,
  boxTo50_34_003,
  boxTo50_34_004
]

/-- Lemma 5.4: the exact cover chains of To50_34. -/
def slabsTo50_34 : List Atlas.Slab := [
  ⟨R (59) 109, R (6) 11, [4, 3, 2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_34 : Rat := R (143) 12

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_34 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
