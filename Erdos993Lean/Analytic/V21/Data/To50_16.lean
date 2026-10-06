import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_16, subinterval 16

The paper's activity rectangle is [89/100, 91/100], its exact mean
rectangle is [312/23, 50]. The 4 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_16/box_000000.json`; sha256 `07a0006acc4b6a7f969e56696442678c7bca044f7f418e711cb4e7d3993df27d`. -/
def boxTo50_16_000 : MBox :=
  ⟨R (89) 189, R (91) 191, R (731) 23, R (50) 1, R (1881) 46,
   R (1153548249) 1000000000000, R (728864809) 200000000000,
   R (1118781316437996128582282193177718294499693223563) 85070591730234615865843651857942052864000000000000,
   R (0) 1, R (3603043) 125000000000, R (1) 1, R (291516348253) 500000000000,
   [R (55776260444771) 200000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 336⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_16/box_000001.json`; sha256 `2aab8d3a3f4bf208121daf2d70ef316203305177447154a5b443b4a6dc6c9cbb`. -/
def boxTo50_16_001 : MBox :=
  ⟨R (89) 189, R (91) 191, R (1043) 46, R (731) 23, R (2505) 92,
   R (519010639) 200000000000, R (3486358931) 1000000000000,
   R (1667033978602138277011610145287067338661538168529) 85070591730234615865843651857942052864000000000000,
   R (158703) 20000000000, R (2919357) 31250000000, R (1) 1, R (779047318589) 1000000000000,
   [R (1476888849111) 200000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 232⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_16/box_000002.json`; sha256 `272911b5c23dfba46a8620d458f5a47ea56c4b0a6ede8e81c947acce270c5ea4`. -/
def boxTo50_16_002 : MBox :=
  ⟨R (89) 189, R (91) 191, R (1667) 92, R (1043) 46, R (3753) 184,
   R (1242838893) 250000000000, R (4330502511) 500000000000,
   R (1201751298738446025023849483937425704468113123863) 42535295865117307932921825928971026432000000000000,
   R (60079721) 250000000000, R (3387443) 15625000000, R (1) 1, R (627029859231) 1000000000000,
   [R (2025991278673) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 176⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_16/box_000003.json`; sha256 `00e31588944729ea3d1675156c9a00c933dc2cba24836e362c698bb41b7b5c20`. -/
def boxTo50_16_003 : MBox :=
  ⟨R (89) 189, R (91) 191, R (312) 23, R (1667) 92, R (2915) 184,
   R (4504437203) 500000000000, R (166289051) 15625000000,
   R (829483413196429623045473907980261620603153650353) 21267647932558653966460912964485513216000000000000,
   R (0) 1, R (80424919) 200000000000, R (1) 1, R (27694837551) 40000000000,
   [R (275272893179) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 68⟩
/-- Lemma 5.4: the exact 4 boxes of To50_16. -/
def boxesTo50_16 : List MBox := [
  boxTo50_16_000,
  boxTo50_16_001,
  boxTo50_16_002,
  boxTo50_16_003
]

/-- Lemma 5.4: the exact cover chains of To50_16. -/
def slabsTo50_16 : List Atlas.Slab := [
  ⟨R (89) 189, R (91) 191, [3, 2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_16 : Rat := R (312) 23

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_16 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
