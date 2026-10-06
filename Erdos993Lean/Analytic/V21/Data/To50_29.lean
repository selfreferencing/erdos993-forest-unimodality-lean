import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_29, subinterval 29

The paper's activity rectangle is [27/25, 11/10], its exact mean
rectangle is [273/22, 50]. The 8 boxes and
2 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_29/box_000000.json`; sha256 `36e691d5e2805a3784a4b342f94bc286dbef9a2b7d246fec0df4681726348d53`. -/
def boxTo50_29_000 : MBox :=
  ⟨R (27) 52, R (11) 21, R (3573) 88, R (50) 1, R (7973) 176,
   R (670314031) 1000000000000, R (-108852071) 62500000000,
   R (150407565940779565132800963237850978508325258201) 17014118346046923173168730371588410572800000000000,
   R (8060651) 125000000000, R (9140817) 500000000000, R (737807363723) 1000000000000, R (1) 1,
   [R (4682823922375183) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 376⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_29/box_000001.json`; sha256 `75b0c2e5f9c560e91f2ad31d35277e9e00ac1d9498ad6d17b087dcd88cf426b5`. -/
def boxTo50_29_001 : MBox :=
  ⟨R (27) 52, R (11) 21, R (1373) 44, R (3573) 88, R (6319) 176,
   R (165351131) 125000000000, R (-2280479193) 1000000000000,
   R (1106253423853334729787469961838209565327207985239) 85070591730234615865843651857942052864000000000000,
   R (24624799) 1000000000000, R (41734093) 1000000000000, R (389741945623) 500000000000, R (1) 1,
   [R (149488156797149) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 296⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_29/box_000002.json`; sha256 `669b77298de6b969c3cc105dba374a568a561e0bd882b66a50d1ecbe1c6ff01b`. -/
def boxTo50_29_002 : MBox :=
  ⟨R (1139) 2184, R (11) 21, R (1919) 88, R (1373) 44, R (4665) 176,
   R (2919726681) 1000000000000, R (-3708617063) 1000000000000,
   R (3489429509313229991361619897748360296634404479573) 170141183460469231731687303715884105728000000000000,
   R (0) 1, R (20736911) 200000000000, R (782472542707) 1000000000000, R (1) 1,
   [R (505687730891) 50000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 224⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_29/box_000003.json`; sha256 `19b057edf8f0478fdc5101d7350e89a0f00e89b5b983fe04f70d412c5ae38ac4`. -/
def boxTo50_29_003 : MBox :=
  ⟨R (27) 52, R (1139) 2184, R (4665) 176, R (1373) 44, R (10157) 352,
   R (243490261) 125000000000, R (-3529031503) 1000000000000,
   R (5447939393395689158848517894103055494710581872511) 340282366920938463463374607431768211456000000000000,
   R (224348319) 1000000000000, R (70205659) 1000000000000, R (365309023781) 500000000000, R (1) 1,
   [R (22175489606797) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 240⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_29/box_000004.json`; sha256 `f5a127459771935b443022a247bd8ae9cae7d9f4f37e25c14a7a8aa9a2123b61`. -/
def boxTo50_29_004 : MBox :=
  ⟨R (27) 52, R (1139) 2184, R (1919) 88, R (4665) 176, R (773) 32,
   R (374374681) 125000000000, R (-794197791) 200000000000,
   R (86352529040922998112210037911100378553390607793) 4253529586511730793292182592897102643200000000000,
   R (280211681) 1000000000000, R (121676807) 1000000000000, R (192784793993) 250000000000, R (1) 1,
   [R (8636807282097) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 208⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_29/box_000005.json`; sha256 `a2b4a46272629c47e5a1b0fc4d6bbbff560a534c8ba0940a6e64e22e81307143`. -/
def boxTo50_29_005 : MBox :=
  ⟨R (27) 52, R (11) 21, R (3011) 176, R (1919) 88, R (6849) 352,
   R (5578809889) 1000000000000, R (-3074152211) 500000000000,
   R (2473960675960915430641709845723895613560215111973) 85070591730234615865843651857942052864000000000000,
   R (72563979) 500000000000, R (125090333) 500000000000, R (76132953227) 100000000000, R (1) 1,
   [R (71884190053) 20000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 84⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_29/box_000006.json`; sha256 `33eed90efe390e076a466b4f7a24df49ab19674177dd80a77d321823573c333b`. -/
def boxTo50_29_006 : MBox :=
  ⟨R (27) 52, R (11) 21, R (5195) 352, R (3011) 176, R (11217) 704,
   R (1975875213) 250000000000, R (-12380322283) 1000000000000,
   R (367733959532210641259788009676390192512830644083) 10633823966279326983230456482242756608000000000000,
   R (806974579) 1000000000000, R (380969051) 1000000000000, R (120518587939) 200000000000, R (1) 1,
   [R (1707989662469) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 136⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_29/box_000007.json`; sha256 `a4e2d116f3cd48123b6d9aa94f8b7d88cd855444daaef3210d8e2859c253a67f`. -/
def boxTo50_29_007 : MBox :=
  ⟨R (27) 52, R (11) 21, R (273) 22, R (5195) 352, R (9563) 704,
   R (1446611991) 125000000000, R (-53894719) 4000000000,
   R (1844390157743703049036509737736267526974187154447) 42535295865117307932921825928971026432000000000000,
   R (349935373) 500000000000, R (23948583) 40000000000, R (167293621861) 250000000000, R (1) 1,
   [R (1004885934171) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 60⟩
/-- Lemma 5.4: the exact 8 boxes of To50_29. -/
def boxesTo50_29 : List MBox := [
  boxTo50_29_000,
  boxTo50_29_001,
  boxTo50_29_002,
  boxTo50_29_003,
  boxTo50_29_004,
  boxTo50_29_005,
  boxTo50_29_006,
  boxTo50_29_007
]

/-- Lemma 5.4: the exact cover chains of To50_29. -/
def slabsTo50_29 : List Atlas.Slab := [
  ⟨R (27) 52, R (1139) 2184, [7, 6, 5, 4, 3, 1, 0]⟩,
  ⟨R (1139) 2184, R (11) 21, [7, 6, 5, 2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_29 : Rat := R (273) 22

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_29 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
