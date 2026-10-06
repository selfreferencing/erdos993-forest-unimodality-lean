import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_22, subinterval 22

The paper's activity rectangle is [97/100, 99/100], its exact mean
rectangle is [2587/198, 50]. The 7 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/band14_to50/strip_22/box_000000.json`; sha256 `f274c55bfd1dcec0ff6a373150f3e087235ce0d2781f4df36c02e14fe984a0ba`. -/
def boxTo50_22_000 : MBox :=
  ⟨R (97) 197, R (99) 199, R (32287) 792, R (50) 1, R (71887) 1584,
   R (354041947) 500000000000, R (321860033) 1000000000000,
   R (1340944308926319270365695818287770452853873091883) 170141183460469231731687303715884105728000000000000,
   R (1199503) 100000000000, R (16496477) 1000000000000, R (1) 1, R (956478763431) 1000000000000,
   [R (542383353989007) 125000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 376⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/band14_to50/strip_22/box_000001.json`; sha256 `d725fc5e1e9ac640fd9fbd3842d8d4220fd881ba96985d66e05ee6ceba069a72`. -/
def boxTo50_22_001 : MBox :=
  ⟨R (97) 197, R (99) 199, R (12487) 396, R (32287) 792, R (19087) 528,
   R (128771521) 100000000000, R (-19265731) 1000000000000,
   R (3850842707302916301589027414651879752398947174239) 340282366920938463463374607431768211456000000000000,
   R (0) 1, R (36230691) 1000000000000, R (124501900191) 125000000000, R (1) 1,
   [R (34082083445133) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 304⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/band14_to50/strip_22/box_000002.json`; sha256 `72413f11098367bb36c1cb29d18fc70dc0296394a09964d06fab98b7087312e7`. -/
def boxTo50_22_002 : MBox :=
  ⟨R (97) 197, R (99) 199, R (42635) 1584, R (12487) 396, R (10287) 352,
   R (501949107) 250000000000, R (533279341) 500000000000,
   R (1239478754655196079391121741866058485432299310271) 85070591730234615865843651857942052864000000000000,
   R (25809509) 200000000000, R (60636681) 1000000000000, R (1) 1, R (921440322957) 1000000000000,
   [R (7191186199663) 200000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 248⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/band14_to50/strip_22/box_000003.json`; sha256 `ddc936a8c0df56e888e0500d6cc93eb6400482ca6cb38847e19e715624359fc1`. -/
def boxTo50_22_003 : MBox :=
  ⟨R (97) 197, R (99) 199, R (5887) 264, R (42635) 1584, R (7087) 288,
   R (2920584257) 1000000000000, R (54804031) 250000000000,
   R (3147441296807022218750069207150159166014794136467) 170141183460469231731687303715884105728000000000000,
   R (274865127) 1000000000000, R (26273951) 250000000000, R (1) 1, R (98815152397) 100000000000,
   [R (1807460529607) 200000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 208⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/band14_to50/strip_22/box_000004.json`; sha256 `d56eb2031aea33a4e24f9cf5bbc4805b07a656c80eb4b1a19c028f3b05a74a8f`. -/
def boxTo50_22_004 : MBox :=
  ⟨R (97) 197, R (99) 199, R (28009) 1584, R (5887) 264, R (63331) 3168,
   R (5437154247) 1000000000000, R (1579410457) 1000000000000,
   R (2284256854779982182284112256954854357932217125989) 85070591730234615865843651857942052864000000000000,
   R (0) 1, R (212098967) 1000000000000, R (1) 1, R (938339152777) 1000000000000,
   [R (178757490671) 50000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 168⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/band14_to50/strip_22/box_000005.json`; sha256 `7627672ba0be407bd954e175b8d84ac140dbaaf18395076066e48eae69e31fac`. -/
def boxTo50_22_005 : MBox :=
  ⟨R (97) 197, R (99) 199, R (16235) 1056, R (28009) 1584, R (104723) 6336,
   R (1783960741) 250000000000, R (1329264099) 1000000000000,
   R (16702297001806950516776091832303117209001985433) 531691198313966349161522824112137830400000000000,
   R (807335699) 1000000000000, R (16544033) 50000000000, R (1) 1, R (190603260863) 200000000000,
   [R (1387498381511) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 144⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/band14_to50/strip_22/box_000006.json`; sha256 `0e394f74b70414725fa68167cc92bf6c64e2fa7d40e9ff5f2c4a63bf048dffc8`. -/
def boxTo50_22_006 : MBox :=
  ⟨R (97) 197, R (99) 199, R (2587) 198, R (16235) 1056, R (90097) 6336,
   R (5134393537) 500000000000, R (-12333681) 1000000000000,
   R (674051198114441808777743875393603250472960554181) 17014118346046923173168730371588410572800000000000,
   R (129719043) 125000000000, R (491897281) 1000000000000, R (993859591879) 1000000000000, R (1) 1,
   [R (605326067357) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 64⟩
/-- Lemma 5.4: the exact 7 boxes of To50_22. -/
def boxesTo50_22 : List MBox := [
  boxTo50_22_000,
  boxTo50_22_001,
  boxTo50_22_002,
  boxTo50_22_003,
  boxTo50_22_004,
  boxTo50_22_005,
  boxTo50_22_006
]

/-- Lemma 5.4: the exact cover chains of To50_22. -/
def slabsTo50_22 : List Atlas.Slab := [
  ⟨R (97) 197, R (99) 199, [6, 5, 4, 3, 2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_22 : Rat := R (2587) 198

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_22 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
