import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_33, subinterval 33

The paper's activity rectangle is [29/25, 59/50], its exact mean
rectangle is [1417/118, 50]. The 5 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_33/box_000000.json`; sha256 `337c10951eee13ff891676a250725ee3d1a42ab0492e680aff7eca5b3483a9e8`. -/
def boxTo50_33_000 : MBox :=
  ⟨R (29) 54, R (59) 109, R (7317) 236, R (50) 1, R (19117) 472,
   R (148780399) 125000000000, R (-123230509) 31250000000,
   R (709084984252041466144261825930310045989548088309) 42535295865117307932921825928971026432000000000000,
   R (0) 1, R (37114191) 1000000000000, R (259291422321) 500000000000, R (1) 1,
   [R (0) 1, R (40506658878467) 200000000000, R (0) 1, R (0) 1, R (0) 1], 336⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_33/box_000001.json`; sha256 `680e6887a7bbd6aa187979e00826ac8631e7c12df2eaa0311671e858568b80e0`. -/
def boxTo50_33_001 : MBox :=
  ⟨R (29) 54, R (59) 109, R (10151) 472, R (7317) 236, R (24785) 944,
   R (660427117) 200000000000, R (-9179525623) 1000000000000,
   R (1155494533609585867438320201175143388725795714871) 42535295865117307932921825928971026432000000000000,
   R (0) 1, R (31805659) 250000000000, R (436507098141) 1000000000000, R (1) 1,
   [R (17217153074379) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 224⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_33/box_000002.json`; sha256 `28c82b845f568352a8fac3909690c94718cedca7c3d8b7c0395dec6017d8781e`. -/
def boxTo50_33_002 : MBox :=
  ⟨R (29) 54, R (59) 109, R (15819) 944, R (10151) 472, R (36121) 1888,
   R (5651522911) 1000000000000, R (-11079724199) 1000000000000,
   R (2939880325796389590270789439821382651602413747417) 85070591730234615865843651857942052864000000000000,
   R (156063249) 250000000000, R (66807479) 250000000000, R (67559658149) 125000000000, R (1) 1,
   [R (258830257067) 100000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 84⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_33/box_000003.json`; sha256 `a6d2afb48efc31a237eb432936ee6342bf2ede841797469ea72d220591152f49`. -/
def boxTo50_33_003 : MBox :=
  ⟨R (29) 54, R (59) 109, R (27155) 1888, R (15819) 944, R (58793) 3776,
   R (1480634283) 200000000000, R (-11036664143) 1000000000000,
   R (403539066102857154728280749523190048185783783873) 10633823966279326983230456482242756608000000000000,
   R (312089187) 200000000000, R (105820851) 250000000000, R (62582977977) 100000000000, R (1) 1,
   [R (1250559938693) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 68⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_33/box_000004.json`; sha256 `0a1532ffb3f0803a48025af4b752c437ceb3c74c162df64e2fbe8dacde4c2178`. -/
def boxTo50_33_004 : MBox :=
  ⟨R (29) 54, R (59) 109, R (1417) 118, R (27155) 1888, R (49827) 3776,
   R (12726930767) 1000000000000, R (-17279574263) 1000000000000,
   R (2244452615057097509885393715288198321155440349311) 42535295865117307932921825928971026432000000000000,
   R (468993949) 500000000000, R (763644957) 1000000000000, R (292011700139) 500000000000, R (1) 1,
   [R (1116963269623) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 60⟩
/-- Lemma 5.4: the exact 5 boxes of To50_33. -/
def boxesTo50_33 : List MBox := [
  boxTo50_33_000,
  boxTo50_33_001,
  boxTo50_33_002,
  boxTo50_33_003,
  boxTo50_33_004
]

/-- Lemma 5.4: the exact cover chains of To50_33. -/
def slabsTo50_33 : List Atlas.Slab := [
  ⟨R (29) 54, R (59) 109, [4, 3, 2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_33 : Rat := R (1417) 118

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_33 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
