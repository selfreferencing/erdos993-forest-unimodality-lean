import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_27, subinterval 27

The paper's activity rectangle is [21/20, 107/100], its exact mean
rectangle is [2691/214, 50]. The 7 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_27/box_000000.json`; sha256 `48b8e3fc3a4388fb8d287f59aaec70ed4d735225e89ac5a7231554425a90216e`. -/
def boxTo50_27_000 : MBox :=
  ⟨R (21) 41, R (107) 207, R (34791) 856, R (50) 1, R (77591) 1712,
   R (669386131) 1000000000000, R (-587787797) 500000000000,
   R (1370097124052222452430126282433318138020663917487) 170141183460469231731687303715884105728000000000000,
   R (25915317) 1000000000000, R (567201) 31250000000, R (103996617959) 125000000000, R (1) 1,
   [R (3043046214163377) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 376⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_27/box_000001.json`; sha256 `1a75af3d2e709200458f2179a7222ce9701db572c5a369dbb099f1d79ae20b09`. -/
def boxTo50_27_001 : MBox :=
  ⟨R (21) 41, R (107) 207, R (13391) 428, R (34791) 856, R (61573) 1712,
   R (1300710851) 1000000000000, R (-1263751507) 1000000000000,
   R (63116322037405039764186839379234534491026274673) 5316911983139663491615228241121378304000000000000,
   R (0) 1, R (37696017) 1000000000000, R (11002644699) 12500000000, R (1) 1,
   [R (38681365210787) 200000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 296⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_27/box_000002.json`; sha256 `5eaa33eac833c4669548e515509101493935a719993acc94a0c49795ba3abb7f`. -/
def boxTo50_27_002 : MBox :=
  ⟨R (21) 41, R (107) 207, R (45555) 1712, R (13391) 428, R (99119) 3424,
   R (1968985379) 1000000000000, R (-1377468141) 1000000000000,
   R (1289167983631630262157086183427125850938472541939) 85070591730234615865843651857942052864000000000000,
   R (156048339) 1000000000000, R (34746997) 500000000000, R (898806620927) 1000000000000, R (1) 1,
   [R (17694712054221) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 240⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_27/box_000003.json`; sha256 `b0b786e30d99d7ff3f6d1d8158208b9b2b1a5ef4ba03f2f021b6e868b03971fc`. -/
def boxTo50_27_003 : MBox :=
  ⟨R (21) 41, R (107) 207, R (18773) 856, R (45555) 1712, R (83101) 3424,
   R (3124142903) 1000000000000, R (-4256348261) 1000000000000,
   R (334953770623964644225661502824086287352237979871) 17014118346046923173168730371588410572800000000000,
   R (140779309) 1000000000000, R (116524557) 1000000000000, R (762440205263) 1000000000000, R (1) 1,
   [R (7026239473339) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 208⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_27/box_000004.json`; sha256 `183aa50eabbb7734b0817841dec7d67b54cf5d4eae317b0d93bc0325bafd647a`. -/
def boxTo50_27_004 : MBox :=
  ⟨R (21) 41, R (107) 207, R (29537) 1712, R (18773) 856, R (67083) 3424,
   R (5195329389) 1000000000000, R (-539117839) 250000000000,
   R (4585870437137706331670879800709901618685412998551) 170141183460469231731687303715884105728000000000000,
   R (27252571) 100000000000, R (222257691) 1000000000000, R (18337138891) 20000000000, R (1) 1,
   [R (793911129591) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 168⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_27/box_000005.json`; sha256 `b1af886b85d8b9f84b6d1b331f4885e036a5cbf3f34f52f0c3456761a4f7487f`. -/
def boxTo50_27_005 : MBox :=
  ⟨R (21) 41, R (107) 207, R (51065) 3424, R (29537) 1712, R (110139) 6848,
   R (7804064821) 1000000000000, R (-40747713) 15625000000,
   R (5799971742775604954730467854795616997989493786147) 170141183460469231731687303715884105728000000000000,
   R (377053441) 500000000000, R (395875877) 1000000000000, R (462595431519) 500000000000, R (1) 1,
   [R (299295391883) 200000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 72⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_27/box_000006.json`; sha256 `1b3a5ea18e437994c31ad063950ba5e040398841520efced1a4e9433cc37b49d`. -/
def boxTo50_27_006 : MBox :=
  ⟨R (21) 41, R (107) 207, R (2691) 214, R (51065) 3424, R (94121) 6848,
   R (11273390917) 1000000000000, R (-6024277083) 1000000000000,
   R (453239531823669372387915180106343283818490897243) 10633823966279326983230456482242756608000000000000,
   R (705124217) 1000000000000, R (581468809) 1000000000000, R (423536548341) 500000000000, R (1) 1,
   [R (142703524479) 100000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 60⟩
/-- Lemma 5.4: the exact 7 boxes of To50_27. -/
def boxesTo50_27 : List MBox := [
  boxTo50_27_000,
  boxTo50_27_001,
  boxTo50_27_002,
  boxTo50_27_003,
  boxTo50_27_004,
  boxTo50_27_005,
  boxTo50_27_006
]

/-- Lemma 5.4: the exact cover chains of To50_27. -/
def slabsTo50_27 : List Atlas.Slab := [
  ⟨R (21) 41, R (107) 207, [6, 5, 4, 3, 2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_27 : Rat := R (2691) 214

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_27 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
