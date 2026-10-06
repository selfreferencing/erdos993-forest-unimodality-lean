import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_25, subinterval 25

The paper's activity rectangle is [103/100, 26/25], its exact mean
rectangle is [51/4, 50]. The 7 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_25/box_000000.json`; sha256 `8bb3fe03e5c037a213e28cc63872d44f84b901b8fe398eca364868de2a8f23c4`. -/
def boxTo50_25_000 : MBox :=
  ⟨R (103) 203, R (26) 51, R (651) 16, R (50) 1, R (1451) 32,
   R (144142003) 200000000000, R (-151065313) 250000000000,
   R (5546958553804278085015645411129987988449205814983) 680564733841876926926749214863536422912000000000000,
   R (6073899) 500000000000, R (8303673) 500000000000, R (114702662849) 125000000000, R (1) 1,
   [R (4737284011898883) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 376⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_25/box_000001.json`; sha256 `dd04bfaafb017299251295cee7c2a16a868b36d601b7fc58826c742b9c3cfa10`. -/
def boxTo50_25_001 : MBox :=
  ⟨R (103) 203, R (26) 51, R (251) 8, R (651) 16, R (1153) 32,
   R (661925939) 500000000000, R (-787117669) 1000000000000,
   R (2005988186147520746831239521092324352644851465037) 170141183460469231731687303715884105728000000000000,
   R (0) 1, R (37526963) 1000000000000, R (926596230849) 1000000000000, R (1) 1,
   [R (15644550314303) 100000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 304⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_25/box_000002.json`; sha256 `e8d01d5d0a98f30368535269ddecc1d03634676beb87336bae0ea6b0ed8d62e1`. -/
def boxTo50_25_002 : MBox :=
  ⟨R (103) 203, R (26) 51, R (855) 32, R (251) 8, R (1859) 64,
   R (1931731117) 1000000000000, R (-152018353) 200000000000,
   R (4964099808959573673286384555986690497629812968607) 340282366920938463463374607431768211456000000000000,
   R (17838379) 125000000000, R (12662213) 200000000000, R (945414331493) 1000000000000, R (1) 1,
   [R (2771551105811) 62500000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 248⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_25/box_000003.json`; sha256 `7e8c13fd21f1a889d5b5f0c8124432d6b22771afe14c173c08c5bd6c5bafafb9`. -/
def boxTo50_25_003 : MBox :=
  ⟨R (103) 203, R (26) 51, R (353) 16, R (855) 32, R (1561) 64,
   R (150979561) 50000000000, R (-11133131) 25000000000,
   R (13095714518828753095595544068946286335038392557949) 680564733841876926926749214863536422912000000000000,
   R (244429377) 1000000000000, R (112942213) 1000000000000, R (195596325789) 200000000000, R (1) 1,
   [R (210845951) 19531250, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 208⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_25/box_000004.json`; sha256 `f9d9a5a94b04abb4700564c532b99f37e8c6b382e56bf67a6366923e2d81f183`. -/
def boxTo50_25_004 : MBox :=
  ⟨R (103) 203, R (26) 51, R (557) 32, R (353) 16, R (1263) 64,
   R (705568731) 125000000000, R (-544978247) 200000000000,
   R (4712076142297120583005813453677426422156832881067) 170141183460469231731687303715884105728000000000000,
   R (0) 1, R (44577621) 200000000000, R (223633092891) 250000000000, R (1) 1,
   [R (3034541917403) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 168⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_25/box_000005.json`; sha256 `6be85eea35956de18f7ceb65ed03448d887c0f14a6b196b5634a16941e41dfa4`. -/
def boxTo50_25_005 : MBox :=
  ⟨R (103) 203, R (26) 51, R (965) 64, R (557) 32, R (2079) 128,
   R (3907939571) 500000000000, R (-752586717) 500000000000,
   R (2895103559433080442339896725427662094003957297179) 85070591730234615865843651857942052864000000000000,
   R (125573443) 200000000000, R (376957271) 1000000000000, R (191180739317) 200000000000, R (1) 1,
   [R (310109672679) 200000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 72⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_25/box_000006.json`; sha256 `712a3f4043cf27284fa676305959410f3d405b981897097d67cc46becfaa5d32`. -/
def boxTo50_25_006 : MBox :=
  ⟨R (103) 203, R (26) 51, R (51) 4, R (965) 64, R (1781) 128,
   R (674183539) 62500000000, R (-170384763) 1000000000000,
   R (43516710382299260927116656232573880538727543679) 1063382396627932698323045648224275660800000000000,
   R (1127313369) 1000000000000, R (16115277) 31250000000, R (1) 1, R (993987969393) 1000000000000,
   [R (67577331601) 50000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 60⟩
/-- Lemma 5.4: the exact 7 boxes of To50_25. -/
def boxesTo50_25 : List MBox := [
  boxTo50_25_000,
  boxTo50_25_001,
  boxTo50_25_002,
  boxTo50_25_003,
  boxTo50_25_004,
  boxTo50_25_005,
  boxTo50_25_006
]

/-- Lemma 5.4: the exact cover chains of To50_25. -/
def slabsTo50_25 : List Atlas.Slab := [
  ⟨R (103) 203, R (26) 51, [6, 5, 4, 3, 2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_25 : Rat := R (51) 4

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_25 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
