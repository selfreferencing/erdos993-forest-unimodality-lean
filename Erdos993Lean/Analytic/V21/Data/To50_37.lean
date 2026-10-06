import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_37, subinterval 37

The paper's activity rectangle is [5/4, 13/10], its exact mean
rectangle is [161/13, 50]. The 4 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_37/box_000000.json`; sha256 `1dc9483f06723fca45aedb2d4b48565f55e7fbfd92d2b446a86fca63bdc3b94b`. -/
def boxTo50_37_000 : MBox :=
  ⟨R (5) 9, R (13) 23, R (811) 26, R (50) 1, R (2111) 52,
   R (614399139) 500000000000, R (-1242553173) 250000000000,
   R (479099814933019955592384393411470788116188932779) 21267647932558653966460912964485513216000000000000,
   R (0) 1, R (48929329) 1000000000000, R (112787382121) 500000000000, R (1) 1,
   [R (363980047226333) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 336⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_37/box_000001.json`; sha256 `fba3bbee72a8f8315220ff742e4fa011d59fcc74f62886a29030194d8f664b43`. -/
def boxTo50_37_001 : MBox :=
  ⟨R (5) 9, R (13) 23, R (1133) 52, R (811) 26, R (2755) 104,
   R (3212654029) 1000000000000, R (-4437989569) 500000000000,
   R (180148230761693392541482881718837067783450463369) 5316911983139663491615228241121378304000000000000,
   R (251275443) 1000000000000, R (143374359) 1000000000000, R (186953916347) 500000000000, R (1) 1,
   [R (595008269729) 50000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 224⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_37/box_000002.json`; sha256 `e573aea2bc2106a36b55913afe69bc3430baf78c09c308406836edbd6a95dd0b`. -/
def boxTo50_37_002 : MBox :=
  ⟨R (5) 9, R (13) 23, R (1777) 104, R (1133) 52, R (311) 16,
   R (3013224211) 500000000000, R (-3630985103) 200000000000,
   R (970636203829296470753093565786631375105963009419) 21267647932558653966460912964485513216000000000000,
   R (1134761619) 1000000000000, R (159749269) 500000000000, R (58042934451) 500000000000, R (1) 1,
   [R (4695051916961) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 84⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_37/box_000003.json`; sha256 `8a008ae62fbebb892072d61cfc167d49354447f052282351004a84a690371317`. -/
def boxTo50_37_003 : MBox :=
  ⟨R (5) 9, R (13) 23, R (161) 13, R (1777) 104, R (3065) 208,
   R (12792660567) 1000000000000, R (-17181932477) 500000000000,
   R (692194108712142651161194844002900356965690451027) 10633823966279326983230456482242756608000000000000,
   R (282418561) 250000000000, R (176833221) 250000000000, R (6536963523) 500000000000, R (1) 1,
   [R (268020314081) 200000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 64⟩
/-- Lemma 5.4: the exact 4 boxes of To50_37. -/
def boxesTo50_37 : List MBox := [
  boxTo50_37_000,
  boxTo50_37_001,
  boxTo50_37_002,
  boxTo50_37_003
]

/-- Lemma 5.4: the exact cover chains of To50_37. -/
def slabsTo50_37 : List Atlas.Slab := [
  ⟨R (5) 9, R (13) 23, [3, 2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_37 : Rat := R (161) 13

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_37 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
