import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_51, subinterval 51

The paper's activity rectangle is [39/20, 2], its exact mean
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

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_51/box_000000.json`; sha256 `80dcd5835a47cf68e6380c2235a0f2e3a7b1008707587999a8495780143ab2ad`. -/
def boxTo50_51_000 : MBox :=
  ⟨R (39) 59, R (2) 3, R (5137) 164, R (50) 1, R (13337) 328,
   R (137358499) 250000000000, R (-1182889897) 1000000000000,
   R (492966823443548790731156415211084083855873153089) 17014118346046923173168730371588410572800000000000,
   R (413042193) 1000000000000, R (7831267) 250000000000, R (0) 1, R (1) 1,
   [R (0) 1, R (0) 1, R (703357117159) 6250000000, R (0) 1, R (0) 1], 336⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_51/box_000001.json`; sha256 `37de25ada353a8a41076ab05b636c7c575d1a4d0aa964da3b6d3fdb10baee0e7`. -/
def boxTo50_51_001 : MBox :=
  ⟨R (39) 59, R (2) 3, R (7211) 328, R (5137) 164, R (17485) 656,
   R (212053437) 125000000000, R (-3443811111) 1000000000000,
   R (2111150787922615009355352287262553134444603437163) 42535295865117307932921825928971026432000000000000,
   R (161267299) 100000000000, R (49639691) 500000000000, R (0) 1, R (1) 1,
   [R (6708759537679) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 224⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_51/box_000002.json`; sha256 `926306a33004d24f31ed0ccca24f12cad72940bda7ae91ec8f755c97ce0439a2`. -/
def boxTo50_51_002 : MBox :=
  ⟨R (39) 59, R (2) 3, R (1037) 82, R (7211) 328, R (11359) 656,
   R (9973124939) 1000000000000, R (-4301480431) 250000000000,
   R (1374780202675224275629882926922400299886143170941) 10633823966279326983230456482242756608000000000000,
   R (2282048239) 500000000000, R (460410573) 1000000000000, R (0) 1, R (1) 1,
   [R (542237975471) 200000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 76⟩
/-- Lemma 5.4: the exact 3 boxes of To50_51. -/
def boxesTo50_51 : List MBox := [
  boxTo50_51_000,
  boxTo50_51_001,
  boxTo50_51_002
]

/-- Lemma 5.4: the exact cover chains of To50_51. -/
def slabsTo50_51 : List Atlas.Slab := [
  ⟨R (39) 59, R (2) 3, [2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_51 : Rat := R (1037) 82

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_51 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
