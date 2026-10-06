import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_04, subinterval 4

The paper's activity rectangle is [1/2, 11/20], its exact mean
rectangle is [186/11, 50]. The 2 boxes and
2 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_04/box_000000.json`; sha256 `de9c887e9850ebbfb07e2c6215b5b0ed0aa8c0222309cbc26138d6751b64ea39`. -/
def boxTo50_04_000 : MBox :=
  ⟨R (32) 93, R (11) 31, R (186) 11, R (50) 1, R (368) 11,
   R (726323357) 200000000000, R (4316052877) 500000000000,
   R (1792835032306603291074963467014595550081174623077) 21267647932558653966460912964485513216000000000000,
   R (960970529) 1000000000000, R (55519037) 1000000000000, R (1) 1, R (0) 1,
   [R (120383962947) 100000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 280⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_04/box_000001.json`; sha256 `41fc5966a413543ae74c8dc6e6823599e09d71f8ae590c5c52ffe2d583741b35`. -/
def boxTo50_04_001 : MBox :=
  ⟨R (1) 3, R (32) 93, R (186) 11, R (50) 1, R (368) 11,
   R (3522107951) 1000000000000, R (3840072021) 500000000000,
   R (188589627569033431436457495735842449220274048457) 2126764793255865396646091296448551321600000000000,
   R (634403477) 500000000000, R (46034877) 1000000000000, R (1) 1, R (0) 1,
   [R (13572917417) 12500000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 280⟩
/-- Lemma 5.4: the exact 2 boxes of To50_04. -/
def boxesTo50_04 : List MBox := [
  boxTo50_04_000,
  boxTo50_04_001
]

/-- Lemma 5.4: the exact cover chains of To50_04. -/
def slabsTo50_04 : List Atlas.Slab := [
  ⟨R (1) 3, R (32) 93, [1]⟩,
  ⟨R (32) 93, R (11) 31, [0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_04 : Rat := R (186) 11

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_04 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
