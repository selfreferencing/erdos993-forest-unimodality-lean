import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: Below48, subinterval 48

The paper's activity rectangle is [9/5, 37/20], its exact mean
rectangle is [228/37, 493/38]. The 4 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_hand_caps/subintervals_38_39_43_44_47_to_54_and_bands_24_26_to_29/outputs/stage2/mgf_hand/full/strip_48/box_000000.json`; sha256 `17ad3f52b429e868efce5733791569d414c1494110471916be3c8c2009df491c`. -/
def boxBelow48_000 : MBox :=
  ⟨R (9) 14, R (37) 57, R (12911) 1406, R (493) 38, R (7788) 703,
   R (11357089119) 500000000000, R (-3942629413) 100000000000,
   R (411437742644877442708927359295577876483533145673) 2658455991569831745807614120560689152000000000000,
   R (1166945701) 125000000000, R (1286657887) 1000000000000, R (0) 1, R (1) 1,
   [R (5466838241) 6250000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 52⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_hand_caps/subintervals_38_39_43_44_47_to_54_and_bands_24_26_to_29/outputs/stage2/mgf_hand/full/strip_48/box_000001.json`; sha256 `7f2407949b920552bcec98aaefec83a543c5bfa5fa8402ed3a17e18695468b77`. -/
def boxBelow48_001 : MBox :=
  ⟨R (9) 14, R (37) 57, R (5123) 703, R (12911) 1406, R (23157) 2812,
   R (81536433) 2500000000, R (-13321698987) 250000000000,
   R (435506831991989233871236368578115845833570146321) 2658455991569831745807614120560689152000000000000,
   R (14704352941) 1000000000000, R (1667756261) 1000000000000, R (0) 1, R (1) 1,
   [R (951348354359) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 40⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_hand_caps/subintervals_38_39_43_44_47_to_54_and_bands_24_26_to_29/outputs/stage2/mgf_hand/full/strip_48/box_000002.json`; sha256 `3a881c243980bbdacae0e35deba990fad6e96f463913c30b0e825118865eefb0`. -/
def boxBelow48_002 : MBox :=
  ⟨R (9) 14, R (37) 57, R (17827) 2812, R (5123) 703, R (38319) 5624,
   R (12332977791) 250000000000, R (-14425812803) 200000000000,
   R (513299962537163653641190673299641510503276629071) 2658455991569831745807614120560689152000000000000,
   R (18458233101) 1000000000000, R (265186837) 100000000000, R (0) 1, R (1) 1,
   [R (414423720457) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 64⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_hand_caps/subintervals_38_39_43_44_47_to_54_and_bands_24_26_to_29/outputs/stage2/mgf_hand/full/strip_48/box_000003.json`; sha256 `be743b4a500cc6d61840457e9c690dee6bab9efd695e13d28b494e5e8909abcb`. -/
def boxBelow48_003 : MBox :=
  ⟨R (9) 14, R (37) 57, R (399) 74, R (17827) 2812, R (32989) 5624,
   R (21134054367) 250000000000, R (-100657243807) 1000000000000,
   R (1354940982887145127849297354099493692371804182907) 5316911983139663491615228241121378304000000000000,
   R (7015937807) 500000000000, R (3996650629) 1000000000000, R (0) 1, R (1) 1,
   [R (856925189323) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 28⟩
/-- Lemma 5.4: the exact 4 boxes of Below48. -/
def boxesBelow48 : List MBox := [
  boxBelow48_000,
  boxBelow48_001,
  boxBelow48_002,
  boxBelow48_003
]

/-- Lemma 5.4: the exact cover chains of Below48. -/
def slabsBelow48 : List Atlas.Slab := [
  ⟨R (9) 14, R (37) 57, [3, 2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloBelow48 : Rat := R (228) 37

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiBelow48 : Rat := R (493) 38

end Erdos993Lean.Analytic.V21.Data
