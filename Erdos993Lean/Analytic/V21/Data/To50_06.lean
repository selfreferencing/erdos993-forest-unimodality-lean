import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_06, subinterval 6

The paper's activity rectangle is [3/5, 13/20], its exact mean
rectangle is [198/13, 50]. The 2 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_06/box_000000.json`; sha256 `9bd0fbaa4045ec2780d0ac850464be94dfd31c32e3dfa3289f146681ea75cc2c`. -/
def boxTo50_06_000 : MBox :=
  ⟨R (3) 8, R (13) 33, R (424) 13, R (50) 1, R (537) 13,
   R (633204999) 1000000000000, R (272723377) 125000000000,
   R (128156073668501492996457551050880790240556072701) 5316911983139663491615228241121378304000000000000,
   R (252892809) 500000000000, R (25461029) 1000000000000, R (1) 1, R (0) 1,
   [R (0) 1, R (1292291173507) 100000000000, R (0) 1, R (0) 1, R (0) 1], 344⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_06/box_000001.json`; sha256 `4f6d64fb6e7357e120e59bde786c5e7c959bf1c8fc6463c0a4939e9fe1513c30`. -/
def boxTo50_06_001 : MBox :=
  ⟨R (3) 8, R (13) 33, R (198) 13, R (424) 13, R (311) 13,
   R (5796006359) 1000000000000, R (14256201763) 1000000000000,
   R (413475398843625240730147322038258061732285700741) 5316911983139663491615228241121378304000000000000,
   R (1146191377) 1000000000000, R (38212407) 200000000000, R (1) 1, R (0) 1,
   [R (928862297367) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 200⟩
/-- Lemma 5.4: the exact 2 boxes of To50_06. -/
def boxesTo50_06 : List MBox := [
  boxTo50_06_000,
  boxTo50_06_001
]

/-- Lemma 5.4: the exact cover chains of To50_06. -/
def slabsTo50_06 : List Atlas.Slab := [
  ⟨R (3) 8, R (13) 33, [1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_06 : Rat := R (198) 13

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_06 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
