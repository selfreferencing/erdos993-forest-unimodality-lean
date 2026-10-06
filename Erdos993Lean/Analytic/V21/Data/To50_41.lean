import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_41, subinterval 41

The paper's activity rectangle is [57/40, 29/20], its exact mean
rectangle is [343/29, 50]. The 3 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_41/box_000000.json`; sha256 `abe4d40bd4c830821bcfdcb357b3c69ecc788dca98e525bbfb78e79791a59c18`. -/
def boxTo50_41_000 : MBox :=
  ⟨R (57) 97, R (29) 49, R (1793) 58, R (50) 1, R (4693) 116,
   R (603183611) 500000000000, R (-2266269869) 500000000000,
   R (2898736770386364265774693536851333341407059748123) 85070591730234615865843651857942052864000000000000,
   R (260572991) 1000000000000, R (12949019) 250000000000, R (0) 1, R (1) 1,
   [R (390002682236231) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 336⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_41/box_000001.json`; sha256 `40c3a55d5882d02127bd1dcc7713c91106ea664a62f66d3b3992a5a040c0b840`. -/
def boxTo50_41_001 : MBox :=
  ⟨R (57) 97, R (29) 49, R (2479) 116, R (1793) 58, R (6065) 232,
   R (3132606031) 1000000000000, R (-9994882521) 1000000000000,
   R (2111883214092684491643464235098735149915980377663) 42535295865117307932921825928971026432000000000000,
   R (469133187) 500000000000, R (176059253) 1000000000000, R (0) 1, R (1) 1,
   [R (3794747219477) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 112⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_41/box_000002.json`; sha256 `f6d6b2dcd2d76e3a2e8076376abd65ddab3138f3a4d7ce3fe0db5ef6ec1ef2b7`. -/
def boxTo50_41_002 : MBox :=
  ⟨R (57) 97, R (29) 49, R (343) 29, R (2479) 116, R (3851) 232,
   R (253642257) 20000000000, R (-3503189913) 125000000000,
   R (23555067442667639778078205876458396802543546057) 265845599156983174580761412056068915200000000000,
   R (65577991) 1000000000000, R (331185189) 500000000000, R (13559928661) 100000000000, R (1) 1,
   [R (515812439757) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 72⟩
/-- Lemma 5.4: the exact 3 boxes of To50_41. -/
def boxesTo50_41 : List MBox := [
  boxTo50_41_000,
  boxTo50_41_001,
  boxTo50_41_002
]

/-- Lemma 5.4: the exact cover chains of To50_41. -/
def slabsTo50_41 : List Atlas.Slab := [
  ⟨R (57) 97, R (29) 49, [2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_41 : Rat := R (343) 29

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_41 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
