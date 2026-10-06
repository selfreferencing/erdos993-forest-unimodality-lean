import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_48, subinterval 48

The paper's activity rectangle is [9/5, 37/20], its exact mean
rectangle is [493/38, 50]. The 3 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_48/box_000000.json`; sha256 `950381ce552cd9f29faf74aedd9aeb7397dbfc16dbb26b1049bdced789267bfd`. -/
def boxTo50_48_000 : MBox :=
  ⟨R (9) 14, R (37) 57, R (2393) 76, R (50) 1, R (6193) 152,
   R (12792857) 20000000000, R (-821947633) 500000000000,
   R (1301255618668072589457719043600291647729301448207) 42535295865117307932921825928971026432000000000000,
   R (465152531) 1000000000000, R (17490721) 500000000000, R (0) 1, R (1) 1,
   [R (488031421241053) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 336⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_48/box_000001.json`; sha256 `b2c95bbd98e943d1ede831da91a69ae5a46ebb30d614d277996e306eec1ec594`. -/
def boxTo50_48_001 : MBox :=
  ⟨R (9) 14, R (37) 57, R (3379) 152, R (2393) 76, R (8165) 304,
   R (1975907653) 1000000000000, R (-2276857719) 500000000000,
   R (34547807889155671060320085094392862217613826487) 664613997892457936451903530140172288000000000000,
   R (33105319) 20000000000, R (54284999) 500000000000, R (0) 1, R (1) 1,
   [R (10028773190339) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 224⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_48/box_000002.json`; sha256 `e540f3b60ab370a2f3790f00cb2db8c64ca492287f47df7a087a7d54947cd41a`. -/
def boxTo50_48_002 : MBox :=
  ⟨R (9) 14, R (37) 57, R (493) 38, R (3379) 152, R (5351) 304,
   R (2117243549) 250000000000, R (-1655714951) 100000000000,
   R (1153910887656490404815516040136354091040026616057) 10633823966279326983230456482242756608000000000000,
   R (890623307) 250000000000, R (483840909) 1000000000000, R (0) 1, R (1) 1,
   [R (501684737791) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 76⟩
/-- Lemma 5.4: the exact 3 boxes of To50_48. -/
def boxesTo50_48 : List MBox := [
  boxTo50_48_000,
  boxTo50_48_001,
  boxTo50_48_002
]

/-- Lemma 5.4: the exact cover chains of To50_48. -/
def slabsTo50_48 : List Atlas.Slab := [
  ⟨R (9) 14, R (37) 57, [2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_48 : Rat := R (493) 38

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_48 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
