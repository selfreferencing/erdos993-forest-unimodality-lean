import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_40, subinterval 40

The paper's activity rectangle is [7/5, 57/40], its exact mean
rectangle is [679/57, 50]. The 3 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_40/box_000000.json`; sha256 `452d9ff3c4b914454340a25c5b7c0d30a90089423bc896248b137fea9e55ef4c`. -/
def boxTo50_40_000 : MBox :=
  ⟨R (7) 12, R (57) 97, R (3529) 114, R (50) 1, R (9229) 228,
   R (1274798973) 1000000000000, R (-2436933541) 500000000000,
   R (1443827052364532605655303750736261321925556374281) 42535295865117307932921825928971026432000000000000,
   R (42940709) 200000000000, R (26645403) 500000000000, R (1009771459) 100000000000, R (1) 1,
   [R (171551458391493) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 336⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_40/box_000001.json`; sha256 `6d30eed4ea2eb27805264ba8e00067a0903477f5e28902545b515ca125ba4413`. -/
def boxTo50_40_001 : MBox :=
  ⟨R (7) 12, R (57) 97, R (1629) 76, R (3529) 114, R (11945) 456,
   R (3281855361) 1000000000000, R (-10636882113) 1000000000000,
   R (104976238407330433201850443491115211683727850921) 2126764793255865396646091296448551321600000000000,
   R (36797757) 40000000000, R (77625431) 500000000000, R (0) 1, R (1) 1,
   [R (6021691280633) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 112⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_40/box_000002.json`; sha256 `03517c16f78d6f3dbc0527a206fa3807760782b2e002561aca82ecdf72214bba`. -/
def boxTo50_40_002 : MBox :=
  ⟨R (7) 12, R (57) 97, R (679) 57, R (1629) 76, R (7603) 456,
   R (1247390901) 100000000000, R (-29267898871) 1000000000000,
   R (11392363064961326828342944669662117522173949729) 132922799578491587290380706028034457600000000000,
   R (0) 1, R (4167219) 6250000000, R (83859365501) 1000000000000, R (1) 1,
   [R (505550931899) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 72⟩
/-- Lemma 5.4: the exact 3 boxes of To50_40. -/
def boxesTo50_40 : List MBox := [
  boxTo50_40_000,
  boxTo50_40_001,
  boxTo50_40_002
]

/-- Lemma 5.4: the exact cover chains of To50_40. -/
def slabsTo50_40 : List Atlas.Slab := [
  ⟨R (7) 12, R (57) 97, [2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_40 : Rat := R (679) 57

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_40 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
