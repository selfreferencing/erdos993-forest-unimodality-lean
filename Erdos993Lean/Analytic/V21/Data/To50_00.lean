import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_00, subinterval 0

The paper's activity rectangle is [1/3, 9/25], its exact mean
rectangle is [68/3, 50]. The 1 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_00/box_000000.json`; sha256 `3651a8ee3de7e642eac082bbb35aba4fa2df1aa03074f8d67434ecdc01597b21`. -/
def boxTo50_00_000 : MBox :=
  ⟨R (1) 4, R (9) 34, R (68) 3, R (50) 1, R (109) 3,
   R (635966683) 1000000000000, R (371126287) 1000000000000,
   R (16146629389) 500000000000,
   R (300158213) 500000000000, R (11905457) 1000000000000, R (1) 1, R (0) 1,
   [R (62966170553) 62500000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 608⟩
/-- Lemma 5.4: the exact 1 boxes of To50_00. -/
def boxesTo50_00 : List MBox := [
  boxTo50_00_000
]

/-- Lemma 5.4: the exact cover chains of To50_00. -/
def slabsTo50_00 : List Atlas.Slab := [
  ⟨R (1) 4, R (9) 34, [0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_00 : Rat := R (68) 3

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_00 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
