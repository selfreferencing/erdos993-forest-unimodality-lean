import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_02, subinterval 2

The paper's activity rectangle is [2/5, 9/20], its exact mean
rectangle is [58/3, 50]. The 1 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_02/box_000000.json`; sha256 `b686e0b6cd01ac56dd60c5298bf3c65ebfa02ea00ce4148450e5e9116120ced4`. -/
def boxTo50_02_000 : MBox :=
  ⟨R (2) 7, R (9) 29, R (58) 3, R (50) 1, R (104) 3,
   R (1515614117) 1000000000000, R (467411369) 200000000000,
   R (61379306835907658406399107193655655316891526847) 1329227995784915872903807060280344576000000000000,
   R (649262511) 500000000000, R (14368107) 1000000000000, R (1) 1, R (0) 1,
   [R (997437311829) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 576⟩
/-- Lemma 5.4: the exact 1 boxes of To50_02. -/
def boxesTo50_02 : List MBox := [
  boxTo50_02_000
]

/-- Lemma 5.4: the exact cover chains of To50_02. -/
def slabsTo50_02 : List Atlas.Slab := [
  ⟨R (2) 7, R (9) 29, [0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_02 : Rat := R (58) 3

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_02 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
