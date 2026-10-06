import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_01, subinterval 1

The paper's activity rectangle is [9/25, 2/5], its exact mean
rectangle is [21, 50]. The 1 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_01/box_000000.json`; sha256 `291f9a93b0eb340e0a47db9d58473165ed460c20cd4bcf705adb2c30b495a729`. -/
def boxTo50_01_000 : MBox :=
  ⟨R (9) 34, R (2) 7, R (21) 1, R (50) 1, R (71) 2,
   R (178182791) 200000000000, R (884677243) 1000000000000,
   R (213895165305634247325896807088178045734033241469) 5316911983139663491615228241121378304000000000000,
   R (958989) 976562500, R (3256507) 250000000000, R (1) 1, R (0) 1,
   [R (499547434961) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 592⟩
/-- Lemma 5.4: the exact 1 boxes of To50_01. -/
def boxesTo50_01 : List MBox := [
  boxTo50_01_000
]

/-- Lemma 5.4: the exact cover chains of To50_01. -/
def slabsTo50_01 : List Atlas.Slab := [
  ⟨R (9) 34, R (2) 7, [0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_01 : Rat := R (21) 1

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_01 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
