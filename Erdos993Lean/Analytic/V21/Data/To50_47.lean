import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_47, subinterval 47

The paper's activity rectangle is [7/4, 9/5], its exact mean
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

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_47/box_000000.json`; sha256 `df4158320a02a1937253460a84484f63aa7e9ab8a617314a78e257f04e041050`. -/
def boxTo50_47_000 : MBox :=
  ⟨R (7) 11, R (9) 14, R (2393) 76, R (50) 1, R (6193) 152,
   R (660357979) 1000000000000, R (-1814031577) 1000000000000,
   R (257015665749195152393646978643850565942048956307) 8507059173023461586584365185794205286400000000000,
   R (410502711) 1000000000000, R (38027633) 1000000000000, R (0) 1, R (1) 1,
   [R (202012604684413) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 336⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_47/box_000001.json`; sha256 `6462fd052954c4384d22f38ed7809f646b15d30ea8b143b719360652657a6a66`. -/
def boxTo50_47_001 : MBox :=
  ⟨R (7) 11, R (9) 14, R (3379) 152, R (2393) 76, R (8165) 304,
   R (1023512917) 500000000000, R (-125138261) 25000000000,
   R (2197972515514937721741480025099538494490850214143) 42535295865117307932921825928971026432000000000000,
   R (758355113) 500000000000, R (119133951) 1000000000000, R (0) 1, R (1) 1,
   [R (17679443265817) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 224⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_47/box_000002.json`; sha256 `35dd9bf13fb1b45944440e8834b2c3703d20bcf90b2d9948933f25fc1407187e`. -/
def boxTo50_47_002 : MBox :=
  ⟨R (7) 11, R (9) 14, R (493) 38, R (3379) 152, R (5351) 304,
   R (1179584749) 125000000000, R (-9482794231) 500000000000,
   R (14885371249386113178816542748128824796713521877) 132922799578491587290380706028034457600000000000,
   R (429094697) 125000000000, R (121651959) 250000000000, R (0) 1, R (1) 1,
   [R (1964101020363) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 76⟩
/-- Lemma 5.4: the exact 3 boxes of To50_47. -/
def boxesTo50_47 : List MBox := [
  boxTo50_47_000,
  boxTo50_47_001,
  boxTo50_47_002
]

/-- Lemma 5.4: the exact cover chains of To50_47. -/
def slabsTo50_47 : List Atlas.Slab := [
  ⟨R (7) 11, R (9) 14, [2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_47 : Rat := R (493) 38

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_47 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
