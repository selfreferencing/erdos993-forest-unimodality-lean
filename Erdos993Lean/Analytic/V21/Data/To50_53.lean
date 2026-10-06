import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_53, subinterval 53

The paper's activity rectangle is [41/20, 9/4], its exact mean
rectangle is [221/18, 50]. The 3 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_53/box_000000.json`; sha256 `c6efa14f7842d5baa43633d308f2b6a64ce4e0b4109e9d7e1c8da28096286851`. -/
def boxTo50_53_000 : MBox :=
  ⟨R (41) 61, R (9) 13, R (1121) 36, R (50) 1, R (2921) 72,
   R (272651401) 500000000000, R (-234047569) 250000000000,
   R (584993366443470057296446759786068658737388708661) 21267647932558653966460912964485513216000000000000,
   R (444769601) 1000000000000, R (31231483) 1000000000000, R (0) 1, R (1) 1,
   [R (0) 1, R (0) 1, R (48184035101331) 1000000000000, R (0) 1, R (0) 1], 336⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_53/box_000001.json`; sha256 `2d3154cf00b5f898e3f9c95704a43f9c19cf83c753f3b36310ebdf0f62565b07`. -/
def boxTo50_53_001 : MBox :=
  ⟨R (41) 61, R (9) 13, R (521) 24, R (1121) 36, R (3805) 144,
   R (897134981) 500000000000, R (-3071069717) 1000000000000,
   R (540719240357922451998164610171169128314785409379) 10633823966279326983230456482242756608000000000000,
   R (1578004081) 1000000000000, R (59996181) 500000000000, R (0) 1, R (1) 1,
   [R (6222114876247) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 224⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_53/box_000002.json`; sha256 `91bcce555817a046468fbe85ed167b1c1176ae0c168ade6e03f4b48e3fe513bc`. -/
def boxTo50_53_002 : MBox :=
  ⟨R (41) 61, R (9) 13, R (221) 18, R (521) 24, R (2447) 144,
   R (6320148417) 500000000000, R (-9622735967) 500000000000,
   R (3159999962058899628852780913679309329368098463) 20769187434139310514121985316880384000000000000,
   R (4560095481) 1000000000000, R (348151137) 500000000000, R (0) 1, R (1) 1,
   [R (1119627826289) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 72⟩
/-- Lemma 5.4: the exact 3 boxes of To50_53. -/
def boxesTo50_53 : List MBox := [
  boxTo50_53_000,
  boxTo50_53_001,
  boxTo50_53_002
]

/-- Lemma 5.4: the exact cover chains of To50_53. -/
def slabsTo50_53 : List Atlas.Slab := [
  ⟨R (41) 61, R (9) 13, [2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_53 : Rat := R (221) 18

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_53 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
