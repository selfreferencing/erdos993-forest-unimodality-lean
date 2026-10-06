import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_07, subinterval 7

The paper's activity rectangle is [13/20, 7/10], its exact mean
rectangle is [102/7, 50]. The 2 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_07/box_000000.json`; sha256 `863c0a5b75abb979a135f402c4df651312ab97c84260c1073f1736327681cb1e`. -/
def boxTo50_07_000 : MBox :=
  ⟨R (13) 33, R (7) 17, R (226) 7, R (50) 1, R (288) 7,
   R (897289971) 1000000000000, R (1688072219) 500000000000,
   R (580679556028266535661268343977639194372426874299) 21267647932558653966460912964485513216000000000000,
   R (98997767) 200000000000, R (3059419) 100000000000, R (1) 1, R (0) 1,
   [R (0) 1, R (5750476985283) 250000000000, R (0) 1, R (0) 1, R (0) 1], 344⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_07/box_000001.json`; sha256 `1d333e13eef9d641384821972ca3124168b3b7c5b580875d4a3612322268e732`. -/
def boxTo50_07_001 : MBox :=
  ⟨R (13) 33, R (7) 17, R (102) 7, R (226) 7, R (164) 7,
   R (7228220979) 1000000000000, R (4831137957) 250000000000,
   R (789284245294966210123286389326660739300324787017) 10633823966279326983230456482242756608000000000000,
   R (132991081) 500000000000, R (222796423) 1000000000000, R (1) 1, R (0) 1,
   [R (925617878543) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 100⟩
/-- Lemma 5.4: the exact 2 boxes of To50_07. -/
def boxesTo50_07 : List MBox := [
  boxTo50_07_000,
  boxTo50_07_001
]

/-- Lemma 5.4: the exact cover chains of To50_07. -/
def slabsTo50_07 : List Atlas.Slab := [
  ⟨R (13) 33, R (7) 17, [1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_07 : Rat := R (102) 7

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_07 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
