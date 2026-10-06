import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_46, subinterval 46

The paper's activity rectangle is [17/10, 7/4], its exact mean
rectangle is [165/14, 50]. The 3 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_46/box_000000.json`; sha256 `8fef3e6469edbb57c95111e88c7f17612e247b223bde45ccaeaae93e11081ff2`. -/
def boxTo50_46_000 : MBox :=
  ⟨R (17) 27, R (7) 11, R (865) 28, R (50) 1, R (2265) 56,
   R (361841227) 500000000000, R (-2118653713) 1000000000000,
   R (1300118377890129244184612451669644375482569608821) 42535295865117307932921825928971026432000000000000,
   R (280261649) 1000000000000, R (175439) 3906250000, R (0) 1, R (1) 1,
   [R (161287828874071) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 336⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_46/box_000001.json`; sha256 `af47afab6b01be00516a3f762acf01db7cf6d7b8ad8b12e574d0d46f6a10bb7d`. -/
def boxTo50_46_001 : MBox :=
  ⟨R (17) 27, R (7) 11, R (1195) 56, R (865) 28, R (2925) 112,
   R (2339728639) 1000000000000, R (-5962500511) 1000000000000,
   R (570976174266522769975847658804555968032871483277) 10633823966279326983230456482242756608000000000000,
   R (1495943461) 1000000000000, R (8525559) 62500000000, R (0) 1, R (1) 1,
   [R (626315578851) 40000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 224⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_46/box_000002.json`; sha256 `f7740acbea79fa75bcbe5f2558b2e7c15cf5cd91e5fd48c7bc968c014fd4ce02`. -/
def boxTo50_46_002 : MBox :=
  ⟨R (17) 27, R (7) 11, R (165) 14, R (1195) 56, R (265) 16,
   R (3185640653) 250000000000, R (-25209798487) 1000000000000,
   R (1323905010055281797884195788764589124920556389401) 10633823966279326983230456482242756608000000000000,
   R (6932049) 3125000000, R (687689887) 1000000000000, R (0) 1, R (1) 1,
   [R (1779457772437) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 72⟩
/-- Lemma 5.4: the exact 3 boxes of To50_46. -/
def boxesTo50_46 : List MBox := [
  boxTo50_46_000,
  boxTo50_46_001,
  boxTo50_46_002
]

/-- Lemma 5.4: the exact cover chains of To50_46. -/
def slabsTo50_46 : List Atlas.Slab := [
  ⟨R (17) 27, R (7) 11, [2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_46 : Rat := R (165) 14

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_46 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
