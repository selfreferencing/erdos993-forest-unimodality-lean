import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_36, subinterval 36

The paper's activity rectangle is [49/40, 5/4], its exact mean
rectangle is [63/5, 50]. The 4 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_36/box_000000.json`; sha256 `a7393782a25f0147aac843f2ae28a063f599f943d1ef36dea69bd93349d6374d`. -/
def boxTo50_36_000 : MBox :=
  ⟨R (49) 89, R (5) 9, R (313) 10, R (50) 1, R (813) 20,
   R (1502708857) 1000000000000, R (-5794123961) 1000000000000,
   R (522122046263385503055466045280745951856567783193) 21267647932558653966460912964485513216000000000000,
   R (0) 1, R (45669209) 1000000000000, R (259882144261) 1000000000000, R (1) 1,
   [R (0) 1, R (70264832350299) 500000000000, R (0) 1, R (0) 1, R (0) 1], 336⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_36/box_000001.json`; sha256 `68032b729d70b85c4d84419db59ee83a7f816c477af0a906c05c66c11e63398b`. -/
def boxTo50_36_001 : MBox :=
  ⟨R (49) 89, R (5) 9, R (439) 20, R (313) 10, R (213) 8,
   R (2771965453) 1000000000000, R (-8288604317) 1000000000000,
   R (1245204621879727993173414403182255468581281116199) 42535295865117307932921825928971026432000000000000,
   R (57478039) 250000000000, R (693623) 5000000000, R (75850395753) 200000000000, R (1) 1,
   [R (1161323315719) 125000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 224⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_36/box_000002.json`; sha256 `f0820f75bb3e7d3e7127cb8fbfe98f130eb51a81f7383e6f41160703bfcde74b`. -/
def boxTo50_36_002 : MBox :=
  ⟨R (49) 89, R (5) 9, R (691) 40, R (439) 20, R (1569) 80,
   R (4810260601) 1000000000000, R (-2281302393) 200000000000,
   R (781041805971194744967595993733647105379870968927) 21267647932558653966460912964485513216000000000000,
   R (62721917) 62500000000, R (69121807) 250000000000, R (434716580047) 1000000000000, R (1) 1,
   [R (3149417168709) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 84⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_36/box_000003.json`; sha256 `774392d3fc42fcf80e3f30672f3c7eddbd6336eaeed6f3cef822cf08ecbe4497`. -/
def boxTo50_36_003 : MBox :=
  ⟨R (49) 89, R (5) 9, R (63) 5, R (691) 40, R (239) 16,
   R (2474914763) 200000000000, R (-14282326223) 500000000000,
   R (1277909035877619432463337796903951539163754819131) 21267647932558653966460912964485513216000000000000,
   R (52359753) 500000000000, R (613955523) 1000000000000, R (113273780803) 500000000000, R (1) 1,
   [R (114560783697) 62500000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 64⟩
/-- Lemma 5.4: the exact 4 boxes of To50_36. -/
def boxesTo50_36 : List MBox := [
  boxTo50_36_000,
  boxTo50_36_001,
  boxTo50_36_002,
  boxTo50_36_003
]

/-- Lemma 5.4: the exact cover chains of To50_36. -/
def slabsTo50_36 : List Atlas.Slab := [
  ⟨R (49) 89, R (5) 9, [3, 2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_36 : Rat := R (63) 5

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_36 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
