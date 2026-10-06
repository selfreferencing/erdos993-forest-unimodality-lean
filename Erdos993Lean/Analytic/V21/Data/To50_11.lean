import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_11, subinterval 11

The paper's activity rectangle is [4/5, 21/25], its exact mean
rectangle is [92/7, 50]. The 4 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_11/box_000000.json`; sha256 `5f8005a78567837ae174cf2382fcab172d69ae362e3ef0e1609dde530eef908a`. -/
def boxTo50_11_000 : MBox :=
  ⟨R (4) 9, R (21) 46, R (221) 7, R (50) 1, R (571) 14,
   R (80267927) 62500000000, R (2453946757) 500000000000,
   R (417005560244545731711695195187905276891377815077) 21267647932558653966460912964485513216000000000000,
   R (51423379) 1000000000000, R (9298647) 250000000000, R (1) 1, R (34495917789) 100000000000,
   [R (108009354010893) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 336⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_11/box_000001.json`; sha256 `a818771cf1decb61d67189bd08ad722b7f7f123570a17a0a5653c6ee8d5d649e`. -/
def boxTo50_11_001 : MBox :=
  ⟨R (4) 9, R (21) 46, R (313) 14, R (221) 7, R (755) 28,
   R (2835329809) 1000000000000, R (7224999939) 1000000000000,
   R (113565664579758447496202207486698885107348301649) 4253529586511730793292182592897102643200000000000,
   R (67781727) 250000000000, R (102096201) 1000000000000, R (1) 1, R (494871441329) 1000000000000,
   [R (2461405704293) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 224⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_11/box_000002.json`; sha256 `df75edd81bdb17c27fb6b476afda21f55e82b52ca308bc178b3c4bfb2b37ce67`. -/
def boxTo50_11_002 : MBox :=
  ⟨R (4) 9, R (21) 46, R (71) 4, R (313) 14, R (1123) 56,
   R (817831833) 200000000000, R (4719074711) 500000000000,
   R (2481427142405671147528445629206063027482656891) 83076749736557242056487941267521536000000000000,
   R (1164145167) 1000000000000, R (49905103) 250000000000, R (1) 1, R (98511543169) 200000000000,
   [R (339734392679) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 176⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_11/box_000003.json`; sha256 `59122dc7cbc7e62eda5a297fd92b97d1810fa433a22421cc883a14953e36ab53`. -/
def boxTo50_11_003 : MBox :=
  ⟨R (4) 9, R (21) 46, R (92) 7, R (71) 4, R (865) 56,
   R (1295921337) 125000000000, R (22201644561) 1000000000000,
   R (268939621126606271073991913717829605219610388867) 5316911983139663491615228241121378304000000000000,
   R (355245583) 1000000000000, R (53826697) 125000000000, R (1) 1, R (348484411397) 1000000000000,
   [R (126095533621) 100000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 68⟩
/-- Lemma 5.4: the exact 4 boxes of To50_11. -/
def boxesTo50_11 : List MBox := [
  boxTo50_11_000,
  boxTo50_11_001,
  boxTo50_11_002,
  boxTo50_11_003
]

/-- Lemma 5.4: the exact cover chains of To50_11. -/
def slabsTo50_11 : List Atlas.Slab := [
  ⟨R (4) 9, R (21) 46, [3, 2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_11 : Rat := R (92) 7

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_11 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
