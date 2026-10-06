import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_10, subinterval 10

The paper's activity rectangle is [39/50, 4/5], its exact mean
rectangle is [27/2, 50]. The 3 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_10/box_000000.json`; sha256 `804d448b8a616501b6709ada2de2087369aefbfe60b24a497d922df0f12e8579`. -/
def boxTo50_10_000 : MBox :=
  ⟨R (39) 89, R (4) 9, R (127) 4, R (50) 1, R (327) 8,
   R (1163586597) 1000000000000, R (202078603) 50000000000,
   R (929144935395173036462760104544160111256746691883) 42535295865117307932921825928971026432000000000000,
   R (120424721) 1000000000000, R (34569841) 1000000000000, R (1) 1, R (405913786353) 1000000000000,
   [R (65422484648431) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 336⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_10/box_000001.json`; sha256 `8b420ecc6c5dc8454d349ed0dc5de302ce0f3c8d57d84d5e23d5f96aa3dc3bde`. -/
def boxTo50_10_001 : MBox :=
  ⟨R (39) 89, R (4) 9, R (181) 8, R (127) 4, R (435) 16,
   R (641265663) 250000000000, R (7973258171) 1000000000000,
   R (1287939250533569302235000722857164739824114384939) 42535295865117307932921825928971026432000000000000,
   R (18531497) 31250000000, R (25279431) 250000000000, R (1) 1, R (165856757871) 500000000000,
   [R (2682684012397) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 232⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_10/box_000002.json`; sha256 `9b1a014f8d10119907404964149cbb3965b5609a4727871aba9ad1a0a6e4492f`. -/
def boxTo50_10_002 : MBox :=
  ⟨R (39) 89, R (4) 9, R (27) 2, R (181) 8, R (289) 16,
   R (8981706909) 1000000000000, R (19488479873) 1000000000000,
   R (1137066168780723558507057128021404957883074790401) 21267647932558653966460912964485513216000000000000,
   R (0) 1, R (289870723) 1000000000000, R (1) 1, R (172145720793) 500000000000,
   [R (1399338299859) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 80⟩
/-- Lemma 5.4: the exact 3 boxes of To50_10. -/
def boxesTo50_10 : List MBox := [
  boxTo50_10_000,
  boxTo50_10_001,
  boxTo50_10_002
]

/-- Lemma 5.4: the exact cover chains of To50_10. -/
def slabsTo50_10 : List Atlas.Slab := [
  ⟨R (39) 89, R (4) 9, [2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_10 : Rat := R (27) 2

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_10 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
