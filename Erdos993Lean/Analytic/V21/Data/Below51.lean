import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: Below51, subinterval 51

The paper's activity rectangle is [39/20, 2], its exact mean
rectangle is [6, 1037/82]. The 4 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `atlas_mgf/rung_21/strip_51/box_000000.json`; sha256 `f8727c2d9971bce474fa7816be6bb8c7a2d9cf09ecd58cb61b4d338d98f7f865`. -/
def boxBelow51_000 : MBox :=
  ⟨R (39) 59, R (2) 3, R (9) 1, R (45) 4, R (81) 8,
   R (6179794979) 250000000000, R (-593853557) 15625000000,
   R (3662044718158535067407784014248652680630498623981) 21267647932558653966460912964485513216000000000000,
   R (11948181773) 1000000000000, R (806839813) 500000000000, R (0) 1, R (1) 1,
   [R (914182425193) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 48⟩
/-- Exact source `atlas_mgf/rung_21/strip_51/box_000001.json`; sha256 `db88e7be232a85246f67d8d4a0241b58acba1f9ab4e202d1659ebf606788fbf3`. -/
def boxBelow51_001 : MBox :=
  ⟨R (39) 59, R (2) 3, R (27) 4, R (9) 1, R (63) 8,
   R (11211425009) 250000000000, R (-30170735721) 500000000000,
   R (2314268880523629635583098996139086852442829348347) 10633823966279326983230456482242756608000000000000,
   R (1045858779) 62500000000, R (2856848257) 1000000000000, R (0) 1, R (1) 1,
   [R (404320511529) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 36⟩
/-- Exact source `atlas_mgf/rung_21/strip_51/box_000002.json`; sha256 `fd16f29dc332c140432c48880052aba502b85c0c1e3fae9cbf389c0dd50cc0f9`. -/
def boxBelow51_002 : MBox :=
  ⟨R (39) 59, R (2) 3, R (6) 1, R (27) 4, R (51) 8,
   R (2961381627) 50000000000, R (-37276087931) 500000000000,
   R (2409627443362973698190552058811553785618623621603) 10633823966279326983230456482242756608000000000000,
   R (2720516723) 125000000000, R (42552083) 12500000000, R (0) 1, R (1) 1,
   [R (820947738137) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 32⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_hand_caps/subintervals_38_39_43_44_47_to_54_and_bands_24_26_to_29/outputs/stage2/mgf_hand/ext/strip_51/box_000000.json`; sha256 `b38145937931b63e036f223202f406f2a8c74cb0681f787d7548f412f4e01655`. -/
def boxBelow51_003 : MBox :=
  ⟨R (39) 59, R (2) 3, R (45) 4, R (1037) 82, R (3919) 328,
   R (6048224569) 500000000000, R (-10093848917) 500000000000,
   R (1228262811388485045409888418439892510288750214993) 10633823966279326983230456482242756608000000000000,
   R (237274383) 25000000000, R (514262519) 500000000000, R (0) 1, R (1) 1,
   [R (218200286993) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 52⟩
/-- Lemma 5.4: the exact 4 boxes of Below51. -/
def boxesBelow51 : List MBox := [
  boxBelow51_000,
  boxBelow51_001,
  boxBelow51_002,
  boxBelow51_003
]

/-- Lemma 5.4: the exact cover chains of Below51. -/
def slabsBelow51 : List Atlas.Slab := [
  ⟨R (39) 59, R (2) 3, [2, 1, 0, 3]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloBelow51 : Rat := R (6) 1

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiBelow51 : Rat := R (1037) 82

end Erdos993Lean.Analytic.V21.Data
