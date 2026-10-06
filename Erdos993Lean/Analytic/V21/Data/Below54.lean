import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: Below54, subinterval 54

The paper's activity rectangle is [9/4, 7/3], its exact mean
rectangle is [40/7, 90/7]. The 4 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `atlas_mgf/rung_21/strip_54/box_000000.json`; sha256 `b0c37b9d4bf6c54be5181a3ee737f86da68d4a62a5649e689597f8d7160dc427`. -/
def boxBelow54_000 : MBox :=
  ⟨R (9) 13, R (7) 10, R (50) 7, R (75) 7, R (125) 14,
   R (42389081437) 1000000000000, R (-11815533707) 250000000000,
   R (1347248974966046127764446838177300520049510461201) 5316911983139663491615228241121378304000000000000,
   R (7979315529) 500000000000, R (73861637) 25000000000, R (0) 1, R (1) 1,
   [R (396255294911) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 40⟩
/-- Exact source `atlas_mgf/rung_21/strip_54/box_000001.json`; sha256 `303c635659484b00fc653326bcca805edd7aad350e56b5d2692fe7dc24e09aa2`. -/
def boxBelow54_001 : MBox :=
  ⟨R (9) 13, R (7) 10, R (45) 7, R (50) 7, R (95) 14,
   R (429025479) 10000000000, R (-47616311943) 1000000000000,
   R (1102676674785012149590486118259951172804425930897) 5316911983139663491615228241121378304000000000000,
   R (28617539823) 1000000000000, R (371190557) 125000000000, R (0) 1, R (1) 1,
   [R (792816644637) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 64⟩
/-- Exact source `atlas_mgf/rung_21/strip_54/box_000002.json`; sha256 `9cc7cd22f10335a7f254f025b1cbc3f8449f0fa5aac5b06a5109e0a412c8abea`. -/
def boxBelow54_002 : MBox :=
  ⟨R (9) 13, R (7) 10, R (40) 7, R (45) 7, R (85) 14,
   R (36056069823) 500000000000, R (-13446338503) 200000000000,
   R (749243065767118287055671634032522610289465541173) 2658455991569831745807614120560689152000000000000,
   R (29002229637) 1000000000000, R (73574493) 15625000000, R (0) 1, R (1) 1,
   [R (200276210313) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 32⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_hand_caps/subintervals_38_39_43_44_47_to_54_and_bands_24_26_to_29/outputs/stage2/mgf_hand/ext/strip_54/box_000000.json`; sha256 `60d9a8db20c46ce6efbcfbf4776ee1a3fa660316e63f4316127bf4a3e6ae8818`. -/
def boxBelow54_003 : MBox :=
  ⟨R (9) 13, R (7) 10, R (75) 7, R (90) 7, R (165) 14,
   R (7248818113) 500000000000, R (-2418274021) 125000000000,
   R (775199002808103255443809323942945487348545811233) 5316911983139663491615228241121378304000000000000,
   R (570813457) 50000000000, R (499069331) 500000000000, R (0) 1, R (1) 1,
   [R (68519291721) 62500000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 52⟩
/-- Lemma 5.4: the exact 4 boxes of Below54. -/
def boxesBelow54 : List MBox := [
  boxBelow54_000,
  boxBelow54_001,
  boxBelow54_002,
  boxBelow54_003
]

/-- Lemma 5.4: the exact cover chains of Below54. -/
def slabsBelow54 : List Atlas.Slab := [
  ⟨R (9) 13, R (7) 10, [2, 1, 0, 3]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloBelow54 : Rat := R (40) 7

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiBelow54 : Rat := R (90) 7

end Erdos993Lean.Analytic.V21.Data
