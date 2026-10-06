import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: Below50, subinterval 50

The paper's activity rectangle is [19/10, 39/20], its exact mean
rectangle is [236/39, 1037/82]. The 4 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `atlas_mgf/rung_21/strip_50/box_000000.json`; sha256 `aee910d18cd03057a4adedfb4f7bee6e45298ca0218fa88733ef4e82e8685aa0`. -/
def boxBelow50_000 : MBox :=
  ⟨R (19) 29, R (39) 59, R (118) 13, R (295) 26, R (531) 52,
   R (23788771517) 1000000000000, R (-1522304843) 40000000000,
   R (3506823945869206838687667247535492163051283895251) 21267647932558653966460912964485513216000000000000,
   R (11221208999) 1000000000000, R (410175979) 250000000000, R (0) 1, R (1) 1,
   [R (433566421561) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 48⟩
/-- Exact source `atlas_mgf/rung_21/strip_50/box_000001.json`; sha256 `b62644c9934f0c39c290d860f2254bc4f5edac8259a882ad53c0d5a861668efe`. -/
def boxBelow50_001 : MBox :=
  ⟨R (19) 29, R (39) 59, R (177) 26, R (118) 13, R (413) 52,
   R (10150067689) 250000000000, R (-58093172523) 1000000000000,
   R (2146131250039210199557871614144967404666765762607) 10633823966279326983230456482242756608000000000000,
   R (2021450491) 125000000000, R (543477787) 200000000000, R (0) 1, R (1) 1,
   [R (404079107633) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 36⟩
/-- Exact source `atlas_mgf/rung_21/strip_50/box_000002.json`; sha256 `33a3fdb341e1d9b3ba3582fd026d6d185ad87a2d629b83ff5b321147ab74ed1b`. -/
def boxBelow50_002 : MBox :=
  ⟨R (19) 29, R (39) 59, R (413) 78, R (177) 26, R (236) 39,
   R (44068842857) 500000000000, R (-24275325641) 250000000000,
   R (2936358482640732532453741243039419032588119673997) 10633823966279326983230456482242756608000000000000,
   R (7588511463) 500000000000, R (1035516947) 250000000000, R (0) 1, R (1) 1,
   [R (213593780421) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 32⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_hand_caps/subintervals_38_39_43_44_47_to_54_and_bands_24_26_to_29/outputs/stage2/mgf_hand/ext/strip_50/box_000000.json`; sha256 `72917a891cab80d3f08c5d8477944c569451cfe4d0c05df36a9770b57e256068`. -/
def boxBelow50_003 : MBox :=
  ⟨R (19) 29, R (39) 59, R (295) 26, R (1037) 82, R (6394) 533,
   R (5886125617) 500000000000, R (-10347741433) 500000000000,
   R (2317303428120532173142875635126387760630318738101) 21267647932558653966460912964485513216000000000000,
   R (2447833049) 250000000000, R (226132459) 250000000000, R (0) 1, R (1) 1,
   [R (109553611731) 125000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 104⟩
/-- Lemma 5.4: the exact 4 boxes of Below50. -/
def boxesBelow50 : List MBox := [
  boxBelow50_000,
  boxBelow50_001,
  boxBelow50_002,
  boxBelow50_003
]

/-- Lemma 5.4: the exact cover chains of Below50. -/
def slabsBelow50 : List Atlas.Slab := [
  ⟨R (19) 29, R (39) 59, [2, 1, 0, 3]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloBelow50 : Rat := R (236) 39

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiBelow50 : Rat := R (1037) 82

end Erdos993Lean.Analytic.V21.Data
