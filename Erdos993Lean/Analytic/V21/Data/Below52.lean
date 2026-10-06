import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: Below52, subinterval 52

The paper's activity rectangle is [2, 41/20], its exact mean
rectangle is [244/41, 1037/82]. The 4 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `atlas_mgf/rung_21/strip_52/box_000000.json`; sha256 `7c60687af675da481baa194f585b5410540771feef6433f24948329faf624140`. -/
def boxBelow52_000 : MBox :=
  ⟨R (2) 3, R (41) 61, R (366) 41, R (915) 82, R (1647) 164,
   R (12162665403) 500000000000, R (-18127410581) 500000000000,
   R (3683844530377054976301922000763387361266615904397) 21267647932558653966460912964485513216000000000000,
   R (12679150883) 1000000000000, R (397755209) 250000000000, R (0) 1, R (1) 1,
   [R (235341833739) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 48⟩
/-- Exact source `atlas_mgf/rung_21/strip_52/box_000001.json`; sha256 `a8555e6f4821b4dbc62510e333159c7438104c5d5542785252e5b6f2777b3e9d`. -/
def boxBelow52_001 : MBox :=
  ⟨R (2) 3, R (41) 61, R (549) 82, R (366) 41, R (1281) 164,
   R (22326301771) 500000000000, R (-5822158289) 100000000000,
   R (586790411597438089507860394640242729307791184503) 2658455991569831745807614120560689152000000000000,
   R (9036758491) 500000000000, R (18024461) 6250000000, R (0) 1, R (1) 1,
   [R (805697953253) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 36⟩
/-- Exact source `atlas_mgf/rung_21/strip_52/box_000002.json`; sha256 `a658acea047b34828531cf6941271ba492ef39d2b902e4def868a66bffa96a18`. -/
def boxBelow52_002 : MBox :=
  ⟨R (2) 3, R (41) 61, R (244) 41, R (549) 82, R (1037) 164,
   R (60705577531) 1000000000000, R (-14662759369) 200000000000,
   R (2488385196943890347198607339120495524955060573801) 10633823966279326983230456482242756608000000000000,
   R (11505919043) 500000000000, R (70655503) 20000000000, R (0) 1, R (1) 1,
   [R (102295352599) 125000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 32⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_hand_caps/subintervals_38_39_43_44_47_to_54_and_bands_24_26_to_29/outputs/stage2/mgf_hand/ext/strip_52/box_000000.json`; sha256 `4c47367cd82d0c0dbdb128f9b96c0f505e0486b757e4a395b6a88b30fe64eae4`. -/
def boxBelow52_003 : MBox :=
  ⟨R (2) 3, R (41) 61, R (915) 82, R (1037) 82, R (488) 41,
   R (913704173) 62500000000, R (-11843648859) 500000000000,
   R (56336954834827257084721672328381260230422232667) 425352958651173079329218259289710264320000000000,
   R (10679925359) 1000000000000, R (181908353) 200000000000, R (0) 1, R (1) 1,
   [R (482426024347) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 104⟩
/-- Lemma 5.4: the exact 4 boxes of Below52. -/
def boxesBelow52 : List MBox := [
  boxBelow52_000,
  boxBelow52_001,
  boxBelow52_002,
  boxBelow52_003
]

/-- Lemma 5.4: the exact cover chains of Below52. -/
def slabsBelow52 : List Atlas.Slab := [
  ⟨R (2) 3, R (41) 61, [2, 1, 0, 3]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloBelow52 : Rat := R (244) 41

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiBelow52 : Rat := R (1037) 82

end Erdos993Lean.Analytic.V21.Data
