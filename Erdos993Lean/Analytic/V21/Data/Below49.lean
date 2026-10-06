import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: Below49, subinterval 49

The paper's activity rectangle is [37/20, 19/10], its exact mean
rectangle is [116/19, 493/38]. The 4 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `atlas_mgf/rung_21/strip_49/box_000000.json`; sha256 `fe2d899e06c52bf55a1ce5309a932305da4a869e1287552455f8d392e36bb907`. -/
def boxBelow49_000 : MBox :=
  ⟨R (37) 57, R (19) 29, R (174) 19, R (435) 38, R (783) 76,
   R (2824601631) 125000000000, R (-38145237291) 1000000000000,
   R (809967540796883369134727438498180458327082530971) 5316911983139663491615228241121378304000000000000,
   R (5754563133) 500000000000, R (681245899) 500000000000, R (0) 1, R (1) 1,
   [R (885271606371) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 48⟩
/-- Exact source `atlas_mgf/rung_21/strip_49/box_000001.json`; sha256 `5c130a07057add579d75c2e9f008332b6700080b068f77de1cab86212d9f5e29`. -/
def boxBelow49_001 : MBox :=
  ⟨R (37) 57, R (19) 29, R (261) 38, R (174) 19, R (609) 76,
   R (10184346993) 250000000000, R (-12017620993) 200000000000,
   R (421742684624968485372833775631247511974631361709) 2126764793255865396646091296448551321600000000000,
   R (295878591) 20000000000, R (2684662747) 1000000000000, R (0) 1, R (1) 1,
   [R (811602670827) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 40⟩
/-- Exact source `atlas_mgf/rung_21/strip_49/box_000002.json`; sha256 `04cb32328cb2f7f97ce1d88d1e0124e66db2cb3c679eef7a6c36e0d94c6edac0`. -/
def boxBelow49_002 : MBox :=
  ⟨R (37) 57, R (19) 29, R (203) 38, R (261) 38, R (116) 19,
   R (87027320889) 1000000000000, R (-99452443403) 1000000000000,
   R (571112586815704407693310188394845190734362145593) 2126764793255865396646091296448551321600000000000,
   R (1324322083) 100000000000, R (4061844611) 1000000000000, R (0) 1, R (1) 1,
   [R (17137799381) 20000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 32⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_hand_caps/subintervals_38_39_43_44_47_to_54_and_bands_24_26_to_29/outputs/stage2/mgf_hand/ext/strip_49/box_000000.json`; sha256 `91b3b44072648a5e7749ed650002533ff8adde025e19bc48a80e9a9b41ab1eb2`. -/
def boxBelow49_003 : MBox :=
  ⟨R (37) 57, R (19) 29, R (435) 38, R (493) 38, R (232) 19,
   R (12009276437) 1000000000000, R (-10879415157) 500000000000,
   R (2319715267982580479247875939863891455600432415469) 21267647932558653966460912964485513216000000000000,
   R (9341209379) 1000000000000, R (887991099) 1000000000000, R (0) 1, R (1) 1,
   [R (857100809333) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 56⟩
/-- Lemma 5.4: the exact 4 boxes of Below49. -/
def boxesBelow49 : List MBox := [
  boxBelow49_000,
  boxBelow49_001,
  boxBelow49_002,
  boxBelow49_003
]

/-- Lemma 5.4: the exact cover chains of Below49. -/
def slabsBelow49 : List Atlas.Slab := [
  ⟨R (37) 57, R (19) 29, [2, 1, 0, 3]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloBelow49 : Rat := R (116) 19

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiBelow49 : Rat := R (493) 38

end Erdos993Lean.Analytic.V21.Data
