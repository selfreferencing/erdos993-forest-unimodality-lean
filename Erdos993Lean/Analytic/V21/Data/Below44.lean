import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: Below44, subinterval 44

The paper's activity rectangle is [8/5, 33/20], its exact mean
rectangle is [212/33, 187/14]. The 5 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `atlas_mgf/rung_21/strip_44/box_000000.json`; sha256 `821f115b09dbcfc65cca9c4be246c741f83cd54ef46d832596146ad0abe1b755`. -/
def boxBelow44_000 : MBox :=
  ⟨R (8) 13, R (33) 53, R (1219) 132, R (371) 33, R (901) 88,
   R (20896159623) 1000000000000, R (-40858059033) 1000000000000,
   R (1303676471724807651277872121288701151403221076941) 10633823966279326983230456482242756608000000000000,
   R (1123648973) 125000000000, R (766287559) 500000000000, R (0) 1, R (1) 1,
   [R (406174733561) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 48⟩
/-- Exact source `atlas_mgf/rung_21/strip_44/box_000001.json`; sha256 `1c3a37595c74a7fe328c96d5b4e1f5dea613d82005ea6d544f6eb1b5d6729187`. -/
def boxBelow44_001 : MBox :=
  ⟨R (8) 13, R (33) 53, R (159) 22, R (1219) 132, R (2173) 264,
   R (10495925063) 250000000000, R (-70785678563) 1000000000000,
   R (457588641037757230091917707653034821912960742277) 2658455991569831745807614120560689152000000000000,
   R (778012543) 100000000000, R (2429267051) 1000000000000, R (0) 1, R (1) 1,
   [R (209174613753) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 40⟩
/-- Exact source `atlas_mgf/rung_21/strip_44/box_000002.json`; sha256 `18428c5bd6c4fa31ca059c78202b1379e462b51dcac7c1734c2faecfb45987d0`. -/
def boxBelow44_002 : MBox :=
  ⟨R (8) 13, R (33) 53, R (212) 33, R (159) 22, R (901) 132,
   R (11092712277) 250000000000, R (-14883536181) 200000000000,
   R (432206869109883514857262743725328599447971131357) 2658455991569831745807614120560689152000000000000,
   R (13965506723) 1000000000000, R (24710547) 10000000000, R (0) 1, R (1) 1,
   [R (167910364677) 200000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 32⟩
/-- Exact source `atlas_mgf/rung_21/strip_44/box_000003.json`; sha256 `9cfa857fed52aa41a4db73123d2b01864b53b379b2a1307a0de3f4de0d6d2266`. -/
def boxBelow44_003 : MBox :=
  ⟨R (8) 13, R (33) 53, R (371) 66, R (212) 33, R (265) 44,
   R (72376773723) 1000000000000, R (-102557283609) 1000000000000,
   R (449872065801695927430748756230165602748205256277) 2126764793255865396646091296448551321600000000000,
   R (8726796809) 1000000000000, R (728493117) 200000000000, R (0) 1, R (1) 1,
   [R (171757609631) 200000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 32⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_hand_caps/subintervals_38_39_43_44_47_to_54_and_bands_24_26_to_29/outputs/stage2/mgf_hand/ext/strip_44/box_000000.json`; sha256 `1c5992a6c2ac14a43fcb8a3c9ea99f9acc2f149e49351b486030d9807741f402`. -/
def boxBelow44_004 : MBox :=
  ⟨R (8) 13, R (33) 53, R (371) 33, R (187) 14, R (11365) 924,
   R (429044291) 31250000000, R (-28734679553) 1000000000000,
   R (1072386220417720027297417012580019763623672141451) 10633823966279326983230456482242756608000000000000,
   R (3570457743) 500000000000, R (784594267) 1000000000000, R (0) 1, R (1) 1,
   [R (184921397599) 125000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 56⟩
/-- Lemma 5.4: the exact 5 boxes of Below44. -/
def boxesBelow44 : List MBox := [
  boxBelow44_000,
  boxBelow44_001,
  boxBelow44_002,
  boxBelow44_003,
  boxBelow44_004
]

/-- Lemma 5.4: the exact cover chains of Below44. -/
def slabsBelow44 : List Atlas.Slab := [
  ⟨R (8) 13, R (33) 53, [3, 2, 1, 0, 4]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloBelow44 : Rat := R (212) 33

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiBelow44 : Rat := R (187) 14

end Erdos993Lean.Analytic.V21.Data
