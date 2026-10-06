import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: Below47, subinterval 47

The paper's activity rectangle is [7/4, 9/5], its exact mean
rectangle is [56/9, 493/38]. The 5 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `atlas_mgf/rung_21/strip_47/box_000000.json`; sha256 `4690aa5e4c8ffc74e4d1aad50d93bf389a276050d75b26d918a0764f98a67551`. -/
def boxBelow47_000 : MBox :=
  ⟨R (7) 11, R (9) 14, R (28) 3, R (35) 3, R (21) 2,
   R (18734200149) 1000000000000, R (-34114386627) 1000000000000,
   R (136392135915270925607259772625261967479712744647) 1063382396627932698323045648224275660800000000000,
   R (10744311347) 1000000000000, R (265987299) 200000000000, R (0) 1, R (1) 1,
   [R (819467659687) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 48⟩
/-- Exact source `atlas_mgf/rung_21/strip_47/box_000001.json`; sha256 `d1a84db28daba2e515aa9bc809e98ff6e0c54f41c8dbaeceedef8d14eb83415b`. -/
def boxBelow47_001 : MBox :=
  ⟨R (7) 11, R (9) 14, R (7) 1, R (28) 3, R (49) 6,
   R (40709385181) 1000000000000, R (-15894283843) 250000000000,
   R (401568772429160580827068336402533085514297846877) 2126764793255865396646091296448551321600000000000,
   R (5866728807) 500000000000, R (317521533) 125000000000, R (0) 1, R (1) 1,
   [R (422570021477) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 40⟩
/-- Exact source `atlas_mgf/rung_21/strip_47/box_000002.json`; sha256 `60562435a6f2c38b0963d63720888e4eb02e2679365f2ec15e50b80eaf1beb58`. -/
def boxBelow47_002 : MBox :=
  ⟨R (7) 11, R (9) 14, R (56) 9, R (7) 1, R (119) 18,
   R (48321710131) 1000000000000, R (-36604368091) 500000000000,
   R (1941260771659527708011273590173760436141253985801) 10633823966279326983230456482242756608000000000000,
   R (735801033) 40000000000, R (654497611) 250000000000, R (0) 1, R (1) 1,
   [R (831149215787) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 32⟩
/-- Exact source `atlas_mgf/rung_21/strip_47/box_000003.json`; sha256 `83a11079c2b135ca6be0955b282ef67ee626ab916d2e5d16da2d604df8768efc`. -/
def boxBelow47_003 : MBox :=
  ⟨R (7) 11, R (9) 14, R (49) 9, R (56) 9, R (35) 6,
   R (2271243197) 31250000000, R (-93490228377) 1000000000000,
   R (1225877011334192510606062821194665029898478763261) 5316911983139663491615228241121378304000000000000,
   R (4037461259) 250000000000, R (12869359) 3125000000, R (0) 1, R (1) 1,
   [R (836646271713) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 28⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_hand_caps/subintervals_38_39_43_44_47_to_54_and_bands_24_26_to_29/outputs/stage2/mgf_hand/ext/strip_47/box_000000.json`; sha256 `c4a8e78b9922f76faffd14af958e513a88bda05be0c50a7850e15b4729442a39`. -/
def boxBelow47_004 : MBox :=
  ⟨R (7) 11, R (9) 14, R (35) 3, R (493) 38, R (2809) 228,
   R (2722417823) 250000000000, R (-429455131) 20000000000,
   R (2015086819157618355074597570501994026289502180179) 21267647932558653966460912964485513216000000000000,
   R (2088232869) 250000000000, R (328156507) 500000000000, R (0) 1, R (1) 1,
   [R (223928803491) 125000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 112⟩
/-- Lemma 5.4: the exact 5 boxes of Below47. -/
def boxesBelow47 : List MBox := [
  boxBelow47_000,
  boxBelow47_001,
  boxBelow47_002,
  boxBelow47_003,
  boxBelow47_004
]

/-- Lemma 5.4: the exact cover chains of Below47. -/
def slabsBelow47 : List Atlas.Slab := [
  ⟨R (7) 11, R (9) 14, [3, 2, 1, 0, 4]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloBelow47 : Rat := R (56) 9

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiBelow47 : Rat := R (493) 38

end Erdos993Lean.Analytic.V21.Data
