import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: Below39, subinterval 39

The paper's activity rectangle is [27/20, 7/5], its exact mean
rectangle is [48/7, 96/7]. The 5 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `atlas_mgf/rung_21/strip_39/box_000000.json`; sha256 `5f8dcb8180c7c55ced1fd4f7e0f1771348c18f9d7050fa16adec558b7ac7f917`. -/
def boxBelow39_000 : MBox :=
  ⟨R (27) 47, R (7) 12, R (69) 7, R (12) 1, R (153) 14,
   R (9585391007) 500000000000, R (-3682129929) 100000000000,
   R (228473648311160721235840268708585549724670152769) 2658455991569831745807614120560689152000000000000,
   R (2326720977) 500000000000, R (518842923) 500000000000, R (105262640321) 500000000000, R (1) 1,
   [R (214954925031) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 48⟩
/-- Exact source `atlas_mgf/rung_21/strip_39/box_000001.json`; sha256 `20318f3428c7f9746b52a15bc1027cad1be19020f00fc61f8abbb8e278d4cab7`. -/
def boxBelow39_001 : MBox :=
  ⟨R (27) 47, R (7) 12, R (54) 7, R (69) 7, R (123) 14,
   R (35547684111) 1000000000000, R (-14187082717) 200000000000,
   R (312210025802694827217106653197721010807065940679) 2658455991569831745807614120560689152000000000000,
   R (1756750409) 500000000000, R (247948711) 125000000000, R (0) 1, R (1) 1,
   [R (832883052817) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 40⟩
/-- Exact source `atlas_mgf/rung_21/strip_39/box_000002.json`; sha256 `ceb28dd64ed36bf8bce4416d8c7bfe9946d9550283bbfeb5ecea34bbf7958ab3`. -/
def boxBelow39_002 : MBox :=
  ⟨R (27) 47, R (7) 12, R (48) 7, R (54) 7, R (51) 7,
   R (12075171913) 250000000000, R (-18107588327) 200000000000,
   R (35385096861175307130489297035136509593375523209) 265845599156983174580761412056068915200000000000,
   R (485716083) 250000000000, R (2098328841) 1000000000000, R (0) 1, R (1) 1,
   [R (54680600399) 62500000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 36⟩
/-- Exact source `atlas_mgf/rung_21/strip_39/box_000003.json`; sha256 `4c76f85dd6b01dfa9bcbc570708b72e30ef5de955f364ee9b80aa81206bfd6e7`. -/
def boxBelow39_003 : MBox :=
  ⟨R (27) 47, R (7) 12, R (6) 1, R (48) 7, R (45) 7,
   R (1505608153) 25000000000, R (-102724539723) 1000000000000,
   R (1587084947176866876069218666722811767505106687487) 10633823966279326983230456482242756608000000000000,
   R (0) 1, R (2222718963) 1000000000000, R (0) 1, R (1) 1,
   [R (112640260359) 125000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 32⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_hand_caps/subintervals_38_39_43_44_47_to_54_and_bands_24_26_to_29/outputs/stage2/mgf_hand/ext/strip_39/box_000000.json`; sha256 `d5395fb5634b713b5d8cc735055a04b65d0c844e19e96a13c4bb05880b81f338`. -/
def boxBelow39_004 : MBox :=
  ⟨R (27) 47, R (7) 12, R (12) 1, R (96) 7, R (90) 7,
   R (1524120277) 125000000000, R (-30740595049) 1000000000000,
   R (746343098188018693608516137198598130980686399999) 10633823966279326983230456482242756608000000000000,
   R (19588149) 3906250000, R (73886869) 100000000000, R (2126555807) 125000000000, R (1) 1,
   [R (933327352123) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 56⟩
/-- Lemma 5.4: the exact 5 boxes of Below39. -/
def boxesBelow39 : List MBox := [
  boxBelow39_000,
  boxBelow39_001,
  boxBelow39_002,
  boxBelow39_003,
  boxBelow39_004
]

/-- Lemma 5.4: the exact cover chains of Below39. -/
def slabsBelow39 : List Atlas.Slab := [
  ⟨R (27) 47, R (7) 12, [3, 2, 1, 0, 4]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloBelow39 : Rat := R (48) 7

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiBelow39 : Rat := R (96) 7

end Erdos993Lean.Analytic.V21.Data
