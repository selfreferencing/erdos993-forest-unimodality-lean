import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_49, subinterval 49

The paper's activity rectangle is [37/20, 19/10], its exact mean
rectangle is [493/38, 50]. The 3 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_49/box_000000.json`; sha256 `6510aa1d8835a29cf78792d8bea1cc6d336d978b5011c6f119c0a2f45ee2ce64`. -/
def boxTo50_49_000 : MBox :=
  ⟨R (37) 57, R (19) 29, R (2393) 76, R (50) 1, R (6193) 152,
   R (112805357) 200000000000, R (-176736511) 125000000000,
   R (59372944737065721281436816658652922031121065287) 2126764793255865396646091296448551321600000000000,
   R (4955903) 15625000000, R (36618687) 1000000000000, R (0) 1, R (1) 1,
   [R (550394835666743) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 336⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_49/box_000001.json`; sha256 `95c8fa9d8f70d6e35cd7c53f5c4d4ea7b6640bbfb5f8c9e360a6df056f3b4bda`. -/
def boxTo50_49_001 : MBox :=
  ⟨R (37) 57, R (19) 29, R (3379) 152, R (2393) 76, R (8165) 304,
   R (182104073) 100000000000, R (-4015007993) 1000000000000,
   R (533954490829483190347972035031685329419191308211) 10633823966279326983230456482242756608000000000000,
   R (1646785887) 1000000000000, R (25853429) 250000000000, R (0) 1, R (1) 1,
   [R (11061248926891) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 224⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_49/box_000002.json`; sha256 `0a534962de7e46b6f3a442908b130bdab6ecff0c5094213737d159bc2211e798`. -/
def boxTo50_49_002 : MBox :=
  ⟨R (37) 57, R (19) 29, R (493) 38, R (3379) 152, R (5351) 304,
   R (9347496453) 1000000000000, R (-17513824389) 1000000000000,
   R (252494176990896536810100044392840120665043462677) 2126764793255865396646091296448551321600000000000,
   R (3886803699) 1000000000000, R (58658171) 125000000000, R (0) 1, R (1) 1,
   [R (71417959291) 31250000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 76⟩
/-- Lemma 5.4: the exact 3 boxes of To50_49. -/
def boxesTo50_49 : List MBox := [
  boxTo50_49_000,
  boxTo50_49_001,
  boxTo50_49_002
]

/-- Lemma 5.4: the exact cover chains of To50_49. -/
def slabsTo50_49 : List Atlas.Slab := [
  ⟨R (37) 57, R (19) 29, [2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_49 : Rat := R (493) 38

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_49 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
