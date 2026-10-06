import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_08, subinterval 8

The paper's activity rectangle is [7/10, 3/4], its exact mean
rectangle is [14, 50]. The 3 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_08/box_000000.json`; sha256 `bc2f1ecf2c6363dba3bdd9c3055913951727e2e18e6cfcd60507ea34846cb516`. -/
def boxTo50_08_000 : MBox :=
  ⟨R (7) 17, R (3) 7, R (32) 1, R (50) 1, R (41) 1,
   R (517431177) 500000000000, R (822866787) 200000000000,
   R (534751824015156218202480019022398516004277384043) 21267647932558653966460912964485513216000000000000,
   R (35125417) 125000000000, R (38917417) 1000000000000, R (1) 1, R (21551599397) 200000000000,
   [R (47117176771629) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 336⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_08/box_000001.json`; sha256 `4d6fd0fb6c68c9e1227803aae3f52dc120b4913011f88cf2bd74282944c85245`. -/
def boxTo50_08_001 : MBox :=
  ⟨R (7) 17, R (3) 7, R (23) 1, R (32) 1, R (55) 2,
   R (1327526151) 500000000000, R (9284074411) 1000000000000,
   R (81258472421388056022428716899237582502896458153) 2126764793255865396646091296448551321600000000000,
   R (220458707) 200000000000, R (48017271) 500000000000, R (1) 1, R (0) 1,
   [R (177087010721) 31250000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 232⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_08/box_000002.json`; sha256 `7e9e5fddd3701493c0b2ca9509ebd4e1b738e3538853fdd8464b512abb9d0969`. -/
def boxTo50_08_002 : MBox :=
  ⟨R (7) 17, R (3) 7, R (14) 1, R (23) 1, R (37) 2,
   R (1855122111) 250000000000, R (2233328917) 125000000000,
   R (616272219013703813119251936387164719133064311561) 10633823966279326983230456482242756608000000000000,
   R (166875437) 125000000000, R (35762109) 125000000000, R (1) 1, R (109688342561) 500000000000,
   [R (229124225201) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 160⟩
/-- Lemma 5.4: the exact 3 boxes of To50_08. -/
def boxesTo50_08 : List MBox := [
  boxTo50_08_000,
  boxTo50_08_001,
  boxTo50_08_002
]

/-- Lemma 5.4: the exact cover chains of To50_08. -/
def slabsTo50_08 : List Atlas.Slab := [
  ⟨R (7) 17, R (3) 7, [2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_08 : Rat := R (14) 1

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_08 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
