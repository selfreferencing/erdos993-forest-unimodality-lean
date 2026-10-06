import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_05, subinterval 5

The paper's activity rectangle is [11/20, 3/5], its exact mean
rectangle is [16, 50]. The 2 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_05/box_000000.json`; sha256 `19c1c67b1f2a243e7878e6cb0a76439b72c5af8b99c5afb88069b7ba843481c1`. -/
def boxTo50_05_000 : MBox :=
  ⟨R (11) 31, R (3) 8, R (33) 1, R (50) 1, R (83) 2,
   R (447507937) 1000000000000, R (1358749241) 1000000000000,
   R (444024957488015836522790538200848872862508421349) 21267647932558653966460912964485513216000000000000,
   R (233036297) 500000000000, R (2107427) 100000000000, R (1) 1, R (0) 1,
   [R (1474510878539) 125000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 344⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_05/box_000001.json`; sha256 `0cd336a38fc96fc6162596e19d1b0738157a8d41cb64436259ff07c4cb5eeeea`. -/
def boxTo50_05_001 : MBox :=
  ⟨R (11) 31, R (3) 8, R (16) 1, R (33) 1, R (49) 2,
   R (4443854211) 1000000000000, R (126726041) 12500000000,
   R (814031472872397138360983157173277469659967780709) 10633823966279326983230456482242756608000000000000,
   R (1654595721) 1000000000000, R (144602917) 1000000000000, R (1) 1, R (0) 1,
   [R (470675213581) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 208⟩
/-- Lemma 5.4: the exact 2 boxes of To50_05. -/
def boxesTo50_05 : List MBox := [
  boxTo50_05_000,
  boxTo50_05_001
]

/-- Lemma 5.4: the exact cover chains of To50_05. -/
def slabsTo50_05 : List Atlas.Slab := [
  ⟨R (11) 31, R (3) 8, [1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_05 : Rat := R (16) 1

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_05 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
