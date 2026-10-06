import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_39, subinterval 39

The paper's activity rectangle is [27/20, 7/5], its exact mean
rectangle is [96/7, 50]. The 3 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_39/box_000000.json`; sha256 `6d0ab6495f66f051172f307c27761102b2b059c87168646fd0e3b954465faa06`. -/
def boxTo50_39_000 : MBox :=
  ⟨R (27) 47, R (7) 12, R (223) 7, R (50) 1, R (573) 14,
   R (597973127) 500000000000, R (-1213321549) 250000000000,
   R (40107649367950726118835707489924907420363117597) 1329227995784915872903807060280344576000000000000,
   R (313168737) 1000000000000, R (12094669) 250000000000, R (0) 1, R (1) 1,
   [R (63995212207539) 200000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 336⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_39/box_000001.json`; sha256 `d7bd0ad3894edd1b49e7b43b90d335c1fdc4e86f23ade97db9f83ad260314c4d`. -/
def boxTo50_39_001 : MBox :=
  ⟨R (27) 47, R (7) 12, R (319) 14, R (223) 7, R (765) 28,
   R (2806634559) 1000000000000, R (-900083123) 100000000000,
   R (867354285220704862644771021195789786573616270759) 21267647932558653966460912964485513216000000000000,
   R (388754819) 500000000000, R (33642189) 250000000000, R (66362900513) 500000000000, R (1) 1,
   [R (2542596658579) 125000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 232⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_39/box_000002.json`; sha256 `5b2542425ae61d766fcceeb199b68124ea5cd9babd769a470560337385c4526d`. -/
def boxTo50_39_002 : MBox :=
  ⟨R (27) 47, R (7) 12, R (96) 7, R (319) 14, R (73) 4,
   R (73712887) 8000000000, R (-25032804711) 1000000000000,
   R (150204434142928859781120212739422211704044784509) 2126764793255865396646091296448551321600000000000,
   R (628162543) 1000000000000, R (59912903) 125000000000, R (0) 1, R (1) 1,
   [R (266743847997) 125000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 80⟩
/-- Lemma 5.4: the exact 3 boxes of To50_39. -/
def boxesTo50_39 : List MBox := [
  boxTo50_39_000,
  boxTo50_39_001,
  boxTo50_39_002
]

/-- Lemma 5.4: the exact cover chains of To50_39. -/
def slabsTo50_39 : List Atlas.Slab := [
  ⟨R (27) 47, R (7) 12, [2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_39 : Rat := R (96) 7

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_39 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
