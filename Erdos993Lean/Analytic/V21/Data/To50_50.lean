import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_50, subinterval 50

The paper's activity rectangle is [19/10, 39/20], its exact mean
rectangle is [1037/82, 50]. The 3 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_50/box_000000.json`; sha256 `140750d19079d342ac32dfaff8f50630c2fa9eee218e7f8915f49f08dcea2819`. -/
def boxTo50_50_000 : MBox :=
  ⟨R (19) 29, R (39) 59, R (5137) 164, R (50) 1, R (13337) 328,
   R (293505201) 500000000000, R (-1344526839) 1000000000000,
   R (2539345825601849055644034981587317596319383279383) 85070591730234615865843651857942052864000000000000,
   R (40444607) 100000000000, R (33899783) 1000000000000, R (0) 1, R (1) 1,
   [R (20719795693797) 31250000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 336⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_50/box_000001.json`; sha256 `fdd9c423e90d8500fa1a6c12ce4177ef185640379dd01a55388f437850711cc9`. -/
def boxTo50_50_001 : MBox :=
  ⟨R (19) 29, R (39) 59, R (7211) 328, R (5137) 164, R (17485) 656,
   R (1777208121) 1000000000000, R (-479402173) 125000000000,
   R (427233226026251193498595939125697014152826317101) 8507059173023461586584365185794205286400000000000,
   R (1519899313) 1000000000000, R (54298869) 500000000000, R (0) 1, R (1) 1,
   [R (23938197945293) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 224⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_50/box_000002.json`; sha256 `7fa432d6e349e8cc476007c89ae0c70c787e468947b45e4914b4242b207a41fc`. -/
def boxTo50_50_002 : MBox :=
  ⟨R (19) 29, R (39) 59, R (1037) 82, R (7211) 328, R (11359) 656,
   R (10278331099) 1000000000000, R (-18349456307) 1000000000000,
   R (2727203983613245472662350862716811214854242698253) 21267647932558653966460912964485513216000000000000,
   R (433805401) 100000000000, R (471920617) 1000000000000, R (0) 1, R (1) 1,
   [R (510201576627) 200000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 76⟩
/-- Lemma 5.4: the exact 3 boxes of To50_50. -/
def boxesTo50_50 : List MBox := [
  boxTo50_50_000,
  boxTo50_50_001,
  boxTo50_50_002
]

/-- Lemma 5.4: the exact cover chains of To50_50. -/
def slabsTo50_50 : List Atlas.Slab := [
  ⟨R (19) 29, R (39) 59, [2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_50 : Rat := R (1037) 82

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_50 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
