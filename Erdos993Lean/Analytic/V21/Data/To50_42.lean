import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_42, subinterval 42

The paper's activity rectangle is [29/20, 3/2], its exact mean
rectangle is [35/3, 50]. The 3 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_42/box_000000.json`; sha256 `30ca23323cb7d6aa736abf5f292631be34b4375c95d6781a1460bfe9b511fdb9`. -/
def boxTo50_42_000 : MBox :=
  ⟨R (29) 49, R (3) 5, R (185) 6, R (50) 1, R (485) 12,
   R (1185357089) 1000000000000, R (-266711793) 62500000000,
   R (1476180130723013574024508957317113320058440988403) 42535295865117307932921825928971026432000000000000,
   R (145608357) 500000000000, R (50728149) 1000000000000, R (0) 1, R (1) 1,
   [R (503428053277253) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 336⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_42/box_000001.json`; sha256 `00e70bcf0b8ba5945c43a29fa4e09539593ea507c8d98d8b2429a07d397548bc`. -/
def boxTo50_42_001 : MBox :=
  ⟨R (29) 49, R (3) 5, R (85) 4, R (185) 6, R (625) 24,
   R (3027675909) 1000000000000, R (-9461054209) 1000000000000,
   R (132320784869689960094538560958583624051511757431) 2658455991569831745807614120560689152000000000000,
   R (914949281) 1000000000000, R (179362469) 1000000000000, R (0) 1, R (1) 1,
   [R (2107576523681) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 112⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_42/box_000002.json`; sha256 `70e491ca565c1e24c58e5b885ad3f2a3040447bc304e8ecd48bbb04980dbe4f2`. -/
def boxTo50_42_002 : MBox :=
  ⟨R (29) 49, R (3) 5, R (35) 3, R (85) 4, R (395) 24,
   R (6510416327) 500000000000, R (-209311369) 8000000000,
   R (1929724514799609984132543262147921808148715372287) 21267647932558653966460912964485513216000000000000,
   R (22610713) 100000000000, R (6562753) 10000000000, R (42513080031) 200000000000, R (1) 1,
   [R (67764852933) 62500000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 72⟩
/-- Lemma 5.4: the exact 3 boxes of To50_42. -/
def boxesTo50_42 : List MBox := [
  boxTo50_42_000,
  boxTo50_42_001,
  boxTo50_42_002
]

/-- Lemma 5.4: the exact cover chains of To50_42. -/
def slabsTo50_42 : List Atlas.Slab := [
  ⟨R (29) 49, R (3) 5, [2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_42 : Rat := R (35) 3

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_42 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
