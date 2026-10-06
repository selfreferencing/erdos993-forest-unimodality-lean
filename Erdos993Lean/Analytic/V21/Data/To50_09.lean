import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_09, subinterval 9

The paper's activity rectangle is [3/4, 39/50], its exact mean
rectangle is [178/13, 50]. The 3 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_09/box_000000.json`; sha256 `a45b85aaa624145e62bb6f383da0cec3a2f85f8d5d07fb2f4df30b4238c9772c`. -/
def boxTo50_09_000 : MBox :=
  ⟨R (3) 7, R (39) 89, R (414) 13, R (50) 1, R (532) 13,
   R (262718567) 250000000000, R (2007401717) 500000000000,
   R (481264787339404612244807520964005696496067552907) 21267647932558653966460912964485513216000000000000,
   R (29428243) 125000000000, R (7101119) 200000000000, R (1) 1, R (283642752311) 1000000000000,
   [R (5333351221211) 125000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 336⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_09/box_000001.json`; sha256 `1936ac739220c94143e4e3405b01bc9bbae8af46da6ce422ab3071cf0db676b2`. -/
def boxTo50_09_001 : MBox :=
  ⟨R (3) 7, R (39) 89, R (296) 13, R (414) 13, R (355) 13,
   R (2934364597) 1000000000000, R (1978799357) 200000000000,
   R (48507809901064813823002341256487665361938902613) 1329227995784915872903807060280344576000000000000,
   R (766390103) 1000000000000, R (48197629) 500000000000, R (1) 1, R (35840322041) 250000000000,
   [R (4358561162277) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 232⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_09/box_000002.json`; sha256 `67d8880c9538c9df6e3bbf35e6edb25c6bd0d59d7b5b05b0d3ada9baba52095b`. -/
def boxTo50_09_002 : MBox :=
  ⟨R (3) 7, R (39) 89, R (178) 13, R (296) 13, R (237) 13,
   R (9831854581) 1000000000000, R (24394741739) 1000000000000,
   R (649167430215784027507819988748128889859055645683) 10633823966279326983230456482242756608000000000000,
   R (103432259) 1000000000000, R (338060653) 1000000000000, R (1) 1, R (168398243401) 1000000000000,
   [R (916505999461) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 80⟩
/-- Lemma 5.4: the exact 3 boxes of To50_09. -/
def boxesTo50_09 : List MBox := [
  boxTo50_09_000,
  boxTo50_09_001,
  boxTo50_09_002
]

/-- Lemma 5.4: the exact cover chains of To50_09. -/
def slabsTo50_09 : List Atlas.Slab := [
  ⟨R (3) 7, R (39) 89, [2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_09 : Rat := R (178) 13

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_09 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
