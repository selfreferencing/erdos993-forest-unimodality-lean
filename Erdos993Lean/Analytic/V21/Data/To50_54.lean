import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_54, subinterval 54

The paper's activity rectangle is [9/4, 7/3], its exact mean
rectangle is [90/7, 50]. The 2 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_54/box_000000.json`; sha256 `8bec3034da94d1fe057200fe5be822ad9398c85e3a4a1e80052f16d08a7958d9`. -/
def boxTo50_54_000 : MBox :=
  ⟨R (9) 13, R (7) 10, R (220) 7, R (50) 1, R (285) 7,
   R (4077127) 10000000000, R (-589366583) 1000000000000,
   R (129658857459935079586496088869911416733676034141) 5316911983139663491615228241121378304000000000000,
   R (338898161) 1000000000000, R (13584011) 500000000000, R (0) 1, R (1) 1,
   [R (0) 1, R (0) 1, R (52479224207341) 1000000000000, R (0) 1, R (0) 1], 336⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_54/box_000001.json`; sha256 `0598c2aa9a8a4f24598c24c571d42ac2c20b1a259f9a0ed6d3baa1db6de557d8`. -/
def boxTo50_54_001 : MBox :=
  ⟨R (9) 13, R (7) 10, R (90) 7, R (220) 7, R (155) 7,
   R (10209388403) 1000000000000, R (-14805145941) 1000000000000,
   R (176711976342917287921120020088182474093857407759) 1063382396627932698323045648224275660800000000000,
   R (78326863) 25000000000, R (77588273) 250000000000, R (0) 1, R (1) 1,
   [R (0) 1, R (0) 1, R (1121787113257) 500000000000, R (0) 1, R (0) 1], 96⟩
/-- Lemma 5.4: the exact 2 boxes of To50_54. -/
def boxesTo50_54 : List MBox := [
  boxTo50_54_000,
  boxTo50_54_001
]

/-- Lemma 5.4: the exact cover chains of To50_54. -/
def slabsTo50_54 : List Atlas.Slab := [
  ⟨R (9) 13, R (7) 10, [1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_54 : Rat := R (90) 7

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_54 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
