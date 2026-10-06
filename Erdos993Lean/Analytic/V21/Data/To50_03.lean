import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_03, subinterval 3

The paper's activity rectangle is [9/20, 1/2], its exact mean
rectangle is [18, 50]. The 1 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_03/box_000000.json`; sha256 `455943d9d24d6cc0f1bdf4ef8bff44fd581c1b34b3ed271156581c4a75142649`. -/
def boxTo50_03_000 : MBox :=
  ⟨R (9) 29, R (1) 3, R (18) 1, R (50) 1, R (34) 1,
   R (2416694347) 1000000000000, R (2295606261) 500000000000,
   R (369751873066507426307538348940173625718800113719) 5316911983139663491615228241121378304000000000000,
   R (1357840387) 1000000000000, R (31467627) 1000000000000, R (1) 1, R (0) 1,
   [R (1292379289163) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 280⟩
/-- Lemma 5.4: the exact 1 boxes of To50_03. -/
def boxesTo50_03 : List MBox := [
  boxTo50_03_000
]

/-- Lemma 5.4: the exact cover chains of To50_03. -/
def slabsTo50_03 : List Atlas.Slab := [
  ⟨R (9) 29, R (1) 3, [0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_03 : Rat := R (18) 1

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_03 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
