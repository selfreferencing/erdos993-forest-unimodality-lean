import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_44, subinterval 44

The paper's activity rectangle is [8/5, 33/20], its exact mean
rectangle is [187/14, 50]. The 3 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_44/box_000000.json`; sha256 `2e1616823d5b95eb3bfbfc90d5970999c3a89afea45e97b6f24cb57c55be4779`. -/
def boxTo50_44_000 : MBox :=
  ⟨R (8) 13, R (33) 53, R (887) 28, R (50) 1, R (2287) 56,
   R (383927999) 500000000000, R (-1246425973) 500000000000,
   R (641317819087200531996264246786584356400171754191) 21267647932558653966460912964485513216000000000000,
   R (362082643) 1000000000000, R (10210779) 250000000000, R (0) 1, R (1) 1,
   [R (15381486658899) 15625000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 336⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_44/box_000001.json`; sha256 `bf2c2a4e5dc07b12c9e8e9c3b1346832b98ddc7654f6fcfa01396c8b60037463`. -/
def boxTo50_44_001 : MBox :=
  ⟨R (8) 13, R (33) 53, R (1261) 56, R (887) 28, R (3035) 112,
   R (514562107) 250000000000, R (-2952279911) 500000000000,
   R (196403038933721209796153075899118356830849920211) 4253529586511730793292182592897102643200000000000,
   R (262317021) 200000000000, R (22894907) 200000000000, R (0) 1, R (1) 1,
   [R (6011419617463) 125000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 232⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_44/box_000002.json`; sha256 `b8d2bdd72a91af8a05be0ba3cc300d6ddd24f244c50393e2dbb6a421498d5c8a`. -/
def boxTo50_44_002 : MBox :=
  ⟨R (8) 13, R (33) 53, R (187) 14, R (1261) 56, R (287) 16,
   R (4481996451) 500000000000, R (-20279552911) 1000000000000,
   R (2053077235240207336255220933335130361373557805577) 21267647932558653966460912964485513216000000000000,
   R (2321309917) 1000000000000, R (506203831) 1000000000000, R (0) 1, R (1) 1,
   [R (152086290199) 100000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 76⟩
/-- Lemma 5.4: the exact 3 boxes of To50_44. -/
def boxesTo50_44 : List MBox := [
  boxTo50_44_000,
  boxTo50_44_001,
  boxTo50_44_002
]

/-- Lemma 5.4: the exact cover chains of To50_44. -/
def slabsTo50_44 : List Atlas.Slab := [
  ⟨R (8) 13, R (33) 53, [2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_44 : Rat := R (187) 14

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_44 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
