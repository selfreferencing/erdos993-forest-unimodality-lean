import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_45, subinterval 45

The paper's activity rectangle is [33/20, 17/10], its exact mean
rectangle is [405/34, 50]. The 3 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_45/box_000000.json`; sha256 `6470f4942df218b74152ec7645ec902ce0e86297ddf16128b62296f5e80a6acb`. -/
def boxTo50_45_000 : MBox :=
  ⟨R (33) 53, R (17) 27, R (2105) 68, R (50) 1, R (5505) 136,
   R (73564067) 100000000000, R (-2270495153) 1000000000000,
   R (318667282081140675138478029233825707713024937991) 10633823966279326983230456482242756608000000000000,
   R (15017293) 50000000000, R (45485407) 1000000000000, R (0) 1, R (1) 1,
   [R (135537313303601) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 336⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_45/box_000001.json`; sha256 `b1957e1b5b20360671159015437ffa40353949650bc74339fad27ad04c5da019`. -/
def boxTo50_45_001 : MBox :=
  ⟨R (33) 53, R (17) 27, R (2915) 136, R (2105) 68, R (7125) 272,
   R (119846089) 50000000000, R (-796323183) 125000000000,
   R (140176945906904627092474590815644115933438509479) 2658455991569831745807614120560689152000000000000,
   R (149411063) 100000000000, R (13803501) 100000000000, R (0) 1, R (1) 1,
   [R (702983131487) 50000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 224⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_45/box_000002.json`; sha256 `b316a251a240c0ab6f6a7f7ca17b58966c709b4bcd86a40e181a7be30aa648f3`. -/
def boxTo50_45_002 : MBox :=
  ⟨R (33) 53, R (17) 27, R (405) 34, R (2915) 136, R (4535) 272,
   R (409683939) 31250000000, R (-13398061549) 500000000000,
   R (1289310359851408500803482971295376931290853868383) 10633823966279326983230456482242756608000000000000,
   R (15513951) 10000000000, R (70964541) 100000000000, R (0) 1, R (1) 1,
   [R (1648649152739) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 72⟩
/-- Lemma 5.4: the exact 3 boxes of To50_45. -/
def boxesTo50_45 : List MBox := [
  boxTo50_45_000,
  boxTo50_45_001,
  boxTo50_45_002
]

/-- Lemma 5.4: the exact cover chains of To50_45. -/
def slabsTo50_45 : List Atlas.Slab := [
  ⟨R (33) 53, R (17) 27, [2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_45 : Rat := R (405) 34

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_45 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
