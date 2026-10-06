import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_43, subinterval 43

The paper's activity rectangle is [3/2, 8/5], its exact mean
rectangle is [221/16, 50]. The 3 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_43/box_000000.json`; sha256 `a5cdbd3703eccabcd789d5e703a101ea39d0a3af7a7a5d519d928edf49e12db6`. -/
def boxTo50_43_000 : MBox :=
  ⟨R (3) 5, R (8) 13, R (1021) 32, R (50) 1, R (2621) 64,
   R (57464157) 62500000000, R (-1588617197) 500000000000,
   R (323602223929735445701400618953538710891961925173) 10633823966279326983230456482242756608000000000000,
   R (3356583) 10000000000, R (22205837) 500000000000, R (0) 1, R (1) 1,
   [R (0) 1, R (304360283974923) 1000000000000, R (0) 1, R (0) 1, R (0) 1], 336⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_43/box_000001.json`; sha256 `b8ea37d246010ff8a860acac667f3105407b0b49de7d262dd90e9b58b168efa1`. -/
def boxTo50_43_001 : MBox :=
  ⟨R (3) 5, R (8) 13, R (1463) 64, R (1021) 32, R (3505) 128,
   R (464024191) 200000000000, R (-3517016047) 500000000000,
   R (19063097327799852197866740357879969090536558023) 425352958651173079329218259289710264320000000000,
   R (584503891) 500000000000, R (61417771) 500000000000, R (0) 1, R (1) 1,
   [R (10445578961763) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 232⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_43/box_000002.json`; sha256 `ea4452d5f9a120f9346759cf38bb2e40f608a001abd49188701dbbdabd6ff39b`. -/
def boxTo50_43_002 : MBox :=
  ⟨R (3) 5, R (8) 13, R (221) 16, R (1463) 64, R (2347) 128,
   R (446872) 48828125, R (-2173490573) 100000000000,
   R (57838982392303123666647826224927511486192039227) 664613997892457936451903530140172288000000000000,
   R (751581713) 500000000000, R (256636763) 500000000000, R (0) 1, R (1) 1,
   [R (44049419657) 31250000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 80⟩
/-- Lemma 5.4: the exact 3 boxes of To50_43. -/
def boxesTo50_43 : List MBox := [
  boxTo50_43_000,
  boxTo50_43_001,
  boxTo50_43_002
]

/-- Lemma 5.4: the exact cover chains of To50_43. -/
def slabsTo50_43 : List Atlas.Slab := [
  ⟨R (3) 5, R (8) 13, [2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_43 : Rat := R (221) 16

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_43 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
