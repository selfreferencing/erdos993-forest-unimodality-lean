import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_26, subinterval 26

The paper's activity rectangle is [26/25, 21/20], its exact mean
rectangle is [533/42, 50]. The 7 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_26/box_000000.json`; sha256 `7b25718a5d478994dbe427d9f838e005f117462f0c58699d0fd9f7cb2a75a008`. -/
def boxTo50_26_000 : MBox :=
  ⟨R (26) 51, R (21) 41, R (6833) 168, R (50) 1, R (15233) 336,
   R (168275297) 250000000000, R (-675962751) 1000000000000,
   R (216277461981169609543524570255796974402907309457) 27222589353675077077069968594541456916480000000000,
   R (38211809) 1000000000000, R (1632373) 100000000000, R (905011058469) 1000000000000, R (1) 1,
   [R (41572059653813) 8000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 376⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_26/box_000001.json`; sha256 `c0a6ec7b707faf17a47d79124f009a0f4c266879246b0a0a1258aeef5d606b9e`. -/
def boxTo50_26_001 : MBox :=
  ⟨R (26) 51, R (21) 41, R (2633) 84, R (6833) 168, R (4033) 112,
   R (635835681) 500000000000, R (-870122541) 500000000000,
   R (984633837228100284519873468926283885177061680269) 85070591730234615865843651857942052864000000000000,
   R (0) 1, R (38245489) 1000000000000, R (832086090407) 1000000000000, R (1) 1,
   [R (8439651138817) 50000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 304⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_26/box_000002.json`; sha256 `6359c4997be6857ef31a717d263ce1133bf3e857175d8c83fd8f606541602a39`. -/
def boxTo50_26_002 : MBox :=
  ⟨R (26) 51, R (21) 41, R (8965) 336, R (2633) 84, R (6499) 224,
   R (9544739) 5000000000, R (-31943507) 50000000000,
   R (4950638287600480284650609399847778987108345456797) 340282366920938463463374607431768211456000000000000,
   R (98295517) 500000000000, R (62333899) 1000000000000, R (477062866697) 500000000000, R (1) 1,
   [R (1370613732929) 40000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 248⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_26/box_000003.json`; sha256 `68a36a4a1cd1b5bdb7e53ef1562d4f702a3a7bff902a809c3ce3164888589b63`. -/
def boxTo50_26_003 : MBox :=
  ⟨R (26) 51, R (21) 41, R (1233) 56, R (8965) 336, R (16363) 672,
   R (3099923203) 1000000000000, R (-268627117) 500000000000,
   R (1672101102468708860063876582928285486025848745589) 85070591730234615865843651857942052864000000000000,
   R (252187359) 1000000000000, R (111965973) 1000000000000, R (486699227547) 500000000000, R (1) 1,
   [R (11487311097393) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 208⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_26/box_000004.json`; sha256 `0845257ff2e1cda77c4885d89bebe3729ff02ea8e645b979561d7b9787cc8012`. -/
def boxTo50_26_004 : MBox :=
  ⟨R (26) 51, R (21) 41, R (833) 48, R (1233) 56, R (13229) 672,
   R (552062699) 100000000000, R (-1125685071) 500000000000,
   R (588826357638682008011571538190053941770640968029) 21267647932558653966460912964485513216000000000000,
   R (6008117) 100000000000, R (227159237) 1000000000000, R (911694523861) 1000000000000, R (1) 1,
   [R (75394396487) 25000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 168⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_26/box_000005.json`; sha256 `1b12b427d01099888159067b780e22d8070a7ed5f4cc784d905c8aab2b18a588`. -/
def boxTo50_26_005 : MBox :=
  ⟨R (26) 51, R (21) 41, R (3365) 224, R (833) 48, R (21757) 1344,
   R (3790038539) 500000000000, R (-990082291) 500000000000,
   R (2849343242608262153131896507206729175084574634781) 85070591730234615865843651857942052864000000000000,
   R (3110201) 4000000000, R (3059991) 8000000000, R (940241647791) 1000000000000, R (1) 1,
   [R (1461323697453) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 72⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_26/box_000006.json`; sha256 `d3d83c9e2b0fb3357a6df1bf0afdc4903f046d88d6c35e0ac56858b1146dab45`. -/
def boxTo50_26_006 : MBox :=
  ⟨R (26) 51, R (21) 41, R (533) 42, R (3365) 224, R (18623) 1344,
   R (5344342467) 500000000000, R (-129054287) 500000000000,
   R (6925008847420809703152841417667189075908604786571) 170141183460469231731687303715884105728000000000000,
   R (308567721) 250000000000, R (256815853) 500000000000, R (1) 1, R (9927524611) 10000000000,
   [R (1372235859421) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 120⟩
/-- Lemma 5.4: the exact 7 boxes of To50_26. -/
def boxesTo50_26 : List MBox := [
  boxTo50_26_000,
  boxTo50_26_001,
  boxTo50_26_002,
  boxTo50_26_003,
  boxTo50_26_004,
  boxTo50_26_005,
  boxTo50_26_006
]

/-- Lemma 5.4: the exact cover chains of To50_26. -/
def slabsTo50_26 : List Atlas.Slab := [
  ⟨R (26) 51, R (21) 41, [6, 5, 4, 3, 2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_26 : Rat := R (533) 42

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_26 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
