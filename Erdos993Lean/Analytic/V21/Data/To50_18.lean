import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_18, subinterval 18

The paper's activity rectangle is [23/25, 93/100], its exact mean
rectangle is [637/48, 50]. The 6 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_18/box_000000.json`; sha256 `7399062df69c391aab8ba1504922644173a81e27b687573f38e54b7a700d9e5a`. -/
def boxTo50_18_000 : MBox :=
  ⟨R (23) 48, R (93) 193, R (7837) 192, R (50) 1, R (17437) 384,
   R (664440407) 1000000000000, R (838477877) 500000000000,
   R (594173375444266608610492185826378877919440868779) 68056473384187692692674921486353642291200000000000,
   R (14077611) 200000000000, R (3231533) 200000000000, R (1) 1, R (749535600947) 1000000000000,
   [R (4187968421068337) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 376⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_18/box_000001.json`; sha256 `33632c059ddb5c397f32e4fc0317516dbc9b7949fc44c23081b64e4026bd1bf6`. -/
def boxTo50_18_001 : MBox :=
  ⟨R (23) 48, R (93) 193, R (3037) 96, R (7837) 192, R (4637) 128,
   R (130927947) 100000000000, R (2530744203) 1000000000000,
   R (1092296888139499679166955147202607446397474887911) 85070591730234615865843651857942052864000000000000,
   R (128123) 50000000000, R (244697) 6250000000, R (1) 1, R (753766093907) 1000000000000,
   [R (877960858357) 8000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 304⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_18/box_000002.json`; sha256 `f473cce805bcc2f94bf61e2c2727786e73fe89466a459832bfd1e316303680d8`. -/
def boxTo50_18_002 : MBox :=
  ⟨R (23) 48, R (93) 193, R (1437) 64, R (3037) 96, R (10385) 384,
   R (1363451167) 500000000000, R (2044067103) 500000000000,
   R (3269506732972971415872689113379497276058859800683) 170141183460469231731687303715884105728000000000000,
   R (0) 1, R (3614857) 40000000000, R (1) 1, R (374040670859) 500000000000,
   [R (2289949755491) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 232⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_18/box_000003.json`; sha256 `744668791f1d465a1c305491059183518d20addf9926e77d2515df3a64f47dd1`. -/
def boxTo50_18_003 : MBox :=
  ⟨R (23) 48, R (93) 193, R (6859) 384, R (1437) 64, R (15481) 768,
   R (4833925031) 1000000000000, R (425890907) 250000000000,
   R (8969522751330291160045475252168885516345439661241) 340282366920938463463374607431768211456000000000000,
   R (322202801) 1000000000000, R (98741289) 500000000000, R (1) 1, R (935224395297) 1000000000000,
   [R (501908962309) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 176⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_18/box_000004.json`; sha256 `6f63148b1866de78fbc287ba8e872b6aebd6024f9b7eabe1f30d0fee20a98713`. -/
def boxTo50_18_004 : MBox :=
  ⟨R (23) 48, R (93) 193, R (3985) 256, R (6859) 384, R (25673) 1536,
   R (7057084383) 1000000000000, R (6854904073) 1000000000000,
   R (5591996074385156083704103698544261142463453248899) 170141183460469231731687303715884105728000000000000,
   R (29153283) 50000000000, R (38156991) 125000000000, R (1) 1, R (77150445489) 100000000000,
   [R (254032195989) 125000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 144⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_18/box_000005.json`; sha256 `ca1cadfe7d5e1928d76577df58a5e808b56f202791960a526a7eddd8932ce10f`. -/
def boxTo50_18_005 : MBox :=
  ⟨R (23) 48, R (93) 193, R (637) 48, R (3985) 256, R (22147) 1536,
   R (2532955787) 250000000000, R (5611970763) 500000000000,
   R (857240074120643679290224502225092019689875405997) 21267647932558653966460912964485513216000000000000,
   R (110093179) 250000000000, R (111299203) 250000000000, R (1) 1, R (695239708637) 1000000000000,
   [R (74600926201) 62500000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 64⟩
/-- Lemma 5.4: the exact 6 boxes of To50_18. -/
def boxesTo50_18 : List MBox := [
  boxTo50_18_000,
  boxTo50_18_001,
  boxTo50_18_002,
  boxTo50_18_003,
  boxTo50_18_004,
  boxTo50_18_005
]

/-- Lemma 5.4: the exact cover chains of To50_18. -/
def slabsTo50_18 : List Atlas.Slab := [
  ⟨R (23) 48, R (93) 193, [5, 4, 3, 2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_18 : Rat := R (637) 48

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_18 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
