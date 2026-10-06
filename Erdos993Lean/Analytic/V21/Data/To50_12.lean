import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_12, subinterval 12

The paper's activity rectangle is [21/25, 43/50], its exact mean
rectangle is [558/43, 50]. The 4 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_12/box_000000.json`; sha256 `dc0d6abdab820c6a1a63c68fb3b32c433e1adc42f16f058283c68df18e904cda`. -/
def boxTo50_12_000 : MBox :=
  ⟨R (21) 46, R (43) 93, R (1354) 43, R (50) 1, R (1752) 43,
   R (1230839029) 1000000000000, R (4011242277) 1000000000000,
   R (182156579685016700764690762428877351202564521669) 10633823966279326983230456482242756608000000000000,
   R (0) 1, R (1368863) 40000000000, R (1) 1, R (516719278371) 1000000000000,
   [R (22017705721043) 200000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 336⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_12/box_000001.json`; sha256 `e5cdbf909119fc8c9c5e700d7c77ddeceb68d929dd3ca05f30c498a376746e34`. -/
def boxTo50_12_001 : MBox :=
  ⟨R (21) 46, R (43) 93, R (956) 43, R (1354) 43, R (1155) 43,
   R (2982365807) 1000000000000, R (75725909) 10000000000,
   R (54816344676589014305657521126833653497882999407) 2126764793255865396646091296448551321600000000000,
   R (71950429) 1000000000000, R (104711357) 1000000000000, R (1) 1, R (254421347277) 500000000000,
   [R (7775691530119) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 224⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_12/box_000002.json`; sha256 `10f456c0190cd826d080b1186dd03d5b34a1c9ee308a8e5e4b359e3b4f987dcb`. -/
def boxTo50_12_002 : MBox :=
  ⟨R (21) 46, R (43) 93, R (757) 43, R (956) 43, R (1713) 86,
   R (556896541) 125000000000, R (953063137) 100000000000,
   R (1282791104459469642501375558199672928521943905289) 42535295865117307932921825928971026432000000000000,
   R (33754931) 40000000000, R (202053303) 1000000000000, R (1) 1, R (107505465091) 200000000000,
   [R (3383071987) 2000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 168⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_12/box_000003.json`; sha256 `2c787e76f00e5a06fe6ea529b0ee85f29c093fda06d8c633a2e78c166325e4c2`. -/
def boxTo50_12_003 : MBox :=
  ⟨R (21) 46, R (43) 93, R (558) 43, R (757) 43, R (1315) 86,
   R (10302306097) 1000000000000, R (6217957909) 500000000000,
   R (199140875383723559635096108172190891291969414637) 4253529586511730793292182592897102643200000000000,
   R (10890271) 125000000000, R (464371211) 1000000000000, R (1) 1, R (10361577321) 15625000000,
   [R (457762455667) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 68⟩
/-- Lemma 5.4: the exact 4 boxes of To50_12. -/
def boxesTo50_12 : List MBox := [
  boxTo50_12_000,
  boxTo50_12_001,
  boxTo50_12_002,
  boxTo50_12_003
]

/-- Lemma 5.4: the exact cover chains of To50_12. -/
def slabsTo50_12 : List Atlas.Slab := [
  ⟨R (21) 46, R (43) 93, [3, 2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_12 : Rat := R (558) 43

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_12 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
