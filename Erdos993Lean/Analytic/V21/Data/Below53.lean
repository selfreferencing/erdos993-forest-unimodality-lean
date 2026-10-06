import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: Below53, subinterval 53

The paper's activity rectangle is [41/20, 9/4], its exact mean
rectangle is [52/9, 221/18]. The 4 boxes and
2 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_hand_caps/subintervals_38_39_43_44_47_to_54_and_bands_24_26_to_29/outputs/stage2/mgf_hand/full/strip_53/box_000000.json`; sha256 `44383a5bb26844523c4888f887e2a3d851cee637a730a1d412b0f06718871f70`. -/
def boxBelow53_000 : MBox :=
  ⟨R (41) 61, R (9) 13, R (325) 36, R (221) 18, R (767) 72,
   R (23417616467) 1000000000000, R (-4211970601) 125000000000,
   R (911149546009980835341691367260828575458785152929) 5316911983139663491615228241121378304000000000000,
   R (6263581849) 500000000000, R (1294969599) 1000000000000, R (0) 1, R (1) 1,
   [R (1129133894829) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 48⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_hand_caps/subintervals_38_39_43_44_47_to_54_and_bands_24_26_to_29/outputs/stage2/mgf_hand/full/strip_53/box_000001.json`; sha256 `f108ac66d4bf6926cc5e8bb50653656db126c954981ab8e89cdf25ec0987c9b5`. -/
def boxBelow53_001 : MBox :=
  ⟨R (41) 61, R (9) 13, R (533) 72, R (325) 36, R (1183) 144,
   R (36597637347) 1000000000000, R (-51087578643) 1000000000000,
   R (491406387194596959533706743802782647812633815833) 2658455991569831745807614120560689152000000000000,
   R (10476369367) 500000000000, R (961598791) 500000000000, R (0) 1, R (1) 1,
   [R (20322721073) 25000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 40⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_hand_caps/subintervals_38_39_43_44_47_to_54_and_bands_24_26_to_29/outputs/stage2/mgf_hand/full/strip_53/box_000002.json`; sha256 `2163e75d7de509707576116aad722894da49b7aae6316a1bbc4d456bf4c5d56a`. -/
def boxBelow53_002 : MBox :=
  ⟨R (541) 793, R (9) 13, R (52) 9, R (533) 72, R (949) 144,
   R (46551126237) 500000000000, R (-84289930741) 1000000000000,
   R (339735609247955697716230207960237010706927817463) 1063382396627932698323045648224275660800000000000,
   R (3636276917) 200000000000, R (2201312917) 500000000000, R (0) 1, R (1) 1,
   [R (422292488753) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 32⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_hand_caps/subintervals_38_39_43_44_47_to_54_and_bands_24_26_to_29/outputs/stage2/mgf_hand/full/strip_53/box_000003.json`; sha256 `aca799c5189033a325a9aa3e37edfe1a55bcbf0335d5255911edf3de429def59`. -/
def boxBelow53_003 : MBox :=
  ⟨R (41) 61, R (541) 793, R (52) 9, R (533) 72, R (949) 144,
   R (23274067623) 250000000000, R (-90219124727) 1000000000000,
   R (816287612474732188201501624684908767308416744977) 2658455991569831745807614120560689152000000000000,
   R (119374093) 7812500000, R (4265010727) 1000000000000, R (0) 1, R (1) 1,
   [R (85103886757) 100000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 32⟩
/-- Lemma 5.4: the exact 4 boxes of Below53. -/
def boxesBelow53 : List MBox := [
  boxBelow53_000,
  boxBelow53_001,
  boxBelow53_002,
  boxBelow53_003
]

/-- Lemma 5.4: the exact cover chains of Below53. -/
def slabsBelow53 : List Atlas.Slab := [
  ⟨R (41) 61, R (541) 793, [3, 1, 0]⟩,
  ⟨R (541) 793, R (9) 13, [2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloBelow53 : Rat := R (52) 9

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiBelow53 : Rat := R (221) 18

end Erdos993Lean.Analytic.V21.Data
