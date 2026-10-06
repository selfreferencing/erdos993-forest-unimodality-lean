import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: Below38, subinterval 38

The paper's activity rectangle is [13/10, 27/20], its exact mean
rectangle is [188/27, 96/7]. The 8 boxes and
2 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_hand_caps/subintervals_38_39_43_44_47_to_54_and_bands_24_26_to_29/outputs/stage2/mgf_hand/full/strip_38/box_000000.json`; sha256 `53182e5e599acde391fb5d7f024070c20623b969b2c6eb9e77e085a412c8ea3e`. -/
def boxBelow38_000 : MBox :=
  ⟨R (13) 23, R (27) 47, R (7487) 756, R (96) 7, R (17855) 1512,
   R (971358349) 50000000000, R (-7401401897) 200000000000,
   R (439592552446169821469205258257166143727031831961) 5316911983139663491615228241121378304000000000000,
   R (128414871) 62500000000, R (1023053833) 1000000000000, R (235308095451) 1000000000000, R (1) 1,
   [R (431996682031) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 52⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_hand_caps/subintervals_38_39_43_44_47_to_54_and_bands_24_26_to_29/outputs/stage2/mgf_hand/full/strip_38/box_000001.json`; sha256 `a505fa7df30831b6b2d46ef452bd1f221027eeccff52bea3f4591d895620a54a`. -/
def boxBelow38_001 : MBox :=
  ⟨R (616) 1081, R (27) 47, R (4031) 504, R (7487) 756, R (27067) 3024,
   R (1802398529) 62500000000, R (-41353034877) 1000000000000,
   R (211425090798838356464539497917308167429968843199) 2126764793255865396646091296448551321600000000000,
   R (3285138727) 1000000000000, R (727219137) 500000000000, R (391885377867) 1000000000000, R (1) 1,
   [R (442775344849) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 40⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_hand_caps/subintervals_38_39_43_44_47_to_54_and_bands_24_26_to_29/outputs/stage2/mgf_hand/full/strip_38/box_000002.json`; sha256 `52603d80ac53205efa99c126e06d2025dbfd461eb52277de6023274ee58f1294`. -/
def boxBelow38_002 : MBox :=
  ⟨R (13) 23, R (616) 1081, R (4031) 504, R (7487) 756, R (27067) 3024,
   R (28325656437) 1000000000000, R (-21435473371) 500000000000,
   R (504605033076229765215957505548045724364175445151) 5316911983139663491615228241121378304000000000000,
   R (3002646409) 1000000000000, R (272675427) 200000000000, R (368639331937) 1000000000000, R (1) 1,
   [R (88979643929) 100000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 40⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_hand_caps/subintervals_38_39_43_44_47_to_54_and_bands_24_26_to_29/outputs/stage2/mgf_hand/full/strip_38/box_000003.json`; sha256 `a27cda12d04a4f88d0e10ab4c2e8ff175d17250603077a7d8fcd3faad5729475`. -/
def boxBelow38_003 : MBox :=
  ⟨R (616) 1081, R (27) 47, R (21305) 3024, R (4031) 504, R (45491) 6048,
   R (46283573211) 1000000000000, R (-17960841029) 200000000000,
   R (2663628382105380812107633414681160197650629887293) 21267647932558653966460912964485513216000000000000,
   R (865557921) 1000000000000, R (478541389) 250000000000, R (0) 1, R (1) 1,
   [R (877395797551) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 36⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_hand_caps/subintervals_38_39_43_44_47_to_54_and_bands_24_26_to_29/outputs/stage2/mgf_hand/full/strip_38/box_000004.json`; sha256 `411d6e54b9bb72ac26ea3d083a626508f54d176bd5a4019ef83b5c4c592da1a4`. -/
def boxBelow38_004 : MBox :=
  ⟨R (13) 23, R (616) 1081, R (21305) 3024, R (4031) 504, R (45491) 6048,
   R (46853697387) 1000000000000, R (-91132964779) 1000000000000,
   R (515341021876359997370631811429476532332192169873) 4253529586511730793292182592897102643200000000000,
   R (0) 1, R (1859899009) 1000000000000, R (0) 1, R (1) 1,
   [R (440433939743) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 36⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_hand_caps/subintervals_38_39_43_44_47_to_54_and_bands_24_26_to_29/outputs/stage2/mgf_hand/full/strip_38/box_000005.json`; sha256 `9ceb003d3f085d703e761dd5f9fb61350b4ee24ceecf866eb221cf5705a22ed3`. -/
def boxBelow38_005 : MBox :=
  ⟨R (13) 23, R (27) 47, R (13243) 2016, R (21305) 3024, R (82339) 12096,
   R (52502532679) 1000000000000, R (-19359445711) 200000000000,
   R (1337833994893280520438690745947036641314882403423) 10633823966279326983230456482242756608000000000000,
   R (0) 1, R (822780113) 500000000000, R (0) 1, R (1) 1,
   [R (9067541009) 10000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 64⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_hand_caps/subintervals_38_39_43_44_47_to_54_and_bands_24_26_to_29/outputs/stage2/mgf_hand/full/strip_38/box_000006.json`; sha256 `00e94c489dbcda208a4a46d7bfb2c8c70b0c869a5bce4f7db62dd386f935acbb`. -/
def boxBelow38_006 : MBox :=
  ⟨R (616) 1081, R (27) 47, R (329) 54, R (13243) 2016, R (76577) 12096,
   R (14401108537) 250000000000, R (-3155515263) 31250000000,
   R (3015296036770449418072102926041692487073833919071) 21267647932558653966460912964485513216000000000000,
   R (-113087363) 250000000000, R (236027017) 125000000000, R (0) 1, R (1) 1,
   [R (456847850461) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 32⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_hand_caps/subintervals_38_39_43_44_47_to_54_and_bands_24_26_to_29/outputs/stage2/mgf_hand/full/strip_38/box_000007.json`; sha256 `bf4ed106a0c4bd311d9382aab5cb79048c00755993c08e2f9342a59775fe0b03`. -/
def boxBelow38_007 : MBox :=
  ⟨R (13) 23, R (616) 1081, R (329) 54, R (13243) 2016, R (76577) 12096,
   R (61610012999) 1000000000000, R (-100804516039) 1000000000000,
   R (1519885968519182345175866522379258797042170429923) 10633823966279326983230456482242756608000000000000,
   R (-2022027977) 500000000000, R (162436877) 100000000000, R (70660392891) 1000000000000, R (1) 1,
   [R (944167350773) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 64⟩
/-- Lemma 5.4: the exact 8 boxes of Below38. -/
def boxesBelow38 : List MBox := [
  boxBelow38_000,
  boxBelow38_001,
  boxBelow38_002,
  boxBelow38_003,
  boxBelow38_004,
  boxBelow38_005,
  boxBelow38_006,
  boxBelow38_007
]

/-- Lemma 5.4: the exact cover chains of Below38. -/
def slabsBelow38 : List Atlas.Slab := [
  ⟨R (13) 23, R (616) 1081, [7, 5, 4, 2, 0]⟩,
  ⟨R (616) 1081, R (27) 47, [6, 5, 3, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloBelow38 : Rat := R (188) 27

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiBelow38 : Rat := R (96) 7

end Erdos993Lean.Analytic.V21.Data
