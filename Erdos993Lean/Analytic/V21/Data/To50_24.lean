import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_24, subinterval 24

The paper's activity rectangle is [1, 103/100], its exact mean
rectangle is [2639/206, 50]. The 9 boxes and
2 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_24/box_000000.json`; sha256 `961e0d656033ee4560d1e6e2dd69c5b617f9467189fb110689b5f80a607eef89`. -/
def boxTo50_24_000 : MBox :=
  ⟨R (1) 2, R (103) 203, R (33539) 824, R (50) 1, R (74739) 1648,
   R (698354483) 1000000000000, R (-545397) 500000000000,
   R (529414881315820716596858525592923006769504353279) 68056473384187692692674921486353642291200000000000,
   R (17777089) 500000000000, R (16323209) 1000000000000, R (1) 1, R (999738317241) 1000000000000,
   [R (1209327200925491) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 376⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_24/box_000001.json`; sha256 `5e578b3c4c388428368116715a4739a7f68b864295709b20185387fc718e97fe`. -/
def boxTo50_24_001 : MBox :=
  ⟨R (1) 2, R (103) 203, R (12939) 412, R (33539) 824, R (59417) 1648,
   R (1313175219) 1000000000000, R (91330123) 1000000000000,
   R (1906832286348289525945831406304888578129573655247) 170141183460469231731687303715884105728000000000000,
   R (0) 1, R (36235269) 1000000000000, R (1) 1, R (247552227661) 250000000000,
   [R (149206067044809) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 304⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_24/box_000002.json`; sha256 `0e424e9ae98b3d0fa45c25a15749cc3a8f96634e7a7fd70272a1724036351827`. -/
def boxTo50_24_002 : MBox :=
  ⟨R (1) 2, R (103) 203, R (44095) 1648, R (12939) 412, R (95851) 3296,
   R (2140198867) 1000000000000, R (-93146789) 200000000000,
   R (1289070003898214751061077693465254691796581685431) 85070591730234615865843651857942052864000000000000,
   R (80072861) 1000000000000, R (32234881) 500000000000, R (968047518897) 1000000000000, R (1) 1,
   [R (11325985675593) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 248⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_24/box_000003.json`; sha256 `9bd2bf2f93d98dc3a43573d6c76fdcfb8fc2327fb429bcee1734b5de30b857f0`. -/
def boxTo50_24_003 : MBox :=
  ⟨R (1) 2, R (103) 203, R (18217) 824, R (44095) 1648, R (80529) 3296,
   R (19707469) 6250000000, R (175068857) 1000000000000,
   R (810734438170459190028664272905445730617339308359) 42535295865117307932921825928971026432000000000000,
   R (43783237) 250000000000, R (3431569) 31250000000, R (1) 1, R (988324909953) 1000000000000,
   [R (1087307083021) 100000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 208⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_24/box_000004.json`; sha256 `a5c44420be0239959e78549087b799cde6e6d3b8d667c12d7857ca35503bc444`. -/
def boxTo50_24_004 : MBox :=
  ⟨R (409) 812, R (103) 203, R (28773) 1648, R (18217) 824, R (65207) 3296,
   R (691496217) 125000000000, R (-28339973) 20000000000,
   R (584796152170081104127110781778313804993411495493) 21267647932558653966460912964485513216000000000000,
   R (0) 1, R (129775357) 500000000000, R (1472940229) 1562500000, R (1) 1,
   [R (1608931083389) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 84⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_24/box_000005.json`; sha256 `4693adf7f61c8dd21fc31c23d187531790066dfc819cbd85ee629d735c0780cb`. -/
def boxTo50_24_005 : MBox :=
  ⟨R (1) 2, R (409) 812, R (28773) 1648, R (18217) 824, R (65207) 3296,
   R (544907041) 100000000000, R (-409068009) 1000000000000,
   R (4663963745448810403381571442032456405101322440899) 170141183460469231731687303715884105728000000000000,
   R (0) 1, R (60668607) 250000000000, R (984254246251) 1000000000000, R (1) 1,
   [R (3287516973171) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 168⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_24/box_000006.json`; sha256 `b0c95561267499896e04f0665173092093808fb147b329ed0b27b150a61cf4b8`. -/
def boxTo50_24_006 : MBox :=
  ⟨R (1) 2, R (103) 203, R (49885) 3296, R (28773) 1648, R (107431) 6592,
   R (994037707) 125000000000, R (-1138986577) 1000000000000,
   R (356034595210729253934900883134384974765488587471) 10633823966279326983230456482242756608000000000000,
   R (138290019) 250000000000, R (362798183) 1000000000000, R (966686490497) 1000000000000, R (1) 1,
   [R (767417439853) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 72⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_24/box_000007.json`; sha256 `6f0960c92cc5a0504a4aaeb29f2487b2e37fc5d08a3fe3dc45bbd26b815edcab`. -/
def boxTo50_24_007 : MBox :=
  ⟨R (409) 812, R (103) 203, R (2639) 206, R (49885) 3296, R (92109) 6592,
   R (1046235541) 100000000000, R (41572267) 500000000000,
   R (6808057697301795637501153574273034547577190524917) 170141183460469231731687303715884105728000000000000,
   R (150807211) 125000000000, R (507171211) 1000000000000, R (1) 1, R (992253364857) 1000000000000,
   [R (657648202067) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 120⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/to50/strip_24/box_000008.json`; sha256 `a67450740d2bb6ee669ea6c4b10c30d686523913dafde8f3af045f06a2dfca0e`. -/
def boxTo50_24_008 : MBox :=
  ⟨R (1) 2, R (409) 812, R (2639) 206, R (49885) 3296, R (92109) 6592,
   R (5409833319) 500000000000, R (32350173) 500000000000,
   R (3490855789527354465792551893361503031953609732807) 85070591730234615865843651857942052864000000000000,
   R (511650709) 500000000000, R (20694707) 40000000000, R (1) 1, R (99687818277) 100000000000,
   [R (1296753084953) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 60⟩
/-- Lemma 5.4: the exact 9 boxes of To50_24. -/
def boxesTo50_24 : List MBox := [
  boxTo50_24_000,
  boxTo50_24_001,
  boxTo50_24_002,
  boxTo50_24_003,
  boxTo50_24_004,
  boxTo50_24_005,
  boxTo50_24_006,
  boxTo50_24_007,
  boxTo50_24_008
]

/-- Lemma 5.4: the exact cover chains of To50_24. -/
def slabsTo50_24 : List Atlas.Slab := [
  ⟨R (1) 2, R (409) 812, [8, 6, 5, 3, 2, 1, 0]⟩,
  ⟨R (409) 812, R (103) 203, [7, 6, 4, 3, 2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_24 : Rat := R (2639) 206

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_24 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
