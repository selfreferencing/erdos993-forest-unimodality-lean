import Erdos993Lean.Analytic.MGF.Act1.Pieces

/-!
# Lane B L4a: R17, piece 17, activity [91/100, 23/25]

Source: `LEAN/certfree/act1_test/outputs/stage2/mgf_D65/strip_17` and `certfree/act1_test/REPORT.md`,
refereed in `certfree/referee_act1_test/REFEREE.md` (1 October 2026).
The exact rectangle is q ∈ [91/191, 23/48], mean ∈ [168/23, 288/23].
There are 9 boxes and 2 cover slabs, with θ = 3/5 and D = 6/5.
Every rational dual, saved centre m0, cutoff N, and cover chain is copied exactly.
Near-one R16–R19 retain the source rung-21 floors. R25S24/R25S27 use rung-25 floors.
All θ/rates/activity edges match N44/Data/Params.lean. Data are separate from the old route.
Generator: lane_b/scripts/gen_mgf_act1.py; source receipts in
lane_b/SOURCES/MGF_ACT1_SOURCE_MATCHING.json.
The corresponding check uses the unchanged MGF.pieceOK.
-/

namespace Erdos993Lean.Analytic.MGF.Act1.Data

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `certfree/act1_test/outputs/stage2/mgf_D65/strip_17/box_000000.json`; sha256 `49ec97f4ec41342096c9137274c193a908211eed5471b6cc2fb2e91c4b18327a`. -/
def boxR17_000 : MBox :=
  ⟨R (91) 191, R (23) 48, R (258) 23, R (288) 23, R (273) 23,
   R (1845142097) 125000000000, R (9538989487) 1000000000000,
   R (867770545135638624778511327199772744951998487331) 17014118346046923173168730371588410572800000000000,
   R (178995601) 200000000000, R (12678923) 20000000000, R (1) 1, R (805205584461) 1000000000000,
   [R (185434558861) 200000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 104⟩
/-- Exact source `certfree/act1_test/outputs/stage2/mgf_D65/strip_17/box_000001.json`; sha256 `d3b0f24aa26deb9a28c15ef629c3659be3e945e1604b6ad696a572cebfb630a3`. -/
def boxR17_001 : MBox :=
  ⟨R (91) 191, R (23) 48, R (228) 23, R (258) 23, R (243) 23,
   R (18611464517) 1000000000000, R (7256952251) 500000000000,
   R (1192156622961175322988572293039455744485902326953) 21267647932558653966460912964485513216000000000000,
   R (497105519) 1000000000000, R (301213767) 500000000000, R (1) 1, R (152244704581) 200000000000,
   [R (237758796219) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 96⟩
/-- Exact source `certfree/act1_test/outputs/stage2/mgf_D65/strip_17/box_000002.json`; sha256 `e15ae5ed2cbfa8f019da98b697159e17e06805a6efa09a71276cff66f198d391`. -/
def boxR17_002 : MBox :=
  ⟨R (91) 191, R (23) 48, R (213) 23, R (228) 23, R (441) 46,
   R (21304618961) 1000000000000, R (14637380351) 1000000000000,
   R (42261633996400408363518683911630242917213523561) 680564733841876926926749214863536422912000000000,
   R (223925781) 250000000000, R (733638813) 1000000000000, R (1) 1, R (191971220939) 250000000000,
   [R (23766435879) 25000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 88⟩
/-- Exact source `certfree/act1_test/outputs/stage2/mgf_D65/strip_17/box_000003.json`; sha256 `87e0629d69b553369fe488ab303801ef26acb62402a3581705321712fd250920`. -/
def boxR17_003 : MBox :=
  ⟨R (91) 191, R (23) 48, R (198) 23, R (213) 23, R (411) 46,
   R (25888323889) 1000000000000, R (17517598047) 1000000000000,
   R (192829940952657084822900664309325509967458972639) 2658455991569831745807614120560689152000000000000,
   R (0) 1, R (516004017) 500000000000, R (1) 1, R (185955570437) 250000000000,
   [R (947266291403) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 80⟩
/-- Exact source `certfree/act1_test/outputs/stage2/mgf_D65/strip_17/box_000004.json`; sha256 `b0612c2cd6c9335e051acd81530f7b3e1fa5fa386cd7fc9f2e8727a5024411ea`. -/
def boxR17_004 : MBox :=
  ⟨R (8761) 18336, R (23) 48, R (381) 46, R (198) 23, R (777) 92,
   R (15261267123) 500000000000, R (10304723373) 500000000000,
   R (6668466915230968291889347882706564539382006464023) 85070591730234615865843651857942052864000000000000,
   R (-338333917) 250000000000, R (99441191) 125000000000, R (1) 1, R (729844952809) 1000000000000,
   [R (982238187199) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 80⟩
/-- Exact source `certfree/act1_test/outputs/stage2/mgf_D65/strip_17/box_000005.json`; sha256 `3add25febe906763099cf5f45a6b06df60b381006c183813123d29a1300316fd`. -/
def boxR17_005 : MBox :=
  ⟨R (8761) 18336, R (23) 48, R (183) 23, R (381) 46, R (747) 92,
   R (1893581837) 50000000000, R (18690304259) 500000000000,
   R (85359363403) 1000000000000,
   R (-6600031891) 1000000000000, R (21966997) 250000000000, R (1) 1, R (139685878207) 250000000000,
   [R (1062452193543) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 160⟩
/-- Exact source `certfree/act1_test/outputs/stage2/mgf_D65/strip_17/box_000006.json`; sha256 `f1b54794f4cda747a1b3428afeb32f0ef40c57ee3d313f79bdf898db10acf30e`. -/
def boxR17_006 : MBox :=
  ⟨R (91) 191, R (8761) 18336, R (183) 23, R (198) 23, R (381) 46,
   R (33909746793) 1000000000000, R (6592412143) 500000000000,
   R (889717356251884054868385129115144923955524468583) 10633823966279326983230456482242756608000000000000,
   R (-2321634959) 1000000000000, R (331606209) 500000000000, R (1) 1, R (848952886211) 1000000000000,
   [R (1010552221243) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 80⟩
/-- Exact source `certfree/act1_test/outputs/stage2/mgf_D65/strip_17/box_000007.json`; sha256 `fc40caf91120b21a11aeaccac492afdc971552990e38819ae13610fd9bea9e0b`. -/
def boxR17_007 : MBox :=
  ⟨R (91) 191, R (23) 48, R (351) 46, R (183) 23, R (717) 92,
   R (41295983563) 1000000000000, R (14147405089) 500000000000,
   R (8304856230923141261072426886126019586228709284887) 85070591730234615865843651857942052864000000000000,
   R (-172676757) 25000000000, R (171006783) 250000000000, R (1) 1, R (342920339953) 500000000000,
   [R (520490232757) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 72⟩
/-- Exact source `certfree/act1_test/outputs/stage2/mgf_D65/strip_17/box_000008.json`; sha256 `0c34c16f00caa4a98291e45183036489c738d8fe9248eb62ef42982758bf891a`. -/
def boxR17_008 : MBox :=
  ⟨R (91) 191, R (23) 48, R (168) 23, R (351) 46, R (687) 92,
   R (1890776703) 40000000000, R (5580942659) 250000000000,
   R (9006404040641632039322714902847988142642564904559) 85070591730234615865843651857942052864000000000000,
   R (-9234064417) 1000000000000, R (28064827) 125000000000, R (1) 1, R (152770112849) 200000000000,
   [R (546664755197) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 72⟩
/-- The 9 exact boxes of R17. -/
def boxesR17 : List MBox := [
  boxR17_000,
  boxR17_001,
  boxR17_002,
  boxR17_003,
  boxR17_004,
  boxR17_005,
  boxR17_006,
  boxR17_007,
  boxR17_008
]

/-- The exact source cover of R17. -/
def slabsR17 : List Atlas.Slab := [
  ⟨R (91) 191, R (8761) 18336, [8, 7, 6, 3, 2, 1, 0]⟩,
  ⟨R (8761) 18336, R (23) 48, [8, 7, 5, 4, 3, 2, 1, 0]⟩
]

/-- Exact lower mean edge from certfree/act1_test/outputs/stage2/mgf_D65/strip_17/COVER.json. -/
def mloR17 : Rat := R (168) 23

/-- Exact upper mean edge from certfree/act1_test/outputs/stage2/mgf_D65/strip_17/COVER.json. -/
def mhiR17 : Rat := R (288) 23

end Erdos993Lean.Analytic.MGF.Act1.Data
