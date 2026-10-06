import Erdos993Lean.Analytic.MGF.Act1.Pieces

/-!
# Lane B L4a: R18, piece 18, activity [23/25, 93/100]

Source: `LEAN/certfree/act1_test/outputs/stage2/mgf_D65/strip_18` and `certfree/act1_test/REPORT.md`,
refereed in `certfree/referee_act1_test/REFEREE.md` (1 October 2026).
The exact rectangle is q ∈ [23/48, 93/193], mean ∈ [1351/186, 386/31].
There are 8 boxes and 1 cover slabs, with θ = 3/5 and D = 6/5.
Every rational dual, saved centre m0, cutoff N, and cover chain is copied exactly.
Near-one R16–R19 retain the source rung-21 floors. R25S24/R25S27 use rung-25 floors.
All θ/rates/activity edges match N44/Data/Params.lean. Data are separate from the old route.
Generator: lane_b/scripts/gen_mgf_act1.py; source receipts in
lane_b/SOURCES/MGF_ACT1_SOURCE_MATCHING.json.
The corresponding check uses the unchanged MGF.pieceOK.
-/

namespace Erdos993Lean.Analytic.MGF.Act1.Data

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `certfree/act1_test/outputs/stage2/mgf_D65/strip_18/box_000000.json`; sha256 `052753e4f37665feaf4f1f598d1cf4def866e9d7868c77bc15927c5f26b47574`. -/
def boxR18_000 : MBox :=
  ⟨R (23) 48, R (93) 193, R (8299) 744, R (386) 31, R (17563) 1488,
   R (14680355991) 1000000000000, R (4812872499) 500000000000,
   R (425310494924855421943410142338343955685514297327) 8507059173023461586584365185794205286400000000000,
   R (942735311) 1000000000000, R (623915513) 1000000000000, R (1) 1, R (803006982267) 1000000000000,
   [R (232047783927) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 104⟩
/-- Exact source `certfree/act1_test/outputs/stage2/mgf_D65/strip_18/box_000001.json`; sha256 `065d5d1d72df62254c49db5c4ef7724011698b8d61864d8e5c8e823efbc971f7`. -/
def boxR18_001 : MBox :=
  ⟨R (23) 48, R (93) 193, R (3667) 372, R (8299) 744, R (5211) 496,
   R (20132194297) 1000000000000, R (1855035189) 125000000000,
   R (626481124257117141035998934231482360152267022349) 10633823966279326983230456482242756608000000000000,
   R (0) 1, R (692250713) 1000000000000, R (1) 1, R (189460757087) 250000000000,
   [R (474019051297) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 96⟩
/-- Exact source `certfree/act1_test/outputs/stage2/mgf_D65/strip_18/box_000002.json`; sha256 `60cc5045992c23fc6384f812912b67403c9c8fc3c6077dd2639ce3d0e6d49173`. -/
def boxR18_002 : MBox :=
  ⟨R (23) 48, R (93) 193, R (13703) 1488, R (3667) 372, R (9457) 992,
   R (23492870757) 1000000000000, R (15606016107) 1000000000000,
   R (1417698076909828486719489051400219019472584124063) 21267647932558653966460912964485513216000000000000,
   R (0) 1, R (460637937) 500000000000, R (1) 1, R (379400419323) 500000000000,
   [R (944295011823) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 44⟩
/-- Exact source `certfree/act1_test/outputs/stage2/mgf_D65/strip_18/box_000003.json`; sha256 `1ce46d6a53ac14159178615a137bad401d22824aeb0dde4a0ceb46ca22a5f311`. -/
def boxR18_003 : MBox :=
  ⟨R (23) 48, R (93) 193, R (2123) 248, R (13703) 1488, R (26441) 2976,
   R (26085354569) 1000000000000, R (18375426401) 1000000000000,
   R (6143209562240485635448870339978009434912320439683) 85070591730234615865843651857942052864000000000000,
   R (0) 1, R (33844003) 31250000000, R (1) 1, R (731482414727) 1000000000000,
   [R (117845549079) 125000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 80⟩
/-- Exact source `certfree/act1_test/outputs/stage2/mgf_D65/strip_18/box_000004.json`; sha256 `e59cd012d31a143bab265515c28e268f8a3eef2e5279fd0141cef990cb0f37c3`. -/
def boxR18_004 : MBox :=
  ⟨R (23) 48, R (93) 193, R (24511) 2976, R (2123) 248, R (49987) 5952,
   R (16631657547) 500000000000, R (665572437) 500000000000,
   R (14510980672805381036737318412134764555235918812043) 170141183460469231731687303715884105728000000000000,
   R (-70179559) 62500000000, R (23490411) 20000000000, R (1) 1, R (997337710251) 1000000000000,
   [R (244438362033) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 40⟩
/-- Exact source `certfree/act1_test/outputs/stage2/mgf_D65/strip_18/box_000005.json`; sha256 `4d7df30ede4e2d671261fd18fe0faae8cd365cd524199318000405d102f38ac4`. -/
def boxR18_005 : MBox :=
  ⟨R (23) 48, R (93) 193, R (11773) 1488, R (24511) 2976, R (16019) 1984,
   R (39759750899) 1000000000000, R (9168757363) 500000000000,
   R (803752031992179451500209374244212831664213340893) 8507059173023461586584365185794205286400000000000,
   R (-66985459) 12500000000, R (1038322193) 1000000000000, R (1) 1, R (404778320339) 500000000000,
   [R (1012634957383) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 40⟩
/-- Exact source `certfree/act1_test/outputs/stage2/mgf_D65/strip_18/box_000006.json`; sha256 `c121bd5a6248f1c6144b8c8676d2c32f980edcb5d3b1c536ee25b22981a5e03c`. -/
def boxR18_006 : MBox :=
  ⟨R (23) 48, R (93) 193, R (7527) 992, R (11773) 1488, R (46127) 5952,
   R (4567248651) 100000000000, R (664460449) 25000000000,
   R (4262448722868442575294460220026205369429482220439) 42535295865117307932921825928971026432000000000000,
   R (-4426285069) 500000000000, R (313472027) 1000000000000, R (1) 1, R (714852042651) 1000000000000,
   [R (1078372722063) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 72⟩
/-- Exact source `certfree/act1_test/outputs/stage2/mgf_D65/strip_18/box_000007.json`; sha256 `1fa41cbbbef4586ba5cc387dfe206d89a173242f3cf7d280acfefc8102932f21`. -/
def boxR18_007 : MBox :=
  ⟨R (23) 48, R (93) 193, R (1351) 186, R (7527) 992, R (44197) 5952,
   R (24431058601) 500000000000, R (10785655831) 500000000000,
   R (2308878883994158210681664483979579495846626162823) 21267647932558653966460912964485513216000000000000,
   R (-1960118849) 200000000000, R (422155393) 1000000000000, R (1) 1, R (392053993237) 500000000000,
   [R (108819779679) 100000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 72⟩
/-- The 8 exact boxes of R18. -/
def boxesR18 : List MBox := [
  boxR18_000,
  boxR18_001,
  boxR18_002,
  boxR18_003,
  boxR18_004,
  boxR18_005,
  boxR18_006,
  boxR18_007
]

/-- The exact source cover of R18. -/
def slabsR18 : List Atlas.Slab := [
  ⟨R (23) 48, R (93) 193, [7, 6, 5, 4, 3, 2, 1, 0]⟩
]

/-- Exact lower mean edge from certfree/act1_test/outputs/stage2/mgf_D65/strip_18/COVER.json. -/
def mloR18 : Rat := R (1351) 186

/-- Exact upper mean edge from certfree/act1_test/outputs/stage2/mgf_D65/strip_18/COVER.json. -/
def mhiR18 : Rat := R (386) 31

end Erdos993Lean.Analytic.MGF.Act1.Data
