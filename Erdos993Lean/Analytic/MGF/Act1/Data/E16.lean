import Erdos993Lean.Analytic.MGF.Act1.Pieces

/-!
# Lane B L4a: E16, piece 16, activity [89/100, 91/100]

Source: `LEAN/certfree/act1_test/outputs/stage2/mgf_ext_D65/strip_16` and `certfree/act1_test/REPORT.md`,
refereed in `certfree/referee_act1_test/REFEREE.md` (1 October 2026).
The exact rectangle is q ∈ [89/189, 91/191], mean ∈ [1146/91, 312/23].
There are 1 boxes and 1 cover slabs, with θ = 3/5 and D = 6/5.
Every rational dual, saved centre m0, cutoff N, and cover chain is copied exactly.
Near-one R16–R19 retain the source rung-21 floors. R25S24/R25S27 use rung-25 floors.
All θ/rates/activity edges match N44/Data/Params.lean. Data are separate from the old route.
Generator: lane_b/scripts/gen_mgf_act1.py; source receipts in
lane_b/SOURCES/MGF_ACT1_SOURCE_MATCHING.json.
The corresponding check uses the unchanged MGF.pieceOK.
-/

namespace Erdos993Lean.Analytic.MGF.Act1.Data

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `certfree/act1_test/outputs/stage2/mgf_ext_D65/strip_16/box_000000.json`; sha256 `543c24f4e8aca6f99336d3f02e2d608b0a1b09a4053ab79744bab682d0bcdfb2`. -/
def boxE16_000 : MBox :=
  ⟨R (89) 189, R (91) 191, R (1146) 91, R (312) 23, R (27375) 2093,
   R (1139105143) 100000000000, R (2237580923) 250000000000,
   R (18773125767912687321205183486314496713141181311) 425352958651173079329218259289710264320000000000,
   R (154926167) 125000000000, R (265162479) 500000000000, R (1) 1, R (781479440289) 1000000000000,
   [R (917972778767) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 60⟩
/-- The 1 exact boxes of E16. -/
def boxesE16 : List MBox := [
  boxE16_000
]

/-- The exact source cover of E16. -/
def slabsE16 : List Atlas.Slab := [
  ⟨R (89) 189, R (91) 191, [0]⟩
]

/-- Exact lower mean edge from certfree/act1_test/outputs/stage2/mgf_ext_D65/strip_16/COVER.json. -/
def mloE16 : Rat := R (1146) 91

/-- Exact upper mean edge from certfree/act1_test/outputs/stage2/mgf_ext_D65/strip_16/COVER.json. -/
def mhiE16 : Rat := R (312) 23

end Erdos993Lean.Analytic.MGF.Act1.Data
