import Erdos993Lean.Analytic.MGF.Act1.Pieces

/-!
# Lane B L4a: E18, piece 18, activity [23/25, 93/100]

Source: `LEAN/certfree/act1_test/outputs/stage2/mgf_ext_D65/strip_18` and `certfree/act1_test/REPORT.md`,
refereed in `certfree/referee_act1_test/REFEREE.md` (1 October 2026).
The exact rectangle is q ∈ [23/48, 93/193], mean ∈ [386/31, 637/48].
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

/-- Exact source `certfree/act1_test/outputs/stage2/mgf_ext_D65/strip_18/box_000000.json`; sha256 `cebca0f753537d74945bd8cbba5b8dcff9cee45c7adeee39bd4cb22973c79d12`. -/
def boxE18_000 : MBox :=
  ⟨R (23) 48, R (93) 193, R (386) 31, R (637) 48, R (38275) 2976,
   R (5589699639) 500000000000, R (12136754439) 1000000000000,
   R (3578143219535944955162578136648149188524552288909) 85070591730234615865843651857942052864000000000000,
   R (1453664767) 1000000000000, R (107366883) 200000000000, R (1) 1, R (346448786449) 500000000000,
   [R (47614059377) 50000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 112⟩
/-- The 1 exact boxes of E18. -/
def boxesE18 : List MBox := [
  boxE18_000
]

/-- The exact source cover of E18. -/
def slabsE18 : List Atlas.Slab := [
  ⟨R (23) 48, R (93) 193, [0]⟩
]

/-- Exact lower mean edge from certfree/act1_test/outputs/stage2/mgf_ext_D65/strip_18/COVER.json. -/
def mloE18 : Rat := R (386) 31

/-- Exact upper mean edge from certfree/act1_test/outputs/stage2/mgf_ext_D65/strip_18/COVER.json. -/
def mhiE18 : Rat := R (637) 48

end Erdos993Lean.Analytic.MGF.Act1.Data
