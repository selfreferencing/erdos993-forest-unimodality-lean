import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: Below15, subinterval 15

The paper's activity rectangle is [22/25, 89/100], its exact mean
rectangle is [756/89, 1134/89]. The 6 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_boxes_below_50/subintervals_15_to_19_24_27/outputs/stage2/r15_existing/strip_15/box_000000.json`; sha256 `14a09093d95177f9b6190b7ff53d6170bc9f9f248ed6825dbf10fade241de65d`. -/
def boxBelow15_000 : MBox :=
  ⟨R (22) 47, R (89) 189, R (945) 89, R (1134) 89, R (2079) 178,
   R (8476054613) 500000000000, R (19029141681) 1000000000000,
   R (2432325355564934604061087866296751797375910049933) 42535295865117307932921825928971026432000000000000,
   R (0) 1, R (688672611) 1000000000000, R (1) 1, R (643386164719) 1000000000000,
   [R (463962987079) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 52⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_boxes_below_50/subintervals_15_to_19_24_27/outputs/stage2/r15_existing/strip_15/box_000001.json`; sha256 `63df30a1720e1d9f1b6c95b018009dcec6323c3c2b2bf5cc5dd65d30ce703def`. -/
def boxBelow15_001 : MBox :=
  ⟨R (22) 47, R (89) 189, R (1701) 178, R (945) 89, R (3591) 356,
   R (20950921089) 1000000000000, R (19163638331) 1000000000000,
   R (5583035734722179704870586513667237242102259753397) 85070591730234615865843651857942052864000000000000,
   R (6675127) 50000000000, R (800614643) 1000000000000, R (1) 1, R (342544678061) 500000000000,
   [R (235839778733) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 48⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_boxes_below_50/subintervals_15_to_19_24_27/outputs/stage2/r15_existing/strip_15/box_000002.json`; sha256 `46188be89c27718d28d18014aafde649b4d320bb677cce61fbf5bdb41c29d66d`. -/
def boxBelow15_002 : MBox :=
  ⟨R (22) 47, R (89) 189, R (756) 89, R (1701) 178, R (3213) 356,
   R (12303066323) 500000000000, R (6061871843) 250000000000,
   R (1566331295765746258127058335280680663203127642159) 21267647932558653966460912964485513216000000000000,
   R (0) 1, R (99269553) 100000000000, R (1) 1, R (157608940259) 250000000000,
   [R (236176743151) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 44⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_boxes_below_50/subintervals_15_to_19_24_27/outputs/stage2/r15_existing/strip_15/box_000003.json`; sha256 `affd7b96fed762a85388589f4f918f5cbf4e747e9a2c0b6293dc088830b13bb6`. -/
def boxBelow15_003 : MBox :=
  ⟨R (22) 47, R (89) 189, R (2835) 356, R (756) 89, R (5859) 712,
   R (15340486827) 500000000000, R (34654482543) 1000000000000,
   R (7141446127055970674087303290361000210477659232339) 85070591730234615865843651857942052864000000000000,
   R (-262536903) 100000000000, R (738780427) 1000000000000, R (1) 1, R (537876527019) 1000000000000,
   [R (991068554219) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 80⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_boxes_below_50/subintervals_15_to_19_24_27/outputs/stage2/r15_existing/strip_15/box_000004.json`; sha256 `bc34016e35f379fd3ea646cd82e57cf2b8f76ff63094d3972e8c0c897783d7f8`. -/
def boxBelow15_004 : MBox :=
  ⟨R (22) 47, R (89) 189, R (5481) 712, R (2835) 356, R (11151) 1424,
   R (3766501971) 100000000000, R (3799643221) 125000000000,
   R (985595535363019751208584478635667697938067218741) 10633823966279326983230456482242756608000000000000,
   R (-3056147837) 500000000000, R (32651549) 250000000000, R (1) 1, R (127161276749) 200000000000,
   [R (8534617431) 8000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 144⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_boxes_below_50/subintervals_15_to_19_24_27/outputs/stage2/r15_existing/strip_15/box_000005.json`; sha256 `b0ffd8b3ac0dfbcd440675419012849bf4df3590b51e7b5d9268ec23656b3cb8`. -/
def boxBelow15_005 : MBox :=
  ⟨R (22) 47, R (89) 189, R (1323) 178, R (5481) 712, R (10773) 1424,
   R (40933336399) 1000000000000, R (2102226563) 100000000000,
   R (1752518396158376543933620338085787331681652752133) 17014118346046923173168730371588410572800000000000,
   R (-237654941) 40000000000, R (372453679) 500000000000, R (1) 1, R (382441333859) 500000000000,
   [R (16312479659) 15625000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 72⟩
/-- Lemma 5.4: the exact 6 boxes of Below15. -/
def boxesBelow15 : List MBox := [
  boxBelow15_000,
  boxBelow15_001,
  boxBelow15_002,
  boxBelow15_003,
  boxBelow15_004,
  boxBelow15_005
]

/-- Lemma 5.4: the exact cover chains of Below15. -/
def slabsBelow15 : List Atlas.Slab := [
  ⟨R (22) 47, R (89) 189, [5, 4, 3, 2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloBelow15 : Rat := R (756) 89

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiBelow15 : Rat := R (1134) 89

end Erdos993Lean.Analytic.V21.Data
