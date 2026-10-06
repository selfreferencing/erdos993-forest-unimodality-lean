import Erdos993Lean.Analytic.N52.Data.S01
import Erdos993Lean.Analytic.N52.Data.S02
import Erdos993Lean.Analytic.N52.Data.S03
import Erdos993Lean.Analytic.N52.Data.S04
import Erdos993Lean.Analytic.N52.Data.S05
import Erdos993Lean.Analytic.N52.Data.S06
import Erdos993Lean.Analytic.N52.Data.S07
import Erdos993Lean.Analytic.N52.Data.S08
import Erdos993Lean.Analytic.N52.Data.S09
import Erdos993Lean.Analytic.N52.Data.S10
import Erdos993Lean.Analytic.N52.Data.S11
import Erdos993Lean.Analytic.N52.Data.S12
import Erdos993Lean.Analytic.N52.Data.S13
import Erdos993Lean.Analytic.N52.Data.S14
import Erdos993Lean.Analytic.N52.Data.S15
import Erdos993Lean.Analytic.N52.Data.S16
import Erdos993Lean.Analytic.N52.Data.S17
import Erdos993Lean.Analytic.N52.Data.S18
import Erdos993Lean.Analytic.N52.Data.S19
import Erdos993Lean.Analytic.N52.Data.S20
import Erdos993Lean.Analytic.N52.Data.S21
import Erdos993Lean.Analytic.N52.Data.S22
import Erdos993Lean.Analytic.N52.Data.S23
import Erdos993Lean.Analytic.N52.Data.S24
import Erdos993Lean.Analytic.N52.Data.S25
import Erdos993Lean.Analytic.N52.Data.S26
import Erdos993Lean.Analytic.N52.Data.S27
import Erdos993Lean.Analytic.N52.Data.S28
import Erdos993Lean.Analytic.N52.Data.S29
import Erdos993Lean.Analytic.N52.Data.S30

/-!
# The n ≥ 52 strip atlas: index (bands 1–30)

Band `i` (0-based) of the strip: its boxes and its cover slabs (generated data, see the band modules).
-/

namespace Erdos993Lean.Analytic.N52.Data

open Erdos993Lean.Analytic.Atlas

/-- The boxes of band `i` (0-based) of the strip. -/
def stripBoxes : Nat → List Box
  | 0 => boxesS01
  | 1 => boxesS02
  | 2 => boxesS03
  | 3 => boxesS04
  | 4 => boxesS05
  | 5 => boxesS06
  | 6 => boxesS07
  | 7 => boxesS08
  | 8 => boxesS09
  | 9 => boxesS10
  | 10 => boxesS11
  | 11 => boxesS12
  | 12 => boxesS13
  | 13 => boxesS14
  | 14 => boxesS15
  | 15 => boxesS16
  | 16 => boxesS17
  | 17 => boxesS18
  | 18 => boxesS19
  | 19 => boxesS20
  | 20 => boxesS21
  | 21 => boxesS22
  | 22 => boxesS23
  | 23 => boxesS24
  | 24 => boxesS25
  | 25 => boxesS26
  | 26 => boxesS27
  | 27 => boxesS28
  | 28 => boxesS29
  | 29 => boxesS30
  | _ => []

/-- The cover slabs of band `i` (0-based) of the strip. -/
def stripSlabs : Nat → List Slab
  | 0 => slabsS01
  | 1 => slabsS02
  | 2 => slabsS03
  | 3 => slabsS04
  | 4 => slabsS05
  | 5 => slabsS06
  | 6 => slabsS07
  | 7 => slabsS08
  | 8 => slabsS09
  | 9 => slabsS10
  | 10 => slabsS11
  | 11 => slabsS12
  | 12 => slabsS13
  | 13 => slabsS14
  | 14 => slabsS15
  | 15 => slabsS16
  | 16 => slabsS17
  | 17 => slabsS18
  | 18 => slabsS19
  | 19 => slabsS20
  | 20 => slabsS21
  | 21 => slabsS22
  | 22 => slabsS23
  | 23 => slabsS24
  | 24 => slabsS25
  | 25 => slabsS26
  | 26 => slabsS27
  | 27 => slabsS28
  | 28 => slabsS29
  | 29 => slabsS30
  | _ => []

end Erdos993Lean.Analytic.N52.Data
