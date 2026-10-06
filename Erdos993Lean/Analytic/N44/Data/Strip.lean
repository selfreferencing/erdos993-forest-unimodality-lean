import Erdos993Lean.Analytic.N44.Data.P00
import Erdos993Lean.Analytic.N44.Data.P01
import Erdos993Lean.Analytic.N44.Data.P02
import Erdos993Lean.Analytic.N44.Data.P03
import Erdos993Lean.Analytic.N44.Data.P04
import Erdos993Lean.Analytic.N44.Data.P05
import Erdos993Lean.Analytic.N44.Data.P06
import Erdos993Lean.Analytic.N44.Data.P07
import Erdos993Lean.Analytic.N44.Data.P08
import Erdos993Lean.Analytic.N44.Data.P09
import Erdos993Lean.Analytic.N44.Data.P10
import Erdos993Lean.Analytic.N44.Data.P11
import Erdos993Lean.Analytic.N44.Data.P12
import Erdos993Lean.Analytic.N44.Data.P13
import Erdos993Lean.Analytic.N44.Data.P14
import Erdos993Lean.Analytic.N44.Data.P15
import Erdos993Lean.Analytic.N44.Data.P16
import Erdos993Lean.Analytic.N44.Data.P17
import Erdos993Lean.Analytic.N44.Data.P18
import Erdos993Lean.Analytic.N44.Data.P31
import Erdos993Lean.Analytic.N44.Data.P32
import Erdos993Lean.Analytic.N44.Data.P33
import Erdos993Lean.Analytic.N44.Data.P34
import Erdos993Lean.Analytic.N44.Data.P35
import Erdos993Lean.Analytic.N44.Data.P43
import Erdos993Lean.Analytic.N44.Data.P44
import Erdos993Lean.Analytic.N44.Data.P54

/-!
# The n ≥ 44 strip atlas: index (27 pieces)

Piece `p` (0-based) of the n ≥ 44 strip: its boxes and its cover slabs (generated data, see the piece modules);
empty on the pieces whose floor does not drop.
-/

namespace Erdos993Lean.Analytic.N44.Data

open Erdos993Lean.Analytic.Atlas

/-- The boxes of piece `p` (0-based) of the n ≥ 44 strip. -/
def strip44Boxes : Nat → List Box
  | 0 => boxesP00
  | 1 => boxesP01
  | 2 => boxesP02
  | 3 => boxesP03
  | 4 => boxesP04
  | 5 => boxesP05
  | 6 => boxesP06
  | 7 => boxesP07
  | 8 => boxesP08
  | 9 => boxesP09
  | 10 => boxesP10
  | 11 => boxesP11
  | 12 => boxesP12
  | 13 => boxesP13
  | 14 => boxesP14
  | 15 => boxesP15
  | 16 => boxesP16
  | 17 => boxesP17
  | 18 => boxesP18
  | 31 => boxesP31
  | 32 => boxesP32
  | 33 => boxesP33
  | 34 => boxesP34
  | 35 => boxesP35
  | 43 => boxesP43
  | 44 => boxesP44
  | 54 => boxesP54
  | _ => []

/-- The cover slabs of piece `p` (0-based) of the n ≥ 44 strip. -/
def strip44Slabs : Nat → List Slab
  | 0 => slabsP00
  | 1 => slabsP01
  | 2 => slabsP02
  | 3 => slabsP03
  | 4 => slabsP04
  | 5 => slabsP05
  | 6 => slabsP06
  | 7 => slabsP07
  | 8 => slabsP08
  | 9 => slabsP09
  | 10 => slabsP10
  | 11 => slabsP11
  | 12 => slabsP12
  | 13 => slabsP13
  | 14 => slabsP14
  | 15 => slabsP15
  | 16 => slabsP16
  | 17 => slabsP17
  | 18 => slabsP18
  | 31 => slabsP31
  | 32 => slabsP32
  | 33 => slabsP33
  | 34 => slabsP34
  | 35 => slabsP35
  | 43 => slabsP43
  | 44 => slabsP44
  | 54 => slabsP54
  | _ => []

end Erdos993Lean.Analytic.N44.Data
