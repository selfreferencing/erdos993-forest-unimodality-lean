import Erdos993Lean.Analytic.N45.Data.P13
import Erdos993Lean.Analytic.N45.Data.P14
import Erdos993Lean.Analytic.N45.Data.P15
import Erdos993Lean.Analytic.N45.Data.P16
import Erdos993Lean.Analytic.N45.Data.P17
import Erdos993Lean.Analytic.N45.Data.P18
import Erdos993Lean.Analytic.N45.Data.P19
import Erdos993Lean.Analytic.N45.Data.P20
import Erdos993Lean.Analytic.N45.Data.P21
import Erdos993Lean.Analytic.N45.Data.P24
import Erdos993Lean.Analytic.N45.Data.P25
import Erdos993Lean.Analytic.N45.Data.P26
import Erdos993Lean.Analytic.N45.Data.P27
import Erdos993Lean.Analytic.N45.Data.P28
import Erdos993Lean.Analytic.N45.Data.P29
import Erdos993Lean.Analytic.N45.Data.P30
import Erdos993Lean.Analytic.N45.Data.P31
import Erdos993Lean.Analytic.N45.Data.P32
import Erdos993Lean.Analytic.N45.Data.P33
import Erdos993Lean.Analytic.N45.Data.P35
import Erdos993Lean.Analytic.N45.Data.P36
import Erdos993Lean.Analytic.N45.Data.P37
import Erdos993Lean.Analytic.N45.Data.P38
import Erdos993Lean.Analytic.N45.Data.P39
import Erdos993Lean.Analytic.N45.Data.P40
import Erdos993Lean.Analytic.N45.Data.P41
import Erdos993Lean.Analytic.N45.Data.P42
import Erdos993Lean.Analytic.N45.Data.P43
import Erdos993Lean.Analytic.N45.Data.P44
import Erdos993Lean.Analytic.N45.Data.P45

/-!
# The n ≥ 45 strip atlas: index (30 pieces)

Piece `p` (0-based) of the n ≥ 45 strip: its boxes and its cover slabs (generated data, see the piece modules);
empty on the pieces whose floor does not drop.
-/

namespace Erdos993Lean.Analytic.N45.Data

open Erdos993Lean.Analytic.Atlas

/-- The boxes of piece `p` (0-based) of the n ≥ 45 strip. -/
def strip45Boxes : Nat → List Box
  | 13 => boxesP13
  | 14 => boxesP14
  | 15 => boxesP15
  | 16 => boxesP16
  | 17 => boxesP17
  | 18 => boxesP18
  | 19 => boxesP19
  | 20 => boxesP20
  | 21 => boxesP21
  | 24 => boxesP24
  | 25 => boxesP25
  | 26 => boxesP26
  | 27 => boxesP27
  | 28 => boxesP28
  | 29 => boxesP29
  | 30 => boxesP30
  | 31 => boxesP31
  | 32 => boxesP32
  | 33 => boxesP33
  | 35 => boxesP35
  | 36 => boxesP36
  | 37 => boxesP37
  | 38 => boxesP38
  | 39 => boxesP39
  | 40 => boxesP40
  | 41 => boxesP41
  | 42 => boxesP42
  | 43 => boxesP43
  | 44 => boxesP44
  | 45 => boxesP45
  | _ => []

/-- The cover slabs of piece `p` (0-based) of the n ≥ 45 strip. -/
def strip45Slabs : Nat → List Slab
  | 13 => slabsP13
  | 14 => slabsP14
  | 15 => slabsP15
  | 16 => slabsP16
  | 17 => slabsP17
  | 18 => slabsP18
  | 19 => slabsP19
  | 20 => slabsP20
  | 21 => slabsP21
  | 24 => slabsP24
  | 25 => slabsP25
  | 26 => slabsP26
  | 27 => slabsP27
  | 28 => slabsP28
  | 29 => slabsP29
  | 30 => slabsP30
  | 31 => slabsP31
  | 32 => slabsP32
  | 33 => slabsP33
  | 35 => slabsP35
  | 36 => slabsP36
  | 37 => slabsP37
  | 38 => slabsP38
  | 39 => slabsP39
  | 40 => slabsP40
  | 41 => slabsP41
  | 42 => slabsP42
  | 43 => slabsP43
  | 44 => slabsP44
  | 45 => slabsP45
  | _ => []

end Erdos993Lean.Analytic.N45.Data
