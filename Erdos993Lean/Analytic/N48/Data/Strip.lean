import Erdos993Lean.Analytic.N48.Data.P00
import Erdos993Lean.Analytic.N48.Data.P01
import Erdos993Lean.Analytic.N48.Data.P02
import Erdos993Lean.Analytic.N48.Data.P03
import Erdos993Lean.Analytic.N48.Data.P04
import Erdos993Lean.Analytic.N48.Data.P05
import Erdos993Lean.Analytic.N48.Data.P06
import Erdos993Lean.Analytic.N48.Data.P07
import Erdos993Lean.Analytic.N48.Data.P08
import Erdos993Lean.Analytic.N48.Data.P09
import Erdos993Lean.Analytic.N48.Data.P10
import Erdos993Lean.Analytic.N48.Data.P11
import Erdos993Lean.Analytic.N48.Data.P12
import Erdos993Lean.Analytic.N48.Data.P15
import Erdos993Lean.Analytic.N48.Data.P16
import Erdos993Lean.Analytic.N48.Data.P17
import Erdos993Lean.Analytic.N48.Data.P18
import Erdos993Lean.Analytic.N48.Data.P19
import Erdos993Lean.Analytic.N48.Data.P20
import Erdos993Lean.Analytic.N48.Data.P21
import Erdos993Lean.Analytic.N48.Data.P22
import Erdos993Lean.Analytic.N48.Data.P23
import Erdos993Lean.Analytic.N48.Data.P24
import Erdos993Lean.Analytic.N48.Data.P25
import Erdos993Lean.Analytic.N48.Data.P26
import Erdos993Lean.Analytic.N48.Data.P27
import Erdos993Lean.Analytic.N48.Data.P28
import Erdos993Lean.Analytic.N48.Data.P29
import Erdos993Lean.Analytic.N48.Data.P30
import Erdos993Lean.Analytic.N48.Data.P31
import Erdos993Lean.Analytic.N48.Data.P32

/-!
# The n ≥ 48 strip atlas: index (31 pieces)

Piece `p` (0-based) of the n ≥ 48 strip: its boxes and its cover slabs (generated data, see the piece modules);
empty on pieces 13 and 14, whose floor does not drop.
-/

namespace Erdos993Lean.Analytic.N48.Data

open Erdos993Lean.Analytic.Atlas

/-- The boxes of piece `p` (0-based) of the n ≥ 48 strip. -/
def strip48Boxes : Nat → List Box
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
  | 15 => boxesP15
  | 16 => boxesP16
  | 17 => boxesP17
  | 18 => boxesP18
  | 19 => boxesP19
  | 20 => boxesP20
  | 21 => boxesP21
  | 22 => boxesP22
  | 23 => boxesP23
  | 24 => boxesP24
  | 25 => boxesP25
  | 26 => boxesP26
  | 27 => boxesP27
  | 28 => boxesP28
  | 29 => boxesP29
  | 30 => boxesP30
  | 31 => boxesP31
  | 32 => boxesP32
  | _ => []

/-- The cover slabs of piece `p` (0-based) of the n ≥ 48 strip. -/
def strip48Slabs : Nat → List Slab
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
  | 15 => slabsP15
  | 16 => slabsP16
  | 17 => slabsP17
  | 18 => slabsP18
  | 19 => slabsP19
  | 20 => slabsP20
  | 21 => slabsP21
  | 22 => slabsP22
  | 23 => slabsP23
  | 24 => slabsP24
  | 25 => slabsP25
  | 26 => slabsP26
  | 27 => slabsP27
  | 28 => slabsP28
  | 29 => slabsP29
  | 30 => slabsP30
  | 31 => slabsP31
  | 32 => slabsP32
  | _ => []

end Erdos993Lean.Analytic.N48.Data
