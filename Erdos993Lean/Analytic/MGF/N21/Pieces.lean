import Erdos993Lean.Analytic.MGF.Pieces

/-!
# The pieces of the MGF + two-sided atlas at rung 21: the N44 caps with lane O1R21's two O1 rows (lane A24)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A24.  Sources: lane R2X's `LEAN/r2x/REACH_BELOW_27.md` §2a (the two
strips that fail at `N = 21..24` with the N44 caps and the `D` they need), lane O1R21's rows (`LEAN/ladder/o1_N21/REPORT.md`:
row A `D = 21/20` on `[1, 103/100]` = piece 24, row B `D = 23/20` on `[21/20, 107/100]` = piece 27; in Lean
`Ladder/O1/RowsN21.lean`), this lane's `MGF/N25/Caps.lean` (`pieceCaps`).  This file imports only Lean's core (the checker
and lane A21's parameter tables), so that the rung-21 data and check modules stay light; `MGF/N21/Caps.lean` proves
`piece21 p = pieceCaps theta44tab D21tab p` and the O1 input at these caps (`varianceBound21_all`).

* `D21tab p`: the O1 cap of piece `p` at rung 21 — `D44` except `21/20` on piece 24 and `23/20` on piece 27.
* `piece21 p : MPiece`: `piece44 p` with the O1 cap `D21tab p` (the O2 cap, the tilts and the edges unchanged).
-/

namespace Erdos993Lean.Analytic.MGF.N21

/-- The O1 caps at rung 21: the N44 table except on pieces 24 (`[1, 103/100]`: `D = 21/20`, lane O1R21's row A) and 27
(`[21/20, 107/100]`: `D = 23/20`, row B). -/
def D21tab (p : Nat) : Rat :=
  if p = 24 then mkRat 21 20 else if p = 27 then mkRat 23 20 else N44.Data.D44.getD p 0

/-- **The checker's piece `p` at rung 21**: `piece44 p` with the O1 cap `D21tab p`. -/
def piece21 (p : Nat) : MPiece :=
  ⟨N44.Data.theta44.getD p 0, D21tab p, tiltsQ44 p, N44.Data.pieceLo.getD p 0, N44.Data.pieceHi.getD p 0⟩

end Erdos993Lean.Analytic.MGF.N21
