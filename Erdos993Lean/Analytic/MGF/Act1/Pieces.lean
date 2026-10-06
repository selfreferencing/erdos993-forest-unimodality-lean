import Erdos993Lean.Analytic.MGF.Pieces

/-!
# Lane B L4a: near-one MGF certificate parameters at D = 6/5

Source: LEAN/certfree/act1_test/REPORT.md and referee_act1_test/REFEREE.md.
The existing piece's forest-payment cap θ, activity edges and certified MGF
rates are preserved verbatim. Only this separate data family's D is 6/5.
No old data, theorem, assembly or campaign state is changed by these modules.
-/

namespace Erdos993Lean.Analytic.MGF.Act1

/-- Source: certfree/act1_test/REPORT.md, passing lists at D = 6/5. -/
def pieceD65 (p : Nat) : MPiece := { piece44 p with D := mkRat 6 5 }

end Erdos993Lean.Analytic.MGF.Act1
