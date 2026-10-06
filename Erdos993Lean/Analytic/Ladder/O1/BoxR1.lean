import Erdos993Lean.Analytic.Reserve.Cert.Compute.Cell
import Erdos993Lean.Analytic.Ladder.O1.TrieR1

/-!
# The finite box of the O1R row 1 checked natively (lane A21)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A21.  `checkBand (8/5) (33/20) (7/5) (23/50) 13 trieR1 = true`:
lane A12's cell checker (`Erdos993Lean/Analytic/Reserve/Cert/Compute/Cell.lean`, sound by `Cert.boxOK_of_check`)
certifies lane O1R's 85,150 cells of row 1 (`λ ∈ [8/5, 33/20]`, `D = 7/5`, `α = 23q/50`, `β = 0`, `γ = λ(3 + λ)/13`, the
B+, extended past 8/5 family; certificate `LEAN/ladder/o1/o1r_reserve_row_1.json`, SHA-256 `2c32d023…`,
CONFIRMED by the referee's independent replay `LEAN/referee/ladder_replay/REVIEW_LADDER_REPLAY.md` §3) and their cover
of the box `T ∈ [0, 6]`, `r ∈ [0, 1]`.  The trie string `trieR1` (`Ladder/O1/TrieR1.lean`) is the producer's Lean data
module verbatim; the referee decoded it to exactly the certificate's cells (`lean_data_custody.py`).

Trust: the one `native_decide` of this module (`Lean.ofReduceBool`: the Lean compiler, here including the natively
compiled library `Erdos993LeanReserveCertCompute` and lane A10's `Erdos993LeanTailCertCompute`).
-/

namespace Erdos993Lean.Analytic.Ladder.O1

open Erdos993Lean.Analytic.Reserve.Cert.Compute

set_option profiler true
set_option profiler.threshold 500

/-- The finite box of the O1R row 1 (`λ ∈ [8/5, 33/20]`, `D = 7/5`): the 85,150 cells pass the cell checker and cover the
box, by `native_decide`. -/
theorem box_R1 : checkBand (8/5) (33/20) (7/5) (23/50) 13 trieR1 = true := by native_decide

end Erdos993Lean.Analytic.Ladder.O1
