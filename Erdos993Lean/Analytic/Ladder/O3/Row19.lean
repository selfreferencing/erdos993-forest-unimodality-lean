import Erdos993Lean.Analytic.TailCert.Compute.Checker

/-!
# O3 ladder row 19: the sub-band `[89/100, 23/25]` at the Laplace parameter `t = 0` (lane A21)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A21.  Source: lane R4X's `LEAN/r4x/REACH_BELOW_52.md` §5(c)
(the N44 row of band 13), produced by lane O3R with the unmodified O3 checker (`LEAN/ladder/o3/rows.json`, row
19: interval `[89/100, 23/25]`, rate `ℓ = 851/2000` (0.4255), potential coefficient `a = 41/1000`;
`runs/19_N44_b13_89-100_23-25/primary.stdout.json`, `ok: true`, `worst_lower` 1.0705746551312776167136839217449489114e-5).

`checkBand l0 l1 a ℓ 0 = true`: lane A10's verified cell checker (`Erdos993Lean/Analytic/TailCert/Compute/Checker.lean`,
its own adaptive cover; sound by `TailCert.checkBand_sound`, standard axioms) certifies `Tail.T3UNonneg λ 0 a ℓ` for
every `λ ∈ [89/100, 23/25]`.  The tilts `t > 0` of the sub-band are its parent band's (lane A10's `bandCertificates`).

Trust: the one `native_decide` of this module (`Lean.ofReduceBool`, the natively compiled library
`Erdos993LeanTailCertCompute`).
-/

namespace Erdos993Lean.Analytic.Ladder.O3

set_option profiler true
set_option profiler.threshold 500

/-- The `t = 0` certificate of the sub-band `[89/100, 23/25]` (`ℓ = 851/2000`, `a = 41/1000`), by `native_decide`. -/
theorem row19 : TailCert.Compute.checkBand (89/100) (23/25) (41/1000) (851/2000) 0 = true := by native_decide

end Erdos993Lean.Analytic.Ladder.O3
