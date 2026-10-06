import Erdos993Lean.Analytic.TailCert.Compute.Checker

/-!
# O3 ladder row 5: the sub-band `[1, 103/100]` at the Laplace parameter `t = 0` (lane A21)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A21.  Source: lane R4X's `LEAN/r4x/REACH_BELOW_52.md` §5(c)
(the N45 row of band 16), produced by lane O3R with the unmodified O3 checker (`LEAN/ladder/o3/rows.json`, row
5: interval `[1, 103/100]`, rate `ℓ = 881/2000` (0.4405), potential coefficient `a = 23/500`;
`runs/05_N45_b16_1_103-100/primary.stdout.json`, `ok: true`, `worst_lower` 4.6546828812437072021954237569489225427e-6).

`checkBand l0 l1 a ℓ 0 = true`: lane A10's verified cell checker (`Erdos993Lean/Analytic/TailCert/Compute/Checker.lean`,
its own adaptive cover; sound by `TailCert.checkBand_sound`, standard axioms) certifies `Tail.T3UNonneg λ 0 a ℓ` for
every `λ ∈ [1, 103/100]`.  The tilts `t > 0` of the sub-band are its parent band's (lane A10's `bandCertificates`).

Trust: the one `native_decide` of this module (`Lean.ofReduceBool`, the natively compiled library
`Erdos993LeanTailCertCompute`).
-/

namespace Erdos993Lean.Analytic.Ladder.O3

set_option profiler true
set_option profiler.threshold 500

/-- The `t = 0` certificate of the sub-band `[1, 103/100]` (`ℓ = 881/2000`, `a = 23/500`), by `native_decide`. -/
theorem row05 : TailCert.Compute.checkBand (1) (103/100) (23/500) (881/2000) 0 = true := by native_decide

end Erdos993Lean.Analytic.Ladder.O3
