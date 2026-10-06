import Erdos993Lean.Analytic.TailCert.Compute.Checker

/-!
# O3 ladder row 24: the sub-band `[24/25, 97/100]` at the Laplace parameter `t = 0` (lane A21)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A21.  Source: lane R4X's `LEAN/r4x/REACH_BELOW_52.md` §5(c)
(the N44 row of band 15), produced by lane O3R with the unmodified O3 checker (`LEAN/ladder/o3/rows.json`, row
24: interval `[24/25, 97/100]`, rate `ℓ = 441/1000` (0.441), potential coefficient `a = 1/20`;
`runs/24_N44_b15_24-25_97-100/primary.stdout.json`, `ok: true`, `worst_lower` 6.7224383258829569439971958768731967359e-7).

`checkBand l0 l1 a ℓ 0 = true`: lane A10's verified cell checker (`Erdos993Lean/Analytic/TailCert/Compute/Checker.lean`,
its own adaptive cover; sound by `TailCert.checkBand_sound`, standard axioms) certifies `Tail.T3UNonneg λ 0 a ℓ` for
every `λ ∈ [24/25, 97/100]`.  The tilts `t > 0` of the sub-band are its parent band's (lane A10's `bandCertificates`).

Trust: the one `native_decide` of this module (`Lean.ofReduceBool`, the natively compiled library
`Erdos993LeanTailCertCompute`).
-/

namespace Erdos993Lean.Analytic.Ladder.O3

set_option profiler true
set_option profiler.threshold 500

/-- The `t = 0` certificate of the sub-band `[24/25, 97/100]` (`ℓ = 441/1000`, `a = 1/20`), by `native_decide`. -/
theorem row24 : TailCert.Compute.checkBand (24/25) (97/100) (1/20) (441/1000) 0 = true := by native_decide

end Erdos993Lean.Analytic.Ladder.O3
