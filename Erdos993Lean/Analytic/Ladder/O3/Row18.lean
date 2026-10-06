import Erdos993Lean.Analytic.TailCert.Compute.Checker

/-!
# O3 ladder row 18: the sub-band `[87/100, 22/25]` at the Laplace parameter `t = 0` (lane A21)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A21.  Source: lane R4X's `LEAN/r4x/REACH_BELOW_52.md` §5(c)
(the N44 row of band 12), produced by lane O3R with the unmodified O3 checker (`LEAN/ladder/o3/rows.json`, row
18: interval `[87/100, 22/25]`, rate `ℓ = 171/400` (0.4275), potential coefficient `a = 1/25`;
`runs/18_N44_b12_87-100_22-25/primary.stdout.json`, `ok: true`, `worst_lower` 2.4883306029885569587348519897545699041e-7).

`checkBand l0 l1 a ℓ 0 = true`: lane A10's verified cell checker (`Erdos993Lean/Analytic/TailCert/Compute/Checker.lean`,
its own adaptive cover; sound by `TailCert.checkBand_sound`, standard axioms) certifies `Tail.T3UNonneg λ 0 a ℓ` for
every `λ ∈ [87/100, 22/25]`.  The tilts `t > 0` of the sub-band are its parent band's (lane A10's `bandCertificates`).

Trust: the one `native_decide` of this module (`Lean.ofReduceBool`, the natively compiled library
`Erdos993LeanTailCertCompute`).
-/

namespace Erdos993Lean.Analytic.Ladder.O3

set_option profiler true
set_option profiler.threshold 500

/-- The `t = 0` certificate of the sub-band `[87/100, 22/25]` (`ℓ = 171/400`, `a = 1/25`), by `native_decide`. -/
theorem row18 : TailCert.Compute.checkBand (87/100) (22/25) (1/25) (171/400) 0 = true := by native_decide

end Erdos993Lean.Analytic.Ladder.O3
