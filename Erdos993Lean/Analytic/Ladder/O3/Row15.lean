import Erdos993Lean.Analytic.TailCert.Compute.Checker

/-!
# O3 ladder row 15: the sub-band `[37/20, 19/10]` at the Laplace parameter `t = 0` (lane A21)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A21.  Source: lane R4X's `LEAN/r4x/REACH_BELOW_52.md` §5(c)
(the N45 row of band 27), produced by lane O3R with the unmodified O3 checker (`LEAN/ladder/o3/rows.json`, row
15: interval `[37/20, 19/10]`, rate `ℓ = 47/100` (0.47), potential coefficient `a = 19/200`;
`runs/15_N45_b27_37-20_19-10/primary.stdout.json`, `ok: true`, `worst_lower` 9.7467201594063822338575033328757894903e-7).

`checkBand l0 l1 a ℓ 0 = true`: lane A10's verified cell checker (`Erdos993Lean/Analytic/TailCert/Compute/Checker.lean`,
its own adaptive cover; sound by `TailCert.checkBand_sound`, standard axioms) certifies `Tail.T3UNonneg λ 0 a ℓ` for
every `λ ∈ [37/20, 19/10]`.  The tilts `t > 0` of the sub-band are its parent band's (lane A10's `bandCertificates`).

Trust: the one `native_decide` of this module (`Lean.ofReduceBool`, the natively compiled library
`Erdos993LeanTailCertCompute`).
-/

namespace Erdos993Lean.Analytic.Ladder.O3

set_option profiler true
set_option profiler.threshold 500

/-- The `t = 0` certificate of the sub-band `[37/20, 19/10]` (`ℓ = 47/100`, `a = 19/200`), by `native_decide`. -/
theorem row15 : TailCert.Compute.checkBand (37/20) (19/10) (19/200) (47/100) 0 = true := by native_decide

end Erdos993Lean.Analytic.Ladder.O3
