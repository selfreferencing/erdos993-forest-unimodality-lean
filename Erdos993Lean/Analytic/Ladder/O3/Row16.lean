import Erdos993Lean.Analytic.TailCert.Compute.Checker

/-!
# O3 ladder row 16: the sub-band `[19/10, 39/20]` at the Laplace parameter `t = 0` (lane A21)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A21.  Source: lane R4X's `LEAN/r4x/REACH_BELOW_52.md` §5(c)
(the N45 row of band 28), produced by lane O3R with the unmodified O3 checker (`LEAN/ladder/o3/rows.json`, row
16: interval `[19/10, 39/20]`, rate `ℓ = 47/100` (0.47), potential coefficient `a = 27/250`;
`runs/16_N45_b28_19-10_39-20/primary.stdout.json`, `ok: true`, `worst_lower` 1.0627492487967679551091506596874504244e-5).

`checkBand l0 l1 a ℓ 0 = true`: lane A10's verified cell checker (`Erdos993Lean/Analytic/TailCert/Compute/Checker.lean`,
its own adaptive cover; sound by `TailCert.checkBand_sound`, standard axioms) certifies `Tail.T3UNonneg λ 0 a ℓ` for
every `λ ∈ [19/10, 39/20]`.  The tilts `t > 0` of the sub-band are its parent band's (lane A10's `bandCertificates`).

Trust: the one `native_decide` of this module (`Lean.ofReduceBool`, the natively compiled library
`Erdos993LeanTailCertCompute`).
-/

namespace Erdos993Lean.Analytic.Ladder.O3

set_option profiler true
set_option profiler.threshold 500

/-- The `t = 0` certificate of the sub-band `[19/10, 39/20]` (`ℓ = 47/100`, `a = 27/250`), by `native_decide`. -/
theorem row16 : TailCert.Compute.checkBand (19/10) (39/20) (27/250) (47/100) 0 = true := by native_decide

end Erdos993Lean.Analytic.Ladder.O3
