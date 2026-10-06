import Erdos993Lean.Analytic.TailCert.Compute.Checker

/-!
# O3 ladder row 12: the sub-band `[27/20, 7/5]` at the Laplace parameter `t = 0` (lane A21)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A21.  Source: lane R4X's `LEAN/r4x/REACH_BELOW_52.md` §5(c)
(the N45 row of band 23), produced by lane O3R with the unmodified O3 checker (`LEAN/ladder/o3/rows.json`, row
12: interval `[27/20, 7/5]`, rate `ℓ = 37/80` (0.4625), potential coefficient `a = 81/1000`;
`runs/12_N45_b23_27-20_7-5/primary.stdout.json`, `ok: true`, `worst_lower` 1.4376842166409783479635182250025343366e-6).

`checkBand l0 l1 a ℓ 0 = true`: lane A10's verified cell checker (`Erdos993Lean/Analytic/TailCert/Compute/Checker.lean`,
its own adaptive cover; sound by `TailCert.checkBand_sound`, standard axioms) certifies `Tail.T3UNonneg λ 0 a ℓ` for
every `λ ∈ [27/20, 7/5]`.  The tilts `t > 0` of the sub-band are its parent band's (lane A10's `bandCertificates`).

Trust: the one `native_decide` of this module (`Lean.ofReduceBool`, the natively compiled library
`Erdos993LeanTailCertCompute`).
-/

namespace Erdos993Lean.Analytic.Ladder.O3

set_option profiler true
set_option profiler.threshold 500

/-- The `t = 0` certificate of the sub-band `[27/20, 7/5]` (`ℓ = 37/80`, `a = 81/1000`), by `native_decide`. -/
theorem row12 : TailCert.Compute.checkBand (27/20) (7/5) (81/1000) (37/80) 0 = true := by native_decide

end Erdos993Lean.Analytic.Ladder.O3
