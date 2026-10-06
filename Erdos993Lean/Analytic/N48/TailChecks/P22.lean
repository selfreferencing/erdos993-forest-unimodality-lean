import Erdos993Lean.Analytic.TailCert.Compute.Checker

/-!
# O3 at `n ≥ 48`: the sub-band row `[13/10, 27/20]` at the Laplace parameter `t = 0` (lane A20)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A20.  Source: lane R4X's `LEAN/r4x/REACH_BELOW_52.md` §5(c)
(the N = 48 row of band 23), produced by lane O3R with the unmodified O3 checker (`LEAN/ladder/o3/rows.json`, row
1: interval `[13/10, 27/20]`, rate `ℓ = 23/50` (0.46), potential coefficient `a = 7/100`; `runs/<row>/primary.stdout.json`).

`checkBand l0 l1 a ℓ 0 = true`: lane A10's verified cell checker (`Erdos993Lean/Analytic/TailCert/Compute/Checker.lean`,
its own adaptive cover; sound by `TailCert.checkBand_sound`, standard axioms) certifies `Tail.T3UNonneg λ 0 a ℓ` for
every `λ ∈ [13/10, 27/20]`.  The tilts `t > 0` of this piece are its parent band's (lane A10's `bandCertificates`).

Trust: the one `native_decide` of this module (`Lean.ofReduceBool`, the natively compiled library
`Erdos993LeanTailCertCompute`).
-/

namespace Erdos993Lean.Analytic.N48.TailChecks

/-- The t = 0 certificate of the piece `[13/10, 27/20]` (`ℓ = 23/50`, `a = 7/100`), by `native_decide`. -/
theorem rowP22 : TailCert.Compute.checkBand (13/10) (27/20) (7/100) (23/50) 0 = true := by native_decide

end Erdos993Lean.Analytic.N48.TailChecks
