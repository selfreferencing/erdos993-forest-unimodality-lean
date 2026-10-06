import Erdos993Lean.Analytic.TailCert.Compute.Checker

/-!
# O3 at `n ≥ 48`: the sub-band row `[33/20, 17/10]` at the Laplace parameter `t = 0` (lane A20)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A20.  Source: lane R4X's `LEAN/r4x/REACH_BELOW_52.md` §5(c)
(the N = 48 row of band 26), produced by lane O3R with the unmodified O3 checker (`LEAN/ladder/o3/rows.json`, row
3: interval `[33/20, 17/10]`, rate `ℓ = 47/100` (0.47), potential coefficient `a = 97/1000`; `runs/<row>/primary.stdout.json`).

`checkBand l0 l1 a ℓ 0 = true`: lane A10's verified cell checker (`Erdos993Lean/Analytic/TailCert/Compute/Checker.lean`,
its own adaptive cover; sound by `TailCert.checkBand_sound`, standard axioms) certifies `Tail.T3UNonneg λ 0 a ℓ` for
every `λ ∈ [33/20, 17/10]`.  The tilts `t > 0` of this piece are its parent band's (lane A10's `bandCertificates`).

Trust: the one `native_decide` of this module (`Lean.ofReduceBool`, the natively compiled library
`Erdos993LeanTailCertCompute`).
-/

namespace Erdos993Lean.Analytic.N48.TailChecks

/-- The t = 0 certificate of the piece `[33/20, 17/10]` (`ℓ = 47/100`, `a = 97/1000`), by `native_decide`. -/
theorem rowP27 : TailCert.Compute.checkBand (33/20) (17/10) (97/1000) (47/100) 0 = true := by native_decide

end Erdos993Lean.Analytic.N48.TailChecks
