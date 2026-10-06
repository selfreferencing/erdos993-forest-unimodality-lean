import Erdos993Lean.Analytic.TailCert.Compute.Checker

/-!
# O3 at `n ≥ 48`: the sub-band row `[8/5, 33/20]` at the Laplace parameter `t = 0` (lane A20)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A20.  Source: lane R4X's `LEAN/r4x/REACH_BELOW_52.md` §5(c)
(the N = 48 row of band 26), produced by lane O3R with the unmodified O3 checker (`LEAN/ladder/o3/rows.json`, row
2: interval `[8/5, 33/20]`, rate `ℓ = 939/2000` (0.4695), potential coefficient `a = 47/500`; `runs/<row>/primary.stdout.json`).

`checkBand l0 l1 a ℓ 0 = true`: lane A10's verified cell checker (`Erdos993Lean/Analytic/TailCert/Compute/Checker.lean`,
its own adaptive cover; sound by `TailCert.checkBand_sound`, standard axioms) certifies `Tail.T3UNonneg λ 0 a ℓ` for
every `λ ∈ [8/5, 33/20]`.  The tilts `t > 0` of this piece are its parent band's (lane A10's `bandCertificates`).

Trust: the one `native_decide` of this module (`Lean.ofReduceBool`, the natively compiled library
`Erdos993LeanTailCertCompute`).
-/

namespace Erdos993Lean.Analytic.N48.TailChecks

/-- The t = 0 certificate of the piece `[8/5, 33/20]` (`ℓ = 939/2000`, `a = 47/500`), by `native_decide`. -/
theorem rowP26 : TailCert.Compute.checkBand (8/5) (33/20) (47/500) (939/2000) 0 = true := by native_decide

end Erdos993Lean.Analytic.N48.TailChecks
