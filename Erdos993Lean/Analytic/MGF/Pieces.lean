import Erdos993Lean.Analytic.MGF.Checker
import Erdos993Lean.Analytic.N44.Data.Params

/-!
# The pieces of the MGF + two-sided atlas (lane A22): the n ≥ 44 tables as checker pieces

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A22.  Source: `LEAN/atlas_mgf/SPEC.md` v2 §3 ("a λ-interval inside
one piece p (0-based, the 55 pieces of Lean's `N44/Data/Params.lean`), so that θ = theta44[p], D = D44[p] and the five
rates ℓ_k = rates44[p] are constant on it"; the rows are Lean's tables VERBATIM).  This file imports only Lean's core
(the checker and lane A21's parameter tables), so that the data and check modules stay light.

* `tiltsQ44 p`: the five certified tilts `(t_k, ℓ_k)` of piece `p` (`Atlas.tvals`, `N44.Data.rates44`).
* `piece44 p : MPiece`: the checker's piece `p` (its caps, tilts and activity edges).
* `floor44 p`: the floor of `m` at `n ≥ 44` on piece `p` (`N44.Data.mmin44`), the top of every strip below 44.
-/

namespace Erdos993Lean.Analytic.MGF

/-- The five certified tilts `(t_k, ℓ_k)` of piece `p` at `n ≥ 44`, as rationals (`k < 5`: `t_k ∈ {0, 1/20, 1/10, 1/5,
3/10}`, `ℓ_k = rates44[p][k]`). -/
def tiltsQ44 (p : Nat) : List (Rat × Rat) :=
  (List.range 5).map fun k => (Atlas.tvals.getD k 0, (N44.Data.rates44.getD p []).getD k 0)

/-- **The checker's piece `p`** (0-based, `p < 55`): the caps `θ = theta44[p]`, `D = D44[p]`, the tilts `tiltsQ44 p`
and the activity interval `[pieceLo_p, pieceHi_p]`. -/
def piece44 (p : Nat) : MPiece :=
  ⟨N44.Data.theta44.getD p 0, N44.Data.D44.getD p 0, tiltsQ44 p, N44.Data.pieceLo.getD p 0,
    N44.Data.pieceHi.getD p 0⟩

/-- The floor of `m` at `n ≥ 44` on piece `p`: the top of the strip of every rung below 44. -/
def floor44 (p : Nat) : Rat := N44.Data.mmin44.getD p 0

end Erdos993Lean.Analytic.MGF
