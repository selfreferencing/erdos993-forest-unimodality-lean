import Erdos993Lean.Analytic.Defs

/-!
# T1's explicit threshold is antitone in the caps `θ` and `D`

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A21.  Source: the definition `ExplicitThreshold`
(`Erdos993Lean/Analytic/Defs.lean`, T1 Theorem 3.1 + Lemma 5.1 + Theorem 6.1); the companion of lane A20's
`explicitThreshold_tail_mono` (`N48/Mono.lean`, antitone in the tail).

**`explicitThreshold_cap_mono`**: if `ExplicitThreshold q m θ D T M1` holds, `q(1 − q) ≥ 0`, `m ≥ 0`, `θ' ≤ θ` and
`D' ≤ D`, then `ExplicitThreshold q m θ' D' T M1` holds with the same witnesses.  The caps enter only the strict
inequality `ν θ q(1 − q) m < α − γ D m − ∑ …`, through the terms `ν θ q(1 − q) m` (coefficient `ν q(1 − q) m ≥ 0`) and
`γ D m` (coefficient `γ m ≥ 0`), so a smaller `θ` or `D` keeps it.

Use: the atlas checks of a coarser profile (Profile30's `θ`, `D` in lane A20's n ≥ 48 strip, lane A19's n ≥ 52 strip
and lane A9's atlas) stay valid for the piece-wise smaller caps of the profiles `P45` and `P44`, whose O1/O2 inputs
are the certified ladder rows (`N45/Strip.lean`, `N44/Strip.lean`).

Scalarity check: no new scalar; `θ` is O2's cap on the second moment of `δ`, `D` O1's cap on the variance of the
free count `M`, both consumed by T1's threshold inequality.
-/

namespace Erdos993Lean.Analytic.N45

/-- **T1's explicit threshold is antitone in the caps**: smaller `θ` and `D` keep the explicit threshold, with the
same multipliers, fibre bound and prices (`q(1 − q) ≥ 0`, `m ≥ 0`). -/
theorem explicitThreshold_cap_mono {q m θ θ' D D' : ℝ} {T : ℕ → ℝ} {M1 : ℕ}
    (h : ExplicitThreshold q m θ D T M1) (hq : 0 ≤ q * (1 - q)) (hm : 0 ≤ m) (hθ : θ' ≤ θ) (hD : D' ≤ D) :
    ExplicitThreshold q m θ' D' T M1 := by
  obtain ⟨ν, c, α, β, γ, hh, S, hν, hγ, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨ν, c, α, β, γ, hh, S, hν, hγ, h1, h2, h3, h4, h5, ?_⟩
  have e1 : ν * θ' * (q * (1 - q)) * m ≤ ν * θ * (q * (1 - q)) * m := by
    have a1 : ν * θ' ≤ ν * θ := mul_le_mul_of_nonneg_left hθ hν.le
    have a2 : ν * θ' * (q * (1 - q)) ≤ ν * θ * (q * (1 - q)) := mul_le_mul_of_nonneg_right a1 hq
    exact mul_le_mul_of_nonneg_right a2 hm
  have e2 : γ * D' * m ≤ γ * D * m := by
    have a1 : γ * D' ≤ γ * D := mul_le_mul_of_nonneg_left hD hγ
    exact mul_le_mul_of_nonneg_right a1 hm
  linarith

end Erdos993Lean.Analytic.N45
