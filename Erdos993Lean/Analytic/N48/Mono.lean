import Erdos993Lean.Analytic.Defs

/-!
# T1's explicit threshold is antitone in the tail function

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A20.  Source: the definition `ExplicitThreshold`
(`Erdos993Lean/Analytic/Defs.lean`, T1 Theorem 3.1 + Lemma 5.1 + Theorem 6.1).

**`explicitThreshold_tail_mono`**: if `ExplicitThreshold q m θ D T M1` holds and `T' ≤ T` below `M1`, then
`ExplicitThreshold q m θ D T' M1` holds with the same witnesses.  The tail enters only through the price
`∑_{M' < M1} S(M') (T(M') − T(M' − 1))` (with `T(−1) = 0`); by Abel summation this is
`∑_{M' < M1 − 1} (S(M') − S(M' + 1)) T(M') + S(M1 − 1) T(M1 − 1)`, a nonnegative combination of the values `T(M')`,
because the prices `S` are nonnegative and nonincreasing.  (The proof is an induction on the number of terms:
`∑_{i < n} S_i (d_i − d_{i−1}) ≥ S_{n−1} d_{n−1}` for `d = T − T' ≥ 0`.)

Use: a better lower-tail bound (O3) never breaks an atlas check, so the checks made with a coarser tail stay valid
(`N48/Strip.lean`: lane A19's strip and lane A9's atlas under the tail `tailFn48 ≤ tailFnAct`).

Scalarity check: no new scalar; `T` is the lower-tail bound of the free count `M` (O3), `S` the tail prices of T1.
-/

namespace Erdos993Lean.Analytic.N48

open Finset

/-- The Abel-summation step: for `S` nonincreasing below `M1` and `d ≥ 0` below `M1`,
`∑_{i < n} S_i (d_i − d_{i−1}) ≥ S_{n−1} d_{n−1}` (`d_{−1} = 0`) for `1 ≤ n ≤ M1`. -/
theorem abel_step {S d : ℕ → ℝ} {M1 : ℕ}
    (hS1 : ∀ M : ℕ, M + 1 < M1 → S (M + 1) ≤ S M) (hd : ∀ i < M1, 0 ≤ d i) :
    ∀ n, 1 ≤ n → n ≤ M1 →
      S (n - 1) * d (n - 1) ≤ ∑ i ∈ range n, S i * (d i - if i = 0 then 0 else d (i - 1)) := by
  intro n hn1 hnM
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · rw [Finset.sum_range_succ]
      have ih' := ih hpos (by omega)
      have hn0 : n ≠ 0 := by omega
      rw [if_neg hn0]
      have hS : S n ≤ S (n - 1) := by
        have := hS1 (n - 1) (by omega)
        rwa [Nat.sub_add_cancel hpos] at this
      have hdn1 : 0 ≤ d (n - 1) := hd (n - 1) (by omega)
      have hSd : S n * d (n - 1) ≤ S (n - 1) * d (n - 1) := mul_le_mul_of_nonneg_right hS hdn1
      rw [Nat.add_sub_cancel]
      nlinarith

/-- **T1's explicit threshold is antitone in the tail function**: a tail bound `T' ≤ T` below `M1` keeps the explicit
threshold, with the same multipliers, fibre bound and prices. -/
theorem explicitThreshold_tail_mono {q m θ D : ℝ} {T T' : ℕ → ℝ} {M1 : ℕ}
    (h : ExplicitThreshold q m θ D T M1) (hT : ∀ M' < M1, T' M' ≤ T M') :
    ExplicitThreshold q m θ D T' M1 := by
  obtain ⟨ν, c, α, β, γ, hh, S, hν, hγ, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨ν, c, α, β, γ, hh, S, hν, hγ, h1, h2, h3, h4, h5, ?_⟩
  set d : ℕ → ℝ := fun i => T i - T' i with hd_def
  have hd : ∀ i < M1, 0 ≤ d i := fun i hi => sub_nonneg.mpr (hT i hi)
  have hdiff : 0 ≤ ∑ i ∈ range M1, S i * (d i - if i = 0 then 0 else d (i - 1)) := by
    rcases Nat.eq_zero_or_pos M1 with h0 | hpos
    · simp [h0]
    · exact le_trans (mul_nonneg (h4 _ (by omega)) (hd _ (by omega)))
        (abel_step h5 hd M1 hpos le_rfl)
  have hsplit : ∑ i ∈ range M1, S i * (d i - if i = 0 then 0 else d (i - 1)) =
      ∑ M' ∈ range M1, S M' * (T M' - if M' = 0 then 0 else T (M' - 1)) -
        ∑ M' ∈ range M1, S M' * (T' M' - if M' = 0 then 0 else T' (M' - 1)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hd_def]
    split_ifs <;> ring
  linarith

end Erdos993Lean.Analytic.N48
