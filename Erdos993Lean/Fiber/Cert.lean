import Mathlib

/-!
# Exact rational certificates of the binomial-fiber consumer: the format and the checker

Source: the 29 Sep 2026 binomial-fiber return, *A matching-excess consumer for forest-generated binomial
fibers* (campaign folder `ProofRuns/2026-09-28_analytic_large_n/LEAN/pro_six/return_binomial_fiber_20260929/
BINOMIAL_FIBER_COMPLETION/`), `PROOF.md` Sections 4–5 and `CHECKER.py` (`all_row_names`, `slack_constant`,
`slack_coefficient`, `certificate_details`).  Lean lane FIBER-FLOOR.

Fix `(n, a)` with `a ≤ n`, `c = n − a`.  The **states** are `(0, a)` and `(y, m)` with `1 ≤ y ≤ c`,
`0 ≤ m ≤ a − y`.  An inventory is an array `N[y, m]` on the states.  The five row families of the basic
inventory relaxation are the affine forms `S_r = u_r + Σ_s v_r(s) N_s` of `CHECKER.py`:

* `edgeBudget`: `S^e = i_2 − [C(n, 2) − (n − 1)]`, `u = −(C(n, 2) − n + 1)`, `v(y, m) = C(m, 2 − y)`;
* `matchingExcess h` (`2 ≤ h ≤ c`): `S^M_h = (D − c) C(c−2, h−1) + (a − c) C(c−2, h−2) − R_h`,
  `u = (a − c) C(c−2, h−2) − c C(c−2, h−1)`, `v(y, m) = C(c−2, h−1)(a − m)[y = 1] − (a − m − y)[y = h]`;
* `subsetCount h` (`2 ≤ h ≤ c`): `S^0_h = C(c, h) − N_h`;
* `missingEdgeUnion h` (`3 ≤ h ≤ c`): `S^-_h = N_h − C(c, h) + (C(c, 2) − N_2) C(c−2, h−2)`;
* `pairExtension h` (`3 ≤ h ≤ c`): `S^+_h = C(c−2, h−2) N_2 − C(h, 2) N_h`.

A certificate for a triple `(n, a, k)` carries `α, β ≥ 0` with `α + β = 1`, prices `t_r ≥ 0` on legal rows,
two signed multipliers `z0, z1` and a margin `ε > 0`.  With
`d_L(y, m) = C(m, k−y) − C(m, k−1−y)`, `d_R(y, m) = C(m, k−y) − C(m, k+1−y)`,

  `ρ(y, m) = α d_L(y, m) + β d_R(y, m) − z0 [y = 0] − z1 [y = 1] − Σ_r t_r v_r(y, m)`,

the checker `Cert.ok` verifies `ε = z0 + c z1 − Σ_r t_r u_r`, `ε > 0` and `ρ ≥ 0` at every state
(`certificate_details` of `CHECKER.py`, here in exact `ℚ` arithmetic instead of cleared denominators).
The soundness of the ledger identity (13) is `Erdos993Lean/Fiber/Ledger.lean`.

Binomial coefficients are computed by `bin n k = n^{(k)} / k!` (`bin_eq_choose`), which the kernel evaluates
quickly; `binS m r y = [y ≤ r] C(m, r − y)` is the coefficient of `x^r` in `x^y (1 + x)^m`.

Grade: definitions and elementary lemmas, standard axioms only.
-/

namespace Erdos993Lean
namespace Fiber

/-- The five row families of the basic inventory relaxation (`PROOF.md` (3), (7)–(10)). -/
inductive RowId where
  /-- The forest edge budget (7), `S^e = i_2 − [C(n, 2) − (n − 1)] = n − 1 − e(F)`. -/
  | edgeBudget
  /-- The excess-blocker payment (3), `S^M_h`, `2 ≤ h ≤ c`. -/
  | matchingExcess (h : ℕ)
  /-- Subset availability (8), `S^0_h = C(c, h) − N_h`, `2 ≤ h ≤ c`. -/
  | subsetCount (h : ℕ)
  /-- The edge-union payment (9), `S^-_h`, `3 ≤ h ≤ c`. -/
  | missingEdgeUnion (h : ℕ)
  /-- The independent-pair extension payment (10), `S^+_h`, `3 ≤ h ≤ c`. -/
  | pairExtension (h : ℕ)
  deriving DecidableEq, Repr

namespace RowId

/-- The legal rows at `c = n − a` (`CHECKER.py`, `all_row_names`). -/
def legal (c : ℕ) : RowId → Bool
  | edgeBudget => true
  | matchingExcess h => Nat.ble 2 h && Nat.ble h c
  | subsetCount h => Nat.ble 2 h && Nat.ble h c
  | missingEdgeUnion h => Nat.ble 3 h && Nat.ble h c
  | pairExtension h => Nat.ble 3 h && Nat.ble h c

end RowId

/-- The binomial coefficient, computed as a falling factorial over a factorial (kernel-friendly). -/
def bin (n k : ℕ) : ℕ := n.descFactorial k / k.factorial

theorem bin_eq_choose (n k : ℕ) : bin n k = n.choose k :=
  (Nat.choose_eq_descFactorial_div_factorial n k).symm

/-- `[x^r] x^y (1 + x)^m = [y ≤ r] C(m, r − y)`. -/
def binS (m r y : ℕ) : ℕ := if y ≤ r then bin m (r - y) else 0

theorem binS_eq (m r y : ℕ) : binS m r y = if y ≤ r then m.choose (r - y) else 0 := by
  unfold binS
  rw [bin_eq_choose]

/-- The constant `u_r` of the slack `S_r` at `(n, a)`, `c = n − a` (`CHECKER.py`, `slack_constant`). -/
def rowConst (n a : ℕ) : RowId → ℚ
  | .edgeBudget => -((bin n 2 : ℚ) - n + 1)
  | .matchingExcess h =>
      ((a : ℚ) - ((n - a : ℕ) : ℚ)) * (bin (n - a - 2) (h - 2) : ℚ) -
        ((n - a : ℕ) : ℚ) * (bin (n - a - 2) (h - 1) : ℚ)
  | .subsetCount h => (bin (n - a) h : ℚ)
  | .missingEdgeUnion h => (bin (n - a - 2) (h - 2) : ℚ) * (bin (n - a) 2 : ℚ) - (bin (n - a) h : ℚ)
  | .pairExtension _ => 0

/-- The coefficient `v_r(y, m)` of `N[y, m]` in the slack `S_r` (`CHECKER.py`, `slack_coefficient`). -/
def rowCoef (n a : ℕ) : RowId → ℕ → ℕ → ℚ
  | .edgeBudget, y, m => (binS m 2 y : ℚ)
  | .matchingExcess h, y, m =>
      (if y = 1 then (bin (n - a - 2) (h - 1) : ℚ) * ((a : ℚ) - m) else 0) -
        (if y = h then (a : ℚ) - m - y else 0)
  | .subsetCount h, y, _ => if y = h then -1 else 0
  | .missingEdgeUnion h, y, _ =>
      (if y = h then 1 else 0) - (if y = 2 then (bin (n - a - 2) (h - 2) : ℚ) else 0)
  | .pairExtension h, y, _ =>
      (if y = 2 then (bin (n - a - 2) (h - 2) : ℚ) else 0) - (if y = h then (bin h 2 : ℚ) else 0)

/-- A certificate for the triple `(n, a, k)`: `alpha = α` (`left`), `beta = β` (`right`), the margin
`eps = ε`, the multipliers `z0, z1` of the two normalizations (`equalities`), and the slack prices
(`rows`). -/
structure Cert where
  n : ℕ
  a : ℕ
  k : ℕ
  alpha : ℚ
  beta : ℚ
  eps : ℚ
  z0 : ℚ
  z1 : ℚ
  prices : List (RowId × ℚ)

namespace Cert

/-- `d_L(y, m) = C(m, k − y) − C(m, k − 1 − y)`. -/
def dL (c : Cert) (y m : ℕ) : ℚ := (binS m c.k y : ℚ) - (binS m (c.k - 1) y : ℚ)

/-- `d_R(y, m) = C(m, k − y) − C(m, k + 1 − y)`. -/
def dR (c : Cert) (y m : ℕ) : ℚ := (binS m c.k y : ℚ) - (binS m (c.k + 1) y : ℚ)

/-- `Σ_r t_r v_r(y, m)`. -/
def priceCoef (c : Cert) (y m : ℕ) : ℚ := (c.prices.map (fun p => p.2 * rowCoef c.n c.a p.1 y m)).sum

/-- `Σ_r t_r u_r`. -/
def priceConst (c : Cert) : ℚ := (c.prices.map (fun p => p.2 * rowConst c.n c.a p.1)).sum

/-- The pointwise residual `ρ(y, m)`. -/
def rho (c : Cert) (y m : ℕ) : ℚ :=
  c.alpha * c.dL y m + c.beta * c.dR y m - (if y = 0 then c.z0 else 0) - (if y = 1 then c.z1 else 0) -
    c.priceCoef y m

/-- **The checker** (`CHECKER.py`, `certificate_details`): the side conditions `1 ≤ n`, `1 ≤ k`, `a ≤ n`;
`α, β ≥ 0`, `α + β = 1`; every price on a legal row and nonnegative; `ε > 0`; the constant ledger
`ε = z0 + c z1 − Σ_r t_r u_r`; and `ρ ≥ 0` at every state `(0, a)` and `(y, m)`, `1 ≤ y ≤ c`,
`0 ≤ m ≤ a − y`. -/
def ok (c : Cert) : Bool :=
  Nat.ble 1 c.n && Nat.ble 1 c.k && Nat.ble c.a c.n &&
    decide (0 ≤ c.alpha) && decide (0 ≤ c.beta) && decide (c.alpha + c.beta = 1) &&
    c.prices.all (fun p => p.1.legal (c.n - c.a) && decide (0 ≤ p.2)) &&
    decide (0 < c.eps) &&
    decide (c.eps = c.z0 + ((c.n - c.a : ℕ) : ℚ) * c.z1 - c.priceConst) &&
    decide (0 ≤ c.rho 0 c.a) &&
    (List.range (c.n - c.a)).all (fun y =>
      (List.range (c.a - y)).all (fun m => decide (0 ≤ c.rho (y + 1) m)))

/-- The key `(n, a, k)` of a certificate. -/
def key (c : Cert) : ℕ × ℕ × ℕ := (c.n, c.a, c.k)

end Cert

/-- **The parameter domain (11)** through order `B` (`CHECKER.py`, `parameter_domain`), in its order:
`1 ≤ n ≤ B`, `⌈n/2⌉ ≤ a ≤ n − 1`, `⌈n/4⌉ < k < min(a, ⌈(n + 2a)/6⌉)`. -/
def paramDomain (B : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range B).flatMap fun n' =>
    ((List.range (n' + 1)).filter (fun a => Nat.ble ((n' + 2) / 2) a)).flatMap fun a =>
      ((List.range (min a ((n' + 1 + 2 * a + 5) / 6))).filter
        (fun k => Nat.ble ((n' + 1 + 3) / 4 + 1) k)).map fun k => (n' + 1, a, k)

theorem mem_paramDomain {B n a k : ℕ} :
    (n, a, k) ∈ paramDomain B ↔
      1 ≤ n ∧ n ≤ B ∧ (n + 1) / 2 ≤ a ∧ a < n ∧ (n + 3) / 4 < k ∧ k < a ∧ k < (n + 2 * a + 5) / 6 := by
  unfold paramDomain
  simp only [List.mem_flatMap, List.mem_filter, List.mem_range, List.mem_map, Nat.ble_eq,
    Prod.mk.injEq, lt_min_iff]
  constructor
  · rintro ⟨n', hn', a', ⟨ha', ha'2⟩, k', ⟨⟨hk'1, hk'2⟩, hk'3⟩, rfl, rfl, rfl⟩
    omega
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    refine ⟨n - 1, by omega, a, ⟨by omega, by omega⟩, k, ⟨⟨by omega, by omega⟩, by omega⟩, by omega, rfl, rfl⟩

end Fiber
end Erdos993Lean
