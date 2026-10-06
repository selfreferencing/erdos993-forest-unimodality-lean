import Mathlib
import Erdos993Lean.Fiber.Cert
import Erdos993Lean.Fiber.Inventory
import Erdos993Lean.Fiber.InventoryRows
import Erdos993Lean.Fiber.Matching

/-!
# The certificate ledger (13) and its soundness for forests

Source: the 29 Sep 2026 binomial-fiber return (`BINOMIAL_FIBER_COMPLETION/PROOF.md`), Sections 1–5.
Lean lane FIBER-FLOOR.

## Part 1: the basic normalized inventory relaxation and the ledger identity

An inventory at `(n, a)` is an array `N : ℕ → ℕ → ℚ`, read on the box `{0, …, n − a} × {0, …, a}`
(`box`); its coefficients are `i_r(N) = Σ N[y, m] [y ≤ r] C(m, r − y)` (`invCoeff`, the coefficients of
`Σ N[y, m] x^y (1 + x)^m`, (1) of the source) and its slacks are `S_r(N) = u_r + Σ_s v_r(s) N_s`
(`rowSlack`, with `u_r = rowConst`, `v_r = rowCoef` of `Erdos993Lean/Fiber/Cert.lean`).  `Relaxation n a N`
is the basic normalized inventory relaxation: `N ≥ 0`, the support `(0, a)` / `1 ≤ y ≤ n − a`,
`m + y ≤ a`, the normalizations `N[0, a] = 1`, `Σ_m N[1, m] = n − a`, and every legal slack `≥ 0`.

* `Cert.ledger` (**the identity (13)**): for every certificate satisfying the constant ledger and every
  inventory with the two normalizations,
  `α (i_k − i_{k−1}) + β (i_k − i_{k+1}) = ε + Σ_r t_r S_r + Σ_s ρ_s N_s`.
* `Cert.eps_le`, `Cert.noValley`: if `c.ok = true` and `N` lies in the relaxation at `(c.n, c.a)`, the left
  side is at least `ε > 0`, so there is no weak valley at `k`: `¬ (i_k ≤ i_{k−1} ∧ i_k ≤ i_{k+1})`.

## Part 2: forests

For a finite forest `F` and an independent set `A` of maximum cardinality, `forestInv F A y m` is
`N[y, m] = Zhang.tCount F.graph univ A y m` (the independent `J ⊆ C = Aᶜ` with `|J| = y` and
`|A \ N(J)| = m`).  `forestInv_relaxation`: it lies in the relaxation at `(F.n, |A|)` — the support and
normalizations from `Fiber/Inventory.lean` (F2), the edge budget (7) from the edge count (F6), the
subset rows (8) from the subset cap, the rows (9), (10) from `Fiber/InventoryRows.lean`, and the
excess-blocker rows (3) from Theorem 3.1 (`Fiber/Charges.lean`) with the exposed-leaf matching of
Lemmas 2.1–2.2 (`Fiber/Matching.lean`).  `invCoeff_forestInv`: its coefficients are the independence
counts (`Zhang.indepCount_eq_sum_tCount`).

* **`noWeakValley_of_cert`**: for a maximum-cardinality independent `A` of `F` and a certificate `c`
  with `c.ok = true` and key `(F.n, |A|, k)`, `¬ (i_k ≤ i_{k−1} ∧ i_k ≤ i_{k+1})` for the independence
  counts `i_r = independenceCount F r`.

Grade: PROVED IN LEAN (complete proofs, standard axioms only).
-/

namespace Erdos993Lean
namespace Fiber

open Finset

/-! ## Part 1: the relaxation and the ledger identity -/

/-- The index box `{0, …, n − a} × {0, …, a}` of an inventory at `(n, a)`. -/
def box (n a : ℕ) : Finset (ℕ × ℕ) := range (n - a + 1) ×ˢ range (a + 1)

/-- The coefficient `i_r(N) = Σ_{(y, m)} N[y, m] [y ≤ r] C(m, r − y)` of `Σ N[y, m] x^y (1 + x)^m`. -/
def invCoeff (n a : ℕ) (N : ℕ → ℕ → ℚ) (r : ℕ) : ℚ :=
  ∑ s ∈ box n a, N s.1 s.2 * (binS s.2 r s.1 : ℚ)

/-- The slack `S_r(N) = u_r + Σ_s v_r(s) N_s` of the row `r` at `(n, a)`. -/
def rowSlack (n a : ℕ) (N : ℕ → ℕ → ℚ) (r : RowId) : ℚ :=
  rowConst n a r + ∑ s ∈ box n a, rowCoef n a r s.1 s.2 * N s.1 s.2

/-- **The basic normalized inventory relaxation** at `(n, a)` ((3), (6)–(10) of the source). -/
structure Relaxation (n a : ℕ) (N : ℕ → ℕ → ℚ) : Prop where
  nonneg : ∀ y m, 0 ≤ N y m
  support : ∀ y m, N y m ≠ 0 → (y = 0 ∧ m = a) ∨ (1 ≤ y ∧ y ≤ n - a ∧ m + y ≤ a)
  empty : N 0 a = 1
  singleton : ∑ m ∈ range (a + 1), N 1 m = ((n - a : ℕ) : ℚ)
  rows : ∀ r : RowId, r.legal (n - a) = true → 0 ≤ rowSlack n a N r

/-- A box sum of a term supported on the level `y = j ≤ n − a`. -/
theorem sum_box_level (n a j : ℕ) (hj : j ≤ n - a) (f : ℕ × ℕ → ℚ) :
    ∑ s ∈ box n a, (if s.1 = j then f s else 0) = ∑ m ∈ range (a + 1), f (j, m) := by
  unfold box
  rw [Finset.sum_product, Finset.sum_eq_single j]
  · apply Finset.sum_congr rfl
    intro m _
    simp
  · intro y _ hy
    apply Finset.sum_eq_zero
    intro m _
    simp [hy]
  · intro hj'
    exact absurd (Finset.mem_range.mpr (by omega)) hj'

/-- A box sum of a term supported on a level `y = j > n − a` vanishes. -/
theorem sum_box_level_zero (n a j : ℕ) (hj : n - a < j) (f : ℕ × ℕ → ℚ) :
    ∑ s ∈ box n a, (if s.1 = j then f s else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro s hs
  unfold box at hs
  rw [Finset.mem_product, Finset.mem_range] at hs
  rw [if_neg (by omega)]

/-- Interchange of the price list and the box sum: `Σ_r t_r S_r = Σ_r t_r u_r + Σ_s (Σ_r t_r v_r(s)) N_s`. -/
theorem sum_prices_rowSlack (n a : ℕ) (N : ℕ → ℕ → ℚ) (L : List (RowId × ℚ)) :
    (L.map (fun p => p.2 * rowSlack n a N p.1)).sum =
      (L.map (fun p => p.2 * rowConst n a p.1)).sum +
        ∑ s ∈ box n a, (L.map (fun p => p.2 * rowCoef n a p.1 s.1 s.2)).sum * N s.1 s.2 := by
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    unfold rowSlack
    have e : ∑ s ∈ box n a, (p.2 * rowCoef n a p.1 s.1 s.2 +
          (L.map (fun p => p.2 * rowCoef n a p.1 s.1 s.2)).sum) * N s.1 s.2 =
        p.2 * ∑ s ∈ box n a, rowCoef n a p.1 s.1 s.2 * N s.1 s.2 +
          ∑ s ∈ box n a, (L.map (fun p => p.2 * rowCoef n a p.1 s.1 s.2)).sum * N s.1 s.2 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s _
      ring
    rw [e]
    ring

/-- **The certificate identity (13)**: for a certificate satisfying the constant ledger
`ε = z0 + c z1 − Σ_r t_r u_r` and an inventory with the two normalizations (the level-`0` mass is `1`
and the level-`1` mass is `c = n − a`),
`α (i_k − i_{k−1}) + β (i_k − i_{k+1}) = ε + Σ_r t_r S_r + Σ_s ρ_s N_s`. -/
theorem Cert.ledger (c : Cert) (N : ℕ → ℕ → ℚ)
    (h0 : ∑ s ∈ box c.n c.a, (if s.1 = 0 then N s.1 s.2 else 0) = 1)
    (h1 : ∑ s ∈ box c.n c.a, (if s.1 = 1 then N s.1 s.2 else 0) = ((c.n - c.a : ℕ) : ℚ))
    (hconst : c.eps = c.z0 + ((c.n - c.a : ℕ) : ℚ) * c.z1 - c.priceConst) :
    c.alpha * (invCoeff c.n c.a N c.k - invCoeff c.n c.a N (c.k - 1)) +
        c.beta * (invCoeff c.n c.a N c.k - invCoeff c.n c.a N (c.k + 1)) =
      c.eps + (c.prices.map (fun p => p.2 * rowSlack c.n c.a N p.1)).sum +
        ∑ s ∈ box c.n c.a, c.rho s.1 s.2 * N s.1 s.2 := by
  have hlhs : c.alpha * (invCoeff c.n c.a N c.k - invCoeff c.n c.a N (c.k - 1)) +
        c.beta * (invCoeff c.n c.a N c.k - invCoeff c.n c.a N (c.k + 1)) =
      ∑ s ∈ box c.n c.a, N s.1 s.2 * (c.alpha * c.dL s.1 s.2 + c.beta * c.dR s.1 s.2) := by
    unfold invCoeff Cert.dL Cert.dR
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    ring
  have hrho : ∑ s ∈ box c.n c.a, c.rho s.1 s.2 * N s.1 s.2 =
      ∑ s ∈ box c.n c.a, N s.1 s.2 * (c.alpha * c.dL s.1 s.2 + c.beta * c.dR s.1 s.2) -
        c.z0 * ∑ s ∈ box c.n c.a, (if s.1 = 0 then N s.1 s.2 else 0) -
        c.z1 * ∑ s ∈ box c.n c.a, (if s.1 = 1 then N s.1 s.2 else 0) -
        ∑ s ∈ box c.n c.a, c.priceCoef s.1 s.2 * N s.1 s.2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    unfold Cert.rho
    split_ifs <;> ring
  rw [hlhs, hrho, sum_prices_rowSlack, h0, h1, hconst]
  unfold Cert.priceConst Cert.priceCoef
  ring

/-- The facts recorded by a passing certificate. -/
theorem Cert.ok_spec {c : Cert} (h : c.ok = true) :
    1 ≤ c.n ∧ 1 ≤ c.k ∧ c.a ≤ c.n ∧ 0 ≤ c.alpha ∧ 0 ≤ c.beta ∧ c.alpha + c.beta = 1 ∧
      (∀ p ∈ c.prices, p.1.legal (c.n - c.a) = true ∧ 0 ≤ p.2) ∧ 0 < c.eps ∧
      c.eps = c.z0 + ((c.n - c.a : ℕ) : ℚ) * c.z1 - c.priceConst ∧ 0 ≤ c.rho 0 c.a ∧
      (∀ y m, 1 ≤ y → y ≤ c.n - c.a → m + y ≤ c.a → 0 ≤ c.rho y m) := by
  simp only [Cert.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, ?_⟩
  intro y m hy1 hyc hmy
  have := h11 (y - 1) (by omega) m (by omega)
  rwa [Nat.sub_add_cancel hy1] at this

/-- **Soundness of a certificate on the relaxation**: `ε ≤ α (i_k − i_{k−1}) + β (i_k − i_{k+1})`. -/
theorem Cert.eps_le (c : Cert) (hc : c.ok = true) {N : ℕ → ℕ → ℚ} (hN : Relaxation c.n c.a N) :
    c.eps ≤ c.alpha * (invCoeff c.n c.a N c.k - invCoeff c.n c.a N (c.k - 1)) +
        c.beta * (invCoeff c.n c.a N c.k - invCoeff c.n c.a N (c.k + 1)) := by
  obtain ⟨-, -, -, -, -, -, hprice, -, hconst, hrho0, hrho⟩ := Cert.ok_spec hc
  have h0 : ∑ s ∈ box c.n c.a, (if s.1 = 0 then N s.1 s.2 else 0) = 1 := by
    rw [sum_box_level c.n c.a 0 (Nat.zero_le _) (fun s => N s.1 s.2)]
    rw [Finset.sum_eq_single c.a]
    · exact hN.empty
    · intro m _ hm
      by_contra hne
      rcases hN.support 0 m hne with ⟨-, h⟩ | ⟨h, -⟩
      · exact hm h
      · omega
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self c.a)) h
  have h1 : ∑ s ∈ box c.n c.a, (if s.1 = 1 then N s.1 s.2 else 0) = ((c.n - c.a : ℕ) : ℚ) := by
    by_cases hc1 : 1 ≤ c.n - c.a
    · rw [sum_box_level c.n c.a 1 hc1 (fun s => N s.1 s.2)]
      exact hN.singleton
    · rw [sum_box_level_zero c.n c.a 1 (by omega) (fun s => N s.1 s.2)]
      have : c.n - c.a = 0 := by omega
      rw [this, Nat.cast_zero]
  rw [c.ledger N h0 h1 hconst]
  have hP : 0 ≤ (c.prices.map (fun p => p.2 * rowSlack c.n c.a N p.1)).sum := by
    apply List.sum_nonneg
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact mul_nonneg (hprice p hp).2 (hN.rows p.1 (hprice p hp).1)
  have hR : 0 ≤ ∑ s ∈ box c.n c.a, c.rho s.1 s.2 * N s.1 s.2 := by
    apply Finset.sum_nonneg
    intro s _
    by_cases hNs : N s.1 s.2 = 0
    · rw [hNs, mul_zero]
    · apply mul_nonneg _ (hN.nonneg _ _)
      rcases hN.support _ _ hNs with ⟨hy, hm⟩ | ⟨hy1, hyc, hmy⟩
      · rw [hy, hm]
        exact hrho0
      · exact hrho _ _ hy1 hyc hmy
  linarith

/-- **No weak valley on the relaxation**: a passing certificate excludes
`i_k ≤ i_{k−1} ∧ i_k ≤ i_{k+1}` for every inventory in the relaxation at `(c.n, c.a)`. -/
theorem Cert.noValley (c : Cert) (hc : c.ok = true) {N : ℕ → ℕ → ℚ} (hN : Relaxation c.n c.a N) :
    ¬ (invCoeff c.n c.a N c.k ≤ invCoeff c.n c.a N (c.k - 1) ∧
        invCoeff c.n c.a N c.k ≤ invCoeff c.n c.a N (c.k + 1)) := by
  rintro ⟨hL, hR⟩
  have heps := c.eps_le hc hN
  obtain ⟨-, -, -, hα, hβ, -, -, hε, -⟩ := Cert.ok_spec hc
  have h1 : c.alpha * (invCoeff c.n c.a N c.k - invCoeff c.n c.a N (c.k - 1)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hα (by linarith)
  have h2 : c.beta * (invCoeff c.n c.a N c.k - invCoeff c.n c.a N (c.k + 1)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hβ (by linarith)
  linarith

/-! ### The slacks level by level -/

theorem rowSlack_edgeBudget (n a : ℕ) (N : ℕ → ℕ → ℚ) :
    rowSlack n a N .edgeBudget = invCoeff n a N 2 - ((bin n 2 : ℚ) - n + 1) := by
  unfold rowSlack invCoeff
  have e : ∑ s ∈ box n a, rowCoef n a .edgeBudget s.1 s.2 * N s.1 s.2 =
      ∑ s ∈ box n a, N s.1 s.2 * (binS s.2 2 s.1 : ℚ) :=
    Finset.sum_congr rfl (fun s _ => mul_comm _ _)
  rw [e]
  simp only [rowConst]
  ring

theorem rowSlack_matchingExcess (n a h : ℕ) (h2 : 2 ≤ h) (hh : h ≤ n - a) (N : ℕ → ℕ → ℚ) :
    rowSlack n a N (.matchingExcess h) =
      ((a : ℚ) - ((n - a : ℕ) : ℚ)) * (bin (n - a - 2) (h - 2) : ℚ) -
        ((n - a : ℕ) : ℚ) * (bin (n - a - 2) (h - 1) : ℚ) +
        (bin (n - a - 2) (h - 1) : ℚ) * ∑ m ∈ range (a + 1), ((a : ℚ) - m) * N 1 m -
        ∑ m ∈ range (a + 1), ((a : ℚ) - m - h) * N h m := by
  unfold rowSlack
  simp only [rowConst, rowCoef]
  have e : ∀ s : ℕ × ℕ,
      ((if s.1 = 1 then (bin (n - a - 2) (h - 1) : ℚ) * ((a : ℚ) - s.2) else 0) -
          (if s.1 = h then (a : ℚ) - s.2 - s.1 else 0)) * N s.1 s.2 =
        (if s.1 = 1 then (bin (n - a - 2) (h - 1) : ℚ) * (((a : ℚ) - s.2) * N s.1 s.2) else 0) -
          (if s.1 = h then ((a : ℚ) - s.2 - h) * N s.1 s.2 else 0) := by
    rintro ⟨y, m⟩
    dsimp only
    split_ifs <;> first | (exfalso; omega) | ring1 | (subst_vars; ring1)
  rw [Finset.sum_congr rfl (fun s _ => e s), Finset.sum_sub_distrib,
    sum_box_level n a 1 (by omega)
      (fun s => (bin (n - a - 2) (h - 1) : ℚ) * (((a : ℚ) - s.2) * N s.1 s.2)),
    sum_box_level n a h hh (fun s => ((a : ℚ) - s.2 - h) * N s.1 s.2), Finset.mul_sum]
  ring

theorem rowSlack_subsetCount (n a h : ℕ) (hh : h ≤ n - a) (N : ℕ → ℕ → ℚ) :
    rowSlack n a N (.subsetCount h) = (bin (n - a) h : ℚ) - ∑ m ∈ range (a + 1), N h m := by
  unfold rowSlack
  simp only [rowConst, rowCoef]
  have e : ∀ s : ℕ × ℕ, (if s.1 = h then (-1 : ℚ) else 0) * N s.1 s.2 =
      if s.1 = h then -N s.1 s.2 else 0 := by
    intro s
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun s _ => e s), sum_box_level n a h hh (fun s => -N s.1 s.2),
    Finset.sum_neg_distrib]
  ring

theorem rowSlack_missingEdgeUnion (n a h : ℕ) (h2 : 2 ≤ h) (hh : h ≤ n - a) (N : ℕ → ℕ → ℚ) :
    rowSlack n a N (.missingEdgeUnion h) =
      (bin (n - a - 2) (h - 2) : ℚ) * (bin (n - a) 2 : ℚ) - (bin (n - a) h : ℚ) +
        ∑ m ∈ range (a + 1), N h m -
        (bin (n - a - 2) (h - 2) : ℚ) * ∑ m ∈ range (a + 1), N 2 m := by
  unfold rowSlack
  simp only [rowConst, rowCoef]
  have e : ∀ s : ℕ × ℕ,
      ((if s.1 = h then (1 : ℚ) else 0) - (if s.1 = 2 then (bin (n - a - 2) (h - 2) : ℚ) else 0)) *
          N s.1 s.2 =
        (if s.1 = h then N s.1 s.2 else 0) -
          (if s.1 = 2 then (bin (n - a - 2) (h - 2) : ℚ) * N s.1 s.2 else 0) := by
    intro s
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun s _ => e s), Finset.sum_sub_distrib,
    sum_box_level n a h hh (fun s => N s.1 s.2),
    sum_box_level n a 2 (by omega) (fun s => (bin (n - a - 2) (h - 2) : ℚ) * N s.1 s.2),
    Finset.mul_sum]
  ring

theorem rowSlack_pairExtension (n a h : ℕ) (h2 : 2 ≤ h) (hh : h ≤ n - a) (N : ℕ → ℕ → ℚ) :
    rowSlack n a N (.pairExtension h) =
      (bin (n - a - 2) (h - 2) : ℚ) * ∑ m ∈ range (a + 1), N 2 m -
        (bin h 2 : ℚ) * ∑ m ∈ range (a + 1), N h m := by
  unfold rowSlack
  simp only [rowConst, rowCoef]
  have e : ∀ s : ℕ × ℕ,
      ((if s.1 = 2 then (bin (n - a - 2) (h - 2) : ℚ) else 0) - (if s.1 = h then (bin h 2 : ℚ) else 0)) *
          N s.1 s.2 =
        (if s.1 = 2 then (bin (n - a - 2) (h - 2) : ℚ) * N s.1 s.2 else 0) -
          (if s.1 = h then (bin h 2 : ℚ) * N s.1 s.2 else 0) := by
    intro s
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun s _ => e s), Finset.sum_sub_distrib,
    sum_box_level n a 2 (by omega) (fun s => (bin (n - a - 2) (h - 2) : ℚ) * N s.1 s.2),
    sum_box_level n a h hh (fun s => (bin h 2 : ℚ) * N s.1 s.2), Finset.mul_sum, Finset.mul_sum]
  ring

/-! ## Part 2: forests -/

section Forest

open scoped Classical

theorem isIndepFinset_of_isIndepSet {V : Type*} {G : SimpleGraph V} {A : Finset V}
    (h : G.IsIndepSet (A : Set V)) : IsIndepFinset G A := by
  intro v hv w hw hvw
  exact h (Finset.mem_coe.mpr hv) (Finset.mem_coe.mpr hw) (G.ne_of_adj hvw) hvw

theorem isIndepSet_of_isIndepFinset {V : Type*} {G : SimpleGraph V} {A : Finset V}
    (h : IsIndepFinset G A) : G.IsIndepSet (A : Set V) := by
  intro v hv w hw _
  exact h v (Finset.mem_coe.mp hv) w (Finset.mem_coe.mp hw)

theorem card_univ_sdiff_fin {n : ℕ} (A : Finset (Fin n)) : (Finset.univ \ A).card = n - A.card := by
  rw [Finset.card_univ_diff, Fintype.card_fin]

/-- `independenceCount` is Mathlib's count (classical decidability of the adjacency). -/
theorem independenceCount_eq_card (F : FiniteForest) (k : ℕ) :
    independenceCount F k = (F.graph.indepSetFinset k).card := rfl

/-- `t_{y,m} ≠ 0` forces `y ≤ |s \ I|`. -/
theorem le_card_of_tCount_ne_zero {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {s I : Finset V} {y m : ℕ} (h : Zhang.tCount G s I y m ≠ 0) : y ≤ (s \ I).card := by
  unfold Zhang.tCount at h
  obtain ⟨J, hJ⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
  rw [Finset.mem_filter, Finset.mem_powerset] at hJ
  rw [← hJ.2.2.1]
  exact Finset.card_le_card hJ.1

variable (F : FiniteForest)

/-- **The inventory of a marking** `A`: `N[y, m] = Zhang.tCount F.graph univ A y m` over `ℚ`. -/
noncomputable def forestInv (A : Finset (Fin F.n)) (y m : ℕ) : ℚ :=
  (Zhang.tCount F.graph Finset.univ A y m : ℚ)

variable {F}

/-- The coefficients of the inventory are the independence counts ((1) of the source,
`Zhang.indepCount_eq_sum_tCount`). -/
theorem invCoeff_forestInv {A : Finset (Fin F.n)} (hAi : IsIndepFinset F.graph A) (r : ℕ) :
    invCoeff F.n A.card (forestInv F A) r = (independenceCount F r : ℚ) := by
  have h := Zhang.indepCount_eq_sum_tCount hAi (Finset.subset_univ A) r
  rw [indepCount_univ, card_univ_sdiff_fin] at h
  rw [independenceCount_eq_card F r, h]
  unfold invCoeff box forestInv
  rw [Finset.sum_product]
  push_cast
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro m _
  rw [binS_eq]
  split_ifs <;> simp

/-- Support of the inventory of a maximum independent `A` ((6) of the source). -/
theorem forestInv_support {A : Finset (Fin F.n)} (hAi : IsIndepFinset F.graph A)
    (hAmax : A.card = Zhang.alphaIn F.graph Finset.univ) (y m : ℕ) (h : forestInv F A y m ≠ 0) :
    (y = 0 ∧ m = A.card) ∨ (1 ≤ y ∧ y ≤ F.n - A.card ∧ m + y ≤ A.card) := by
  unfold forestInv at h
  have h' : Zhang.tCount F.graph Finset.univ A y m ≠ 0 := by exact_mod_cast h
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · left
    refine ⟨rfl, ?_⟩
    rw [Zhang.tCount_zero] at h'
    by_contra hm
    exact h' (if_neg hm)
  · right
    refine ⟨hy, ?_, ?_⟩
    · have := le_card_of_tCount_ne_zero h'
      rwa [card_univ_sdiff_fin] at this
    · by_contra hlt
      exact h' (Zhang.tCount_eq_zero_of_alphaIn_lt hAi (Finset.subset_univ A) (by omega))

/-- `Σ_m (a − m − j) N[y, m]` with the subtraction in `ℕ` equals the same sum in `ℚ` when every
state `(y, m)` with `N[y, m] ≠ 0` has `m + j ≤ a`. -/
theorem sum_natSub_cast (a j : ℕ) (N : ℕ → ℚ) (hN : ∀ m, N m ≠ 0 → m + j ≤ a) :
    ∑ m ∈ range (a + 1), ((a - m - j : ℕ) : ℚ) * N m = ∑ m ∈ range (a + 1), ((a : ℚ) - m - j) * N m := by
  apply Finset.sum_congr rfl
  intro m _
  by_cases h : N m = 0
  · rw [h, mul_zero, mul_zero]
  · have := hN m h
    rw [Nat.cast_sub (by omega : j ≤ a - m), Nat.cast_sub (by omega : m ≤ a)]

/-- **The edge budget (7)** on the inventory of a forest: `S^e = n − 1 − e(F) ≥ 0`. -/
theorem forest_edge_row {A : Finset (Fin F.n)} (hAi : IsIndepFinset F.graph A) (hn : 1 ≤ F.n) :
    0 ≤ rowSlack F.n A.card (forestInv F A) .edgeBudget := by
  rw [rowSlack_edgeBudget, invCoeff_forestInv hAi, bin_eq_choose]
  have h1 := independenceCount_two_add_card_edgeFinset F
  have h2 := card_edgeFinset_le_sub_one F
  have h3 : F.n.choose 2 + 1 ≤ independenceCount F 2 + F.n := by omega
  have h3' : ((F.n.choose 2 : ℕ) : ℚ) + 1 ≤ (independenceCount F 2 : ℚ) + (F.n : ℚ) := by
    exact_mod_cast h3
  linarith

/-- **The subset rows (8)** on the inventory of a forest: `S^0_h = C(c, h) − N_h ≥ 0`. -/
theorem forest_subset_row (A : Finset (Fin F.n)) {h : ℕ} (hh : h ≤ F.n - A.card) :
    0 ≤ rowSlack F.n A.card (forestInv F A) (.subsetCount h) := by
  rw [rowSlack_subsetCount _ _ _ hh, bin_eq_choose]
  have := card_fiber_row_le_choose (G := F.graph) Finset.univ A h
  rw [card_univ_sdiff_fin] at this
  unfold forestInv
  rw [← Nat.cast_sum, sub_nonneg]
  exact_mod_cast this

/-- **The edge-union rows (9)** on the inventory of a forest. -/
theorem forest_edgeUnion_row (A : Finset (Fin F.n)) {h : ℕ} (h2 : 2 ≤ h) (hh : h ≤ F.n - A.card) :
    0 ≤ rowSlack F.n A.card (forestInv F A) (.missingEdgeUnion h) := by
  rw [rowSlack_missingEdgeUnion _ _ _ h2 hh]
  have := edgeUnion_nonneg_inventory (G := F.graph) Finset.univ A h2
  rw [card_univ_sdiff_fin] at this
  simp only [bin_eq_choose]
  unfold forestInv
  rw [← Nat.cast_sum, ← Nat.cast_sum]
  have hq : (0 : ℚ) ≤ (((∑ m ∈ range (A.card + 1), Zhang.tCount F.graph Finset.univ A h m : ℕ) : ℤ) -
      (((F.n - A.card).choose h : ℕ) : ℤ) +
      ((((F.n - A.card).choose 2 : ℕ) : ℤ) -
        ((∑ m ∈ range (A.card + 1), Zhang.tCount F.graph Finset.univ A 2 m : ℕ) : ℤ)) *
        (((F.n - A.card - 2).choose (h - 2) : ℕ) : ℤ) : ℤ) := by
    exact_mod_cast this
  push_cast at hq ⊢
  linarith

/-- **The independent-pair extension rows (10)** on the inventory of a forest. -/
theorem forest_pairExtension_row (A : Finset (Fin F.n)) {h : ℕ} (h2 : 2 ≤ h) (hh : h ≤ F.n - A.card) :
    0 ≤ rowSlack F.n A.card (forestInv F A) (.pairExtension h) := by
  rw [rowSlack_pairExtension _ _ _ h2 hh]
  have := pairExtension_nonneg_inventory (G := F.graph) Finset.univ A h2
  rw [card_univ_sdiff_fin] at this
  simp only [bin_eq_choose]
  unfold forestInv
  rw [← Nat.cast_sum, ← Nat.cast_sum]
  have hq : (0 : ℚ) ≤ (((((F.n - A.card - 2).choose (h - 2) : ℕ) : ℤ) *
        ((∑ m ∈ range (A.card + 1), Zhang.tCount F.graph Finset.univ A 2 m : ℕ) : ℤ) -
      ((h.choose 2 : ℕ) : ℤ) *
        ((∑ m ∈ range (A.card + 1), Zhang.tCount F.graph Finset.univ A h m : ℕ) : ℤ) : ℤ) : ℚ) := by
    exact_mod_cast this
  push_cast at hq ⊢
  linarith

/-- **The excess-blocker rows (3)** on the inventory of a forest (Theorem 3.1 with the exposed-leaf
matching of Lemmas 2.1–2.2). -/
theorem forest_matching_row {A : Finset (Fin F.n)} (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card)
    {h : ℕ} (h2 : 2 ≤ h) (hh : h ≤ F.n - A.card) :
    0 ≤ rowSlack F.n A.card (forestInv F A) (.matchingExcess h) := by
  have hAi := isIndepFinset_of_isIndepSet hA
  have hAmax : A.card = Zhang.alphaIn F.graph Finset.univ :=
    (isMax_iff_card_eq_alphaIn hAi (Finset.subset_univ A)).mp
      (fun S _ hS => hmax S (isIndepSet_of_isIndepFinset hS))
  obtain ⟨μ, hμinj, hμ, hdeg⟩ := exists_saturating_matching_exposedLeaves F A hA hmax
  rw [Finset.compl_eq_univ_sdiff] at hμinj hμ hdeg
  have hc : (Finset.univ \ A).card = F.n - A.card := card_univ_sdiff_fin A
  have hM := matchingExcess_nonneg_of_exposedLeaves (G := F.graph) (A := A) (C := Finset.univ \ A)
    hμ hμinj hdeg h2 (by rw [hc]; exact hh)
  unfold matchingExcess at hM
  rw [← blockerCharge_cast (fun v hv => (hμ v hv).1) (fun v hv => (hμ v hv).2) hμinj h,
    blockerCharge_eq_sum_tCount, card_crossEdges_eq_sum_tCount, hc] at hM
  have hMq : (0 : ℚ) ≤ ((((((∑ m ∈ range (A.card + 1), (A.card - m) *
        Zhang.tCount F.graph Finset.univ A 1 m : ℕ) : ℤ) - ((F.n - A.card : ℕ) : ℤ)) *
        (((F.n - A.card - 2).choose (h - 1) : ℕ) : ℤ) +
      ((A.card : ℤ) - ((F.n - A.card : ℕ) : ℤ)) * (((F.n - A.card - 2).choose (h - 2) : ℕ) : ℤ) -
      ((∑ m ∈ range (A.card + 1), (A.card - m - h) * Zhang.tCount F.graph Finset.univ A h m : ℕ) : ℤ))
        : ℤ) : ℚ) := by
    exact_mod_cast hM
  push_cast at hMq
  have hsupp := forestInv_support hAi hAmax
  have hD : ∑ m ∈ range (A.card + 1), ((A.card - m : ℕ) : ℚ) *
        (Zhang.tCount F.graph Finset.univ A 1 m : ℚ) =
      ∑ m ∈ range (A.card + 1), ((A.card : ℚ) - m) * forestInv F A 1 m := by
    have := sum_natSub_cast A.card 0 (fun m => forestInv F A 1 m) (by
      intro m hm
      rcases hsupp 1 m hm with ⟨h0, -⟩ | ⟨-, -, h3⟩
      · omega
      · omega)
    simp only [Nat.sub_zero, Nat.cast_zero, sub_zero] at this
    exact this
  have hR : ∑ m ∈ range (A.card + 1), ((A.card - m - h : ℕ) : ℚ) *
        (Zhang.tCount F.graph Finset.univ A h m : ℚ) =
      ∑ m ∈ range (A.card + 1), ((A.card : ℚ) - m - h) * forestInv F A h m :=
    sum_natSub_cast A.card h (fun m => forestInv F A h m) (by
      intro m hm
      rcases hsupp h m hm with ⟨h0, -⟩ | ⟨-, -, h3⟩
      · omega
      · omega)
  rw [hD, hR] at hMq
  rw [rowSlack_matchingExcess _ _ _ h2 hh]
  simp only [bin_eq_choose]
  linarith

/-- **The inventory of a maximum independent set of a forest lies in the basic normalized inventory
relaxation** at `(F.n, |A|)`. -/
theorem forestInv_relaxation {A : Finset (Fin F.n)} (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card)
    (hn : 1 ≤ F.n) :
    Relaxation F.n A.card (forestInv F A) where
  nonneg := fun _ _ => Nat.cast_nonneg _
  support := by
    have hAi := isIndepFinset_of_isIndepSet hA
    have hAmax : A.card = Zhang.alphaIn F.graph Finset.univ :=
      (isMax_iff_card_eq_alphaIn hAi (Finset.subset_univ A)).mp
        (fun S _ hS => hmax S (isIndepSet_of_isIndepFinset hS))
    exact forestInv_support hAi hAmax
  empty := by
    unfold forestInv
    rw [Zhang.tCount_zero, if_pos rfl, Nat.cast_one]
  singleton := by
    unfold forestInv
    rw [← Nat.cast_sum, sum_fiber_one, card_univ_sdiff_fin]
  rows := by
    intro r hr
    cases r with
    | edgeBudget => exact forest_edge_row (isIndepFinset_of_isIndepSet hA) hn
    | matchingExcess h =>
      simp only [RowId.legal, Bool.and_eq_true, Nat.ble_eq] at hr
      exact forest_matching_row hA hmax hr.1 hr.2
    | subsetCount h =>
      simp only [RowId.legal, Bool.and_eq_true, Nat.ble_eq] at hr
      exact forest_subset_row A hr.2
    | missingEdgeUnion h =>
      simp only [RowId.legal, Bool.and_eq_true, Nat.ble_eq] at hr
      exact forest_edgeUnion_row A (by omega) hr.2
    | pairExtension h =>
      simp only [RowId.legal, Bool.and_eq_true, Nat.ble_eq] at hr
      exact forest_pairExtension_row A (by omega) hr.2

end Forest

/-- **Soundness of the certificate ledger for forests (M2).**  Let `A` be an independent set of maximum
cardinality of the finite forest `F`, and let `c` be a certificate with `c.ok = true` and key
`(F.n, |A|, k)`.  Then the independence sequence of `F` has no weak valley at `k`. -/
theorem noWeakValley_of_cert (F : FiniteForest) {A : Finset (Fin F.n)}
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card)
    (c : Cert) (hc : c.ok = true) {k : ℕ} (hkey : c.key = (F.n, A.card, k)) :
    ¬ (independenceCount F k ≤ independenceCount F (k - 1) ∧
        independenceCount F k ≤ independenceCount F (k + 1)) := by
  classical
  simp only [Cert.key, Prod.mk.injEq] at hkey
  obtain ⟨hcn, hca, hck⟩ := hkey
  obtain ⟨hn, -⟩ := Cert.ok_spec hc
  have hrel : Relaxation c.n c.a (forestInv F A) := by
    rw [hcn, hca]
    exact forestInv_relaxation hA hmax (by omega)
  have hnv := c.noValley hc hrel
  rw [hcn, hca, hck] at hnv
  have hAi := isIndepFinset_of_isIndepSet hA
  simp only [invCoeff_forestInv hAi] at hnv
  rintro ⟨h1, h2⟩
  exact hnv ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

end Fiber
end Erdos993Lean
