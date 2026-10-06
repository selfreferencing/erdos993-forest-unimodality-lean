import Mathlib
import Erdos993Lean.Fiber.CertData24
import Erdos993Lean.Fiber.Ledger
import Erdos993Lean.Analytic.TopCore
import Erdos993Lean.Ceiling.Join
import Erdos993Lean.Ceiling.Statement

/-!
# Proof 3 of the floor: every forest with at most 24 vertices is unimodal, without enumerating forests

Source: the 29 Sep 2026 binomial-fiber return (`BINOMIAL_FIBER_COMPLETION/PROOF.md`), Section 6
(Theorem 6.2 restricted to order 24, Corollary 6.3). Lean lane B; paper `TWIN_v1.5`, Part I
Theorem `p1:thm:main` and certificate theorem `p1:thm:certificates`.

For a finite forest `F` with `n ≤ 24` vertices, choose an independent set `A` of maximum cardinality
(`exists_maxIndep`), `a = |A|`.

* **Edgeless** (`a = n`): every vertex set is independent, `i_k = C(n, k)`, and the binomial
  coefficients have no weak valley at `0 < k < n` (`choose_noWeakValley`).
* **Otherwise** (`a < n`): `ν(F) = n − a` (`matchingNumber_eq_of_maxIndep`, Lemma 2.1) and `n − a ≤ a`
  (`card_compl_le_card`), so B7 (`Join.hB_le`) gives `h_B ≤ ⌈(n + 2a)/6⌉ ≤ a`; hence every window rank
  `⌈n/4⌉ < k < h_B` lies in the parameter domain (11) (`mem_paramDomain`), which is exactly the list of
  keys of the 249 kernel-checked certificates (`certs_cover`, `certs_ok`), and the certificate
  ledger (`noWeakValley_of_cert`) excludes a weak valley at `k`.

The window consumer `Analytic.unimodal_of_noWeakValley_window` (the rising prefix below `⌈n/4⌉` and the
matching-skeleton tail from `h_B`) turns "no weak valley on the window" into unimodality.

* **`unimodal_of_card_le_24 : ∀ F : FiniteForest, F.n ≤ 24 → independenceSequenceUnimodal F`**;
* **`floorStatement_25_fiber : FloorStatement 25`**.

No forest is enumerated: the only finite computation is the kernel evaluation of the checker on the 249
parameter certificates (the retained 130 in `Erdos993Lean/Fiber/CertData.lean` and the added 119 in
`Erdos993Lean/Fiber/CertData24.lean`, `decide +kernel`).

Grade: PROVED IN LEAN (complete proofs, standard axioms only).
-/

namespace Erdos993Lean
namespace Fiber

open Finset

/-- The binomial coefficients `C(n, k)` have no weak valley at `0 < k < n`. -/
theorem choose_noWeakValley {n k : ℕ} (hk0 : 0 < k) (hkn : k < n) :
    ¬ (n.choose k ≤ n.choose (k - 1) ∧ n.choose k ≤ n.choose (k + 1)) := by
  rintro ⟨h1, h2⟩
  have e1 : n.choose (k + 1) * (k + 1) = n.choose k * (n - k) := Nat.choose_succ_right_eq n k
  have e2 : n.choose k * k = n.choose (k - 1) * (n - (k - 1)) := by
    have := Nat.choose_succ_right_eq n (k - 1)
    rwa [Nat.sub_add_cancel hk0] at this
  have hp1 : 0 < n.choose (k - 1) := Nat.choose_pos (by omega)
  have hp2 : 0 < n.choose k := Nat.choose_pos hkn.le
  rcases le_or_gt (2 * k) n with hle | hlt
  · have hge : k + 1 ≤ n - (k - 1) := by omega
    have h3 := Nat.mul_le_mul_left (n.choose (k - 1)) hge
    have h4 := Nat.mul_le_mul_right k h1
    nlinarith
  · have hle : n - k ≤ k := by omega
    have h3 := Nat.mul_le_mul_left (n.choose k) hle
    have h4 := Nat.mul_le_mul_right (k + 1) h2
    nlinarith

/-- If the whole vertex set is independent, `i_r = C(n, r)`. -/
theorem independenceCount_of_indep_univ (F : FiniteForest)
    (h : F.graph.IsIndepSet (Set.univ : Set (Fin F.n))) (r : ℕ) :
    independenceCount F r = F.n.choose r := by
  classical
  unfold independenceCount
  have e : F.graph.indepSetFinset r = (Finset.univ : Finset (Fin F.n)).powersetCard r := by
    ext t
    rw [SimpleGraph.mem_indepSetFinset_iff, SimpleGraph.isNIndepSet_iff, Finset.mem_powersetCard]
    constructor
    · rintro ⟨-, ht⟩
      exact ⟨Finset.subset_univ t, ht⟩
    · rintro ⟨-, ht⟩
      refine ⟨?_, ht⟩
      intro x _ y _ hxy
      exact h (Set.mem_univ x) (Set.mem_univ y) hxy
  rw [e, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- **Proof 3 of the floor (TWIN_v1.5 Part I, Theorem 6.2 restricted to order 24)**: every finite forest with at most 24 vertices
has a unimodal independence sequence — by the binomial-fiber ledger and its 249 kernel-checked parameter
certificates, without enumerating forests. -/
theorem unimodal_of_card_le_24 : ∀ F : FiniteForest, F.n ≤ 24 → independenceSequenceUnimodal F := by
  intro F hF
  classical
  obtain ⟨A, hA, hmax⟩ := exists_maxIndep F
  unfold independenceSequenceUnimodal
  apply unimodalUpTo_of_unimodal
  apply Analytic.unimodal_of_noWeakValley_window F
  intro k hk1 hk2
  have hB := Join.hB_le F
  rw [matchingNumber_eq_of_maxIndep F A hA hmax] at hB
  have hAn : A.card ≤ F.n := by
    have := Finset.card_le_univ A
    rwa [Fintype.card_fin] at this
  by_cases hedge : A.card = F.n
  · -- edgeless: `A` is the whole vertex set
    have hAu : A = Finset.univ := Finset.eq_univ_of_card A (by rw [hedge, Fintype.card_fin])
    have hu : F.graph.IsIndepSet (Set.univ : Set (Fin F.n)) := by
      rw [← Finset.coe_univ, ← hAu]
      exact hA
    rw [independenceCount_of_indep_univ F hu, independenceCount_of_indep_univ F hu,
      independenceCount_of_indep_univ F hu]
    exact choose_noWeakValley (by omega) (by omega)
  · have hca := card_compl_le_card F A hA hmax
    rw [Finset.card_compl, Fintype.card_fin] at hca
    have hmem : (F.n, A.card, k) ∈ paramDomain 24 :=
      mem_paramDomain.mpr ⟨by omega, hF, by omega, by omega, hk1, by omega, by omega⟩
    rw [← Order24.certs_cover] at hmem
    obtain ⟨c, hc, hkey⟩ := List.mem_map.mp hmem
    exact noWeakValley_of_cert F hA hmax c (Order24.certs_ok c hc) hkey

/-- **The floor at 25 from the binomial-fiber consumer.** -/
theorem floorStatement_25_fiber : FloorStatement 25 :=
  fun F hF => unimodal_of_card_le_24 F (by omega)

/-- Compatibility with the original floor (Part I, Theorem 6.2 through order 20). -/
theorem unimodal_of_card_le_20 (F : FiniteForest) (hF : F.n ≤ 20) :
    independenceSequenceUnimodal F :=
  unimodal_of_card_le_24 F (by omega)

/-- Compatibility with the original floor at 21 (Part I, Corollary 6.3). -/
theorem floorStatement_21_fiber : FloorStatement 21 :=
  fun F hF => unimodal_of_card_le_24 F (by omega)

end Fiber
end Erdos993Lean
