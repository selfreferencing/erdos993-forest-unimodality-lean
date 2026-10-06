import Erdos993Lean.Analytic.TopCore
import Erdos993Lean.Analytic.HardCore.Mixture

/-!
# The analytic route from a size threshold `N`: the inputs O1, O2, O3, O5 at `n ≥ N`

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A19.  Sources: the interface
`Erdos993Lean/Analytic/Defs.lean` (whose inputs are stated for `61 ≤ F.n`) and the assembly
`Erdos993Lean/Analytic/Top.lean` (`noWeakValley_of_analytic_inputs`), whose proof is copied here with the size
hypothesis `61 ≤ F.n` replaced by `N ≤ F.n`; lane R52's scoping report `LEAN/r52/REQUIREMENTS_52.md` §8 (the size
hypothesis appears only in the statements of O1, O2, O3, O5 and in their consumers).

`Defs.lean` is not edited.  The inputs with a general threshold `N`:

* `VarianceBoundN N P`, `VarianceRatioBoundN N P`, `TailBoundN N P`, `DensityBoundN N P`: O1, O2, O3, O5 of
  `Defs.lean` with `N ≤ F.n` in place of `61 ≤ F.n` (at `N = 61` they are `Defs.lean`'s, by `Iff.rfl`:
  `varianceBoundN_61`, …);
* `AnalyticInputsN N P`: the four inputs at `n ≥ N` and O4 (`ThresholdNoValley P`, which has no size hypothesis).

Results:
* **`noWeakValley_of_inputsN`**: for a forest with `n ≥ N`, the inputs exclude a weak valley at every interior rank
  `⌈n/4⌉ < k < h_B` (the proof of `Top.lean`'s `noWeakValley_of_analytic_inputs`, with lane A1's `mixtureFacts`);
* **`unimodal_of_inputsN`**: every forest with `n ≥ N` has a unimodal independence sequence
  (`unimodal_of_noWeakValley_window`).  No finite certificate is used.

Scalarity check: nothing new is carried.  The fields of the profile `P` are consumed exactly as in `Top.lean`
(`θb` the second moment of `δ`, `Db` the variance of the free count `M`, `Tb`/`M1b` its lower tail, `mfloor` the
expected free count `m = E M`); `N` is the size of the forest, consumed only by the four inputs.
-/

namespace Erdos993Lean.Analytic.N52

open Finset

section Inputs

variable (N : ℕ) (P : Profile)

/-- **O1 at `n ≥ N`** (`VarianceBound` with the threshold `N`). -/
def VarianceBoundN : Prop :=
  ∀ F : FiniteForest, N ≤ F.n → ∀ t : ℝ, InRange t → AtInteriorRank F t →
    ∀ B, IsMaxWeight F t B →
    (forestMixture F B t).varM ≤ P.Db t * (forestMixture F B t).meanM

/-- **O2 at `n ≥ N`** (`VarianceRatioBound` with the threshold `N`). -/
def VarianceRatioBoundN : Prop :=
  ∀ F : FiniteForest, N ≤ F.n → ∀ t : ℝ, InRange t → AtInteriorRank F t →
    ∀ B, IsMaxWeight F t B →
    hardCoreVar F t ≤ (1 + P.θb t) * (1 - actQ t) * weightW F t B

/-- **O3 at `n ≥ N`** (`TailBound` with the threshold `N`). -/
def TailBoundN : Prop :=
  ∀ F : FiniteForest, N ≤ F.n → ∀ t : ℝ, InRange t → AtInteriorRank F t →
    ∀ B, IsMaxWeight F t B →
    ∀ M' : ℕ, M' < P.M1b t (forestMixture F B t).meanM →
      (forestMixture F B t).cdfM M' ≤ P.Tb t (forestMixture F B t).meanM M'

/-- **O5 at `n ≥ N`** (`DensityBound` with the threshold `N`). -/
def DensityBoundN : Prop :=
  ∀ F : FiniteForest, N ≤ F.n → ∀ t : ℝ, InRange t → AtInteriorRank F t →
    ∀ B, IsMaxWeight F t B →
    P.mfloor t ≤ (forestMixture F B t).meanM

/-- **The analytic inputs at `n ≥ N`**: O1, O2, O3, O5 for the forests with at least `N` vertices, and O4. -/
structure AnalyticInputsN : Prop where
  o1 : VarianceBoundN N P
  o2 : VarianceRatioBoundN N P
  o3 : TailBoundN N P
  o4 : ThresholdNoValley P
  o5 : DensityBoundN N P

theorem varianceBoundN_61 : VarianceBoundN 61 P ↔ VarianceBound P := Iff.rfl

theorem varianceRatioBoundN_61 : VarianceRatioBoundN 61 P ↔ VarianceRatioBound P := Iff.rfl

theorem tailBoundN_61 : TailBoundN 61 P ↔ TailBound P := Iff.rfl

theorem densityBoundN_61 : DensityBoundN 61 P ↔ DensityBound P := Iff.rfl

/-- At `N = 61` the inputs are those of `Defs.lean`. -/
theorem analyticInputsN_61 : AnalyticInputsN 61 P ↔ AnalyticInputs P :=
  ⟨fun h => ⟨h.o1, h.o2, h.o3, h.o4, h.o5⟩, fun h => ⟨h.o1, h.o2, h.o3, h.o4, h.o5⟩⟩

end Inputs

variable {N : ℕ} {P : Profile}

/-- **No weak valley at the interior ranks of a forest with `n ≥ N`**, from the inputs at `n ≥ N` (the proof of
`noWeakValley_of_analytic_inputs`, `Top.lean`, with `N ≤ F.n` for `61 ≤ F.n` and lane A1's `mixtureFacts`). -/
theorem noWeakValley_of_inputsN (h : AnalyticInputsN N P) (F : FiniteForest) (hn : N ≤ F.n) (k : ℕ)
    (hk1 : (F.n + 3) / 4 < k) (hk2 : k < hB F) :
    ¬ (independenceCount F k ≤ independenceCount F (k - 1) ∧
        independenceCount F k ≤ independenceCount F (k + 1)) := by
  have hmix := mixtureFacts
  -- the activity with `μ_F(t) = k` (O6, option (b)) and a maximum-weight independent set
  obtain ⟨t, hR, ht, hI, hμ⟩ := exists_activity_inRange F k hk1 hk2
  obtain ⟨B, hBmax⟩ := hmix.exists_maxWeight F t ht
  have hBind : F.graph.IsIndepSet (B : Set (Fin F.n)) := hBmax.1
  -- the no-valley property at `q = t/(1 + t)` and `m = E M`: O5 gives `m ≥ mfloor t`, then O4
  have hNV := h.o4 t hR (forestMixture F B t).meanM (h.o5 F hn t hR hI B hBmax)
  -- the second moment of `δ`: `E δ² = V − q(1 − q) m ≤ θ q(1 − q) m` (O2 and `q m = W`)
  have hδ2 : (forestMixture F B t).expect (fun M Y => delta (actQ t) k M Y ^ 2) ≤
      P.θb t * (actQ t * (1 - actQ t)) * (forestMixture F B t).meanM := by
    rw [hmix.var_delta F t B ht hBind k hμ]
    have hO2 := h.o2 F hn t hR hI B hBmax
    rw [← hmix.weight_eq F t B ht hBind] at hO2
    linarith
  -- T1's conclusion for the forest mixture
  have hnv : ¬ (forestMixture F B t).WeakValley (actQ t) k :=
    hNV (Finset (Fin F.n)) (forestMixture F B t) k (hmix.isProb F t B ht hBind) rfl
      (hmix.mean_delta F t B ht hBind k hμ) hδ2 (h.o1 F hn t hR hI B hBmax)
      (h.o3 F hn t hR hI B hBmax)
  -- back to the counts
  exact not_valley_of_not_weakValley F (forestMixture F B t) ht (by omega)
    (hmix.prob_eq F t B ht hBind (k - 1)) (hmix.prob_eq F t B ht hBind k)
    (hmix.prob_eq F t B ht hBind (k + 1)) hnv

/-- **Unimodality of every forest with `n ≥ N`, from the inputs at `n ≥ N`** (the rising prefix below `⌈n/4⌉`,
no weak valley at the interior ranks, the tail B6 from `h_B` on; no finite certificate). -/
theorem unimodal_of_inputsN (h : AnalyticInputsN N P) (F : FiniteForest) (hn : N ≤ F.n) :
    independenceSequenceUnimodal F := by
  unfold independenceSequenceUnimodal
  exact unimodalUpTo_of_unimodal (unimodal_of_noWeakValley_window F
    (fun k hk1 hk2 => noWeakValley_of_inputsN h F hn k hk1 hk2))

end Erdos993Lean.Analytic.N52
