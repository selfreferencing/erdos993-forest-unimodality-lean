import Mathlib
import Erdos993Lean.Analytic.MGF.Criterion
import Erdos993Lean.Analytic.MGF.Checker
import Erdos993Lean.Analytic.Atlas.Atoms

/-!
# The MGF + two-sided atlas (lane A22): the two-sided kernel and what the atom checks mean

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A22.  Sources: `LEAN/atlas_mgf/SPEC.md` v2 §3 (F) and M30's
`ATLAS_MGF_PROOF.md`, lane R3X's `REACH_BELOW_44.md` §2.3, lane A9's `Atlas/Kernel.lean` (`κ = W P`, Soul's first-order
q-uniform bound), `Atlas/Taylor.lean` (the second-order bound) and `Atlas/Atoms.lean` (the atom checks), whose proofs
are repeated here with the two-sided coefficients; the checker `Erdos993Lean/Analytic/MGF/Checker.lean`.

## The two-sided kernel

For `0 ≤ j ≤ M` and `0 < x < 1`: `f_L = (1 − x) b_M(j) a_j` and `f_R = x b_M(j) b_j` with Soul's coefficients
`a_j = (M + 1 − 2j)/(M − j + 1)`, `b_j = (2j + 1 − M)/(j + 1)` (`fL_eq`, `fR_eq`), hence
`κ₂ := a f_L/x + b f_R/(1 − x) = W(x) · [(a a_j)(1 − x)² + (b b_j) x²]` (`kernel2_eq_WP`): the same factorisation as
`κ = W P`, with the quadratic `P` of the coefficients `a a_j, b b_j`.  The elementary bound is `κ₂ ≥ −max(a, b)`
(`kernel2_ge_neg_max`: `f_L/x ≥ −b_M(j − 1)`, `f_R/(1 − x) ≥ −b_M(j + 1)` and `b_M(j − 1) + b_M(j + 1) ≤ 1`).

## Results (namespace `Erdos993Lean.Analytic.MGF`)

* `fL_eq`, `fR_eq`, **`kernel2_eq_WP`**; `kernel2_neg_one` (`κ₂(M, −1) = −b(1 − q)^M`), `kernel2_top`
  (`κ₂(M, M + 1) = −a q^M`), `kernel2_of_lt`, `kernel2_of_gt` (`κ₂ = 0` outside `[−1, M + 1]`).
* `binom_pair_le_one`, `fL_div_ge`, `fR_div_ge`, **`kernel2_ge_neg_max`**, `kernel2_ge_kapB` (the checker's
  `B = max(a, b)`).
* **`kernel2_ge_firstOrder`**, **`kernel2_ge_secondOrder`**, `kernel2_neg_one_ge_secondOrder`,
  `kernel2_top_ge_secondOrder`: Soul's first- and second-order q-uniform bounds for `κ₂ + cδ + νδ²`.
* `kapRow2_cast`, `MBox.q0_cast`, `MBox.rad_cast`, `MBox.piQ_cast`, `MBox.vtx_cast`, `joint_cast`, `pricedQ_cast`.
* `skip_sound`, `distMin_le`, **`atomSkip_sound`**, **`atomMid2_sound`, `atomNeg2_sound`, `atomTop2_sound`,
  `atomAt2_sound`, `atomsFrom2_sound`**: a passing atom `(M, j)`, `−1 ≤ j ≤ M + 1`, gives the pointwise bound
  `rhs ≤ κ₂_q(M, j) + c(j − qM) + ν(j − qM)²` for every `q ∈ [ql, qh]`.

All results use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

open Erdos993Lean.Analytic Erdos993Lean.Analytic.Atlas Erdos993Lean.Analytic.NoValley

namespace Erdos993Lean.Analytic.MGF

/-! ## The two-sided kernel factorised -/

/-- `f_L(M, j) = (1 − x) b_M(j) a_j` for `0 ≤ j ≤ M`, `a_j = (M + 1 − 2j)/(M − j + 1)`. -/
theorem fL_eq {M j : ℕ} (hj : j ≤ M) (x : ℝ) : fL x M j = (1 - x) * binom M x j * coefAR M j := by
  have hl := binom_rel_left hj x
  have hA : (M : ℝ) - j + 1 ≠ 0 := by
    have : (j : ℝ) ≤ M := by exact_mod_cast hj
    linarith
  unfold fL coefAR
  rw [mul_div_assoc', eq_div_iff hA]
  have hA' : (M : ℝ) + 1 - j = (M : ℝ) - j + 1 := by ring
  rw [hA'] at hl
  linear_combination (-1 : ℝ) * hl

/-- `f_R(M, j) = x b_M(j) b_j` for `0 ≤ j ≤ M`, `b_j = (2j + 1 − M)/(j + 1)`. -/
theorem fR_eq {M j : ℕ} (hj : j ≤ M) (x : ℝ) : fR x M j = x * binom M x j * coefBR M j := by
  have hr := binom_rel_right hj x
  have hB : (j : ℝ) + 1 ≠ 0 := by positivity
  unfold fR coefBR
  rw [mul_div_assoc', eq_div_iff hB]
  linear_combination hr

/-- **`κ₂ = W·P` with the two-sided coefficients**: for `0 ≤ j ≤ M` and `0 < x < 1`,
`a f_L/x + b f_R/(1 − x) = W(x) · [(a a_j)(1 − x)² + (b b_j) x²]`. -/
theorem kernel2_eq_WP {M j : ℕ} (hj : j ≤ M) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (a b : ℝ) :
    kernel2 x a b M j = Wf M j x * Pf (a * coefAR M j) (b * coefBR M j) x := by
  have h0 : x ≠ 0 := hx0.ne'
  have h1 : 1 - x ≠ 0 := by linarith
  unfold kernel2 Wf Pf
  rw [fL_eq hj, fR_eq hj]
  field_simp
  try ring

/-- `κ₂(M, −1) = −b(1 − q)^M`. -/
theorem kernel2_neg_one {q : ℝ} (hq1 : q < 1) (a b : ℝ) (M : ℕ) :
    kernel2 q a b M (-1) = -(b * (1 - q) ^ M) := by
  have h1 : (1 - q) ≠ 0 := by linarith
  have e0 : binom M q (-1 + 1) = (1 - q) ^ M := by
    rw [show (-1 : ℤ) + 1 = ((0 : ℕ) : ℤ) by norm_num, binom_natCast_of_le q (Nat.zero_le M)]
    simp
  unfold kernel2 fL fR
  rw [binom_of_neg (by norm_num : (-1 : ℤ) < 0), binom_of_neg (by norm_num : (-1 : ℤ) - 1 < 0), e0]
  field_simp
  try ring

/-- `κ₂(M, M + 1) = −a q^M`. -/
theorem kernel2_top {q : ℝ} (hq0 : 0 < q) (a b : ℝ) (M : ℕ) :
    kernel2 q a b M ((M : ℤ) + 1) = -(a * q ^ M) := by
  have h0 : q ≠ 0 := hq0.ne'
  have e0 : binom M q ((M : ℤ) + 1 - 1) = q ^ M := by
    rw [show (M : ℤ) + 1 - 1 = ((M : ℕ) : ℤ) by ring, binom_natCast_of_le q le_rfl]
    simp
  unfold kernel2 fL fR
  rw [binom_of_gt (by omega : (M : ℤ) < (M : ℤ) + 1), binom_of_gt (by omega : (M : ℤ) < (M : ℤ) + 1 + 1),
    e0]
  field_simp
  try ring

theorem kernel2_of_lt {q a b : ℝ} {M : ℕ} {j : ℤ} (hj : j < -1) : kernel2 q a b M j = 0 := by
  unfold kernel2 fL fR
  rw [binom_of_neg (by omega : j < 0), binom_of_neg (by omega : j - 1 < 0),
    binom_of_neg (by omega : j + 1 < 0)]
  ring

theorem kernel2_of_gt {q a b : ℝ} {M : ℕ} {j : ℤ} (hj : (M : ℤ) + 1 < j) : kernel2 q a b M j = 0 := by
  unfold kernel2 fL fR
  rw [binom_of_gt (by omega : (M : ℤ) < j), binom_of_gt (by omega : (M : ℤ) < j - 1),
    binom_of_gt (by omega : (M : ℤ) < j + 1)]
  ring

/-! ## The elementary bound `κ₂ ≥ −max(a, b)` -/

/-- Two distinct binomial masses sum to at most one: `b_M(j − 1) + b_M(j + 1) ≤ 1`. -/
theorem binom_pair_le_one {M : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (j : ℤ) :
    binom M q (j - 1) + binom M q (j + 1) ≤ 1 := by
  rcases lt_or_ge (j - 1) 0 with hneg | hnn
  · rw [binom_of_neg hneg, zero_add]
    exact binom_le_one hq0 hq1 _
  rcases lt_or_ge (M : ℤ) (j + 1) with hbig | hle
  · rw [binom_of_gt hbig, add_zero]
    exact binom_le_one hq0 hq1 _
  -- both indices in `[0, M]`: two distinct terms of a sum equal to `1`
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = j - 1 := ⟨(j - 1).toNat, Int.toNat_of_nonneg hnn⟩
  have hn2 : j + 1 = ((n + 2 : ℕ) : ℤ) := by push_cast; omega
  rw [← hn, hn2]
  have hnM : n + 2 ≤ M := by omega
  have hsum := sum_binom M q
  have hsub : ({n, n + 2} : Finset ℕ) ⊆ Finset.range (M + 1) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp only [Finset.mem_range] <;> omega
  have h := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun i : ℕ => binom M q (i : ℤ)) (fun i _ _ => binom_nonneg hq0 hq1 _)
  rw [Finset.sum_pair (by omega : n ≠ n + 2), hsum] at h
  exact h

/-- `f_L/q ≥ −b_M(j − 1)` for `0 < q < 1`. -/
theorem fL_div_ge {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (M : ℕ) (j : ℤ) :
    -binom M q (j - 1) ≤ fL q M j / q := by
  have hb := binom_nonneg (M := M) hq0.le hq1.le j
  have e : fL q M j / q = (1 - q) / q * binom M q j - binom M q (j - 1) := by
    unfold fL; field_simp; try ring
  rw [e]
  have : 0 ≤ (1 - q) / q * binom M q j := mul_nonneg (div_nonneg (by linarith) hq0.le) hb
  linarith

/-- `f_R/(1 − q) ≥ −b_M(j + 1)` for `0 < q < 1`. -/
theorem fR_div_ge {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (M : ℕ) (j : ℤ) :
    -binom M q (j + 1) ≤ fR q M j / (1 - q) := by
  have hb := binom_nonneg (M := M) hq0.le hq1.le j
  have h1 : (1 - q) ≠ 0 := by linarith
  have e : fR q M j / (1 - q) = q / (1 - q) * binom M q j - binom M q (j + 1) := by
    unfold fR; field_simp; try ring
  rw [e]
  have : 0 ≤ q / (1 - q) * binom M q j := mul_nonneg (div_nonneg hq0.le (by linarith)) hb
  linarith

/-- **The elementary bound** `a f_L/q + b f_R/(1 − q) ≥ −max(a, b)` for `a, b ≥ 0` (SPEC v2 §3). -/
theorem kernel2_ge_neg_max {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (M : ℕ)
    (j : ℤ) : -(max a b) ≤ kernel2 q a b M j := by
  have hL := fL_div_ge hq0 hq1 M j
  have hR := fR_div_ge hq0 hq1 M j
  have hpair := binom_pair_le_one (M := M) hq0.le hq1.le j
  have hp := binom_nonneg (M := M) hq0.le hq1.le (j - 1)
  have hr := binom_nonneg (M := M) hq0.le hq1.le (j + 1)
  have hamax : a ≤ max a b := le_max_left a b
  have hbmax : b ≤ max a b := le_max_right a b
  have e1 : a * fL q M j / q = a * (fL q M j / q) := by ring
  have e2 : b * fR q M j / (1 - q) = b * (fR q M j / (1 - q)) := by ring
  unfold kernel2
  rw [e1, e2]
  nlinarith [mul_le_mul_of_nonneg_left hL ha, mul_le_mul_of_nonneg_left hR hb,
    mul_le_mul_of_nonneg_right hamax hp, mul_le_mul_of_nonneg_right hbmax hr]

/-- The checker's `B = max(a, b)`: `κ₂ ≥ −B` on the whole box. -/
theorem kernel2_ge_kapB {b : MBox} (h0 : (0 : ℝ) < b.ql) (h1 : (b.qh : ℝ) < 1) (ha : 0 ≤ b.a) (hb : 0 ≤ b.b)
    (M : ℕ) {q : ℝ} (hq : (b.ql : ℝ) ≤ q) (hq' : q ≤ b.qh) (j : ℤ) :
    -((b.kapB : ℚ) : ℝ) ≤ kernel2 q b.a b.b M j := by
  have hq0 : 0 < q := by linarith
  have hq1 : q < 1 := by linarith
  have haR : (0 : ℝ) ≤ b.a := by exact_mod_cast ha
  have hbR : (0 : ℝ) ≤ b.b := by exact_mod_cast hb
  have h := kernel2_ge_neg_max hq0 hq1 haR hbR M j
  unfold MBox.kapB
  rw [qmax_cast]
  exact h

/-! ## Soul's first-order q-uniform bound for the two-sided kernel -/

/-- **Soul's first-order q-uniform bound** for `κ₂` and `0 ≤ j ≤ M` (`Atlas/Kernel.lean` `kappa_ge_firstOrder` with
`κ₂ = W P` for the quadratic of the coefficients `a a_j, b b_j`): with `q0 = (ql + qh)/2`, `W ≤ w`, `|P| ≤ p`,
`|P'| ≤ d`, `|L| ≤ l` on `[ql, qh] ⊆ (0, 1)`, for every `q ∈ [ql, qh]`:
`κ₂_q(M, j) ≥ κ₂_{q0}(M, j) − ((qh − ql)/2) w (d + l p)`. -/
theorem kernel2_ge_firstOrder {M j : ℕ} (hj : j ≤ M) {ql qh q w pa dp la : ℝ} (h0 : 0 < ql)
    (hlh : ql ≤ qh) (h1 : qh < 1) (hq : ql ≤ q) (hq' : q ≤ qh) (a b : ℝ)
    (hW : ∀ x, ql ≤ x → x ≤ qh → Wf M j x ≤ w)
    (hP : ∀ x, ql ≤ x → x ≤ qh → |Pf (a * coefAR M j) (b * coefBR M j) x| ≤ pa)
    (hdP : ∀ x, ql ≤ x → x ≤ qh → |dPf (a * coefAR M j) (b * coefBR M j) x| ≤ dp)
    (hL : ∀ x, ql ≤ x → x ≤ qh → |Lf M j x| ≤ la) :
    kernel2 ((ql + qh) / 2) a b M j - (qh - ql) / 2 * (w * (dp + la * pa)) ≤ kernel2 q a b M j := by
  have hq0l : ql ≤ (ql + qh) / 2 := by linarith
  have hq0h : (ql + qh) / 2 ≤ qh := by linarith
  set q0 := (ql + qh) / 2 with hq0
  set a' := a * coefAR M j
  set b' := b * coefBR M j
  have hmvt : |Wf M j q - Wf M j q0| ≤ w * la * |q - q0| := by
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := Wf M j)
      (f' := fun x => Wf M j x * Lf M j x) (s := Set.Icc ql qh) (C := w * la)
      (fun x hx => (hasDerivAt_Wf hj (by linarith [hx.1]) (by linarith [hx.2])).hasDerivWithinAt)
      (fun x hx => by
        rw [Real.norm_eq_abs, abs_mul]
        have hWx := Wf_pos hj (x := x) (by linarith [hx.1]) (by linarith [hx.2])
        rw [abs_of_pos hWx]
        exact mul_le_mul (hW x hx.1 hx.2) (hL x hx.1 hx.2) (abs_nonneg _)
          (hWx.le.trans (hW x hx.1 hx.2)))
      (convex_Icc ql qh) ⟨hq0l, hq0h⟩ ⟨hq, hq'⟩
    simpa [Real.norm_eq_abs] using this
  have hk := kernel2_eq_WP hj (x := q) (by linarith) (by linarith) a b
  have hk0 := kernel2_eq_WP hj (x := q0) (by linarith) (by linarith) a b
  have hPd : |Pf a' b' q - Pf a' b' q0| ≤ dp * |q - q0| := by
    rw [Pf_sub a' b' q0 q, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hdP _ (by linarith) (by linarith)) (abs_nonneg _)
  have hW0 := Wf_pos hj (x := q0) (by linarith) (by linarith)
  have hw0 : 0 ≤ w := hW0.le.trans (hW q0 hq0l hq0h)
  have hla : 0 ≤ la := (abs_nonneg _).trans (hL q hq hq')
  have hpa : 0 ≤ pa := (abs_nonneg _).trans (hP q hq hq')
  have hdp : 0 ≤ dp := (abs_nonneg _).trans (hdP q hq hq')
  have e : kernel2 q a b M j - kernel2 q0 a b M j =
      (Wf M j q - Wf M j q0) * Pf a' b' q + Wf M j q0 * (Pf a' b' q - Pf a' b' q0) := by
    rw [hk, hk0]; ring
  have hb : |kernel2 q a b M j - kernel2 q0 a b M j| ≤ w * (dp + la * pa) * |q - q0| := by
    rw [e]
    calc |(Wf M j q - Wf M j q0) * Pf a' b' q + Wf M j q0 * (Pf a' b' q - Pf a' b' q0)|
        ≤ |Wf M j q - Wf M j q0| * |Pf a' b' q| + |Wf M j q0| * |Pf a' b' q - Pf a' b' q0| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ (w * la * |q - q0|) * pa + w * (dp * |q - q0|) := by
          rw [abs_of_pos hW0]
          gcongr
          · exact hP q hq hq'
          · exact hW q0 hq0l hq0h
      _ = w * (dp + la * pa) * |q - q0| := by ring
  have hrad : |q - q0| ≤ (qh - ql) / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hK : 0 ≤ w * (dp + la * pa) := by positivity
  have := neg_abs_le (kernel2 q a b M j - kernel2 q0 a b M j)
  nlinarith [mul_le_mul_of_nonneg_left hrad hK]

/-! ## Soul's second-order bound for the two-sided kernel -/

/-- **Soul's second-order bound, atoms `0 ≤ j ≤ M`** (`Atlas/Taylor.lean` `kappa_ge_secondOrder` with
`κ₂ = W P`, `P` of the coefficients `a a_j, b b_j`). -/
theorem kernel2_ge_secondOrder {M j : ℕ} (hj : j ≤ M) {ql qh q wm pa dp la lp c mu : ℝ}
    (h0 : 0 < ql) (hlh : ql ≤ qh) (h1 : qh < 1) (hq : ql ≤ q) (hq' : q ≤ qh) (hmu : 0 ≤ mu) (a b : ℝ)
    (hW : ∀ x, ql ≤ x → x ≤ qh → Wf M j x ≤ wm)
    (hP : ∀ x, ql ≤ x → x ≤ qh → |Pf (a * coefAR M j) (b * coefBR M j) x| ≤ pa)
    (hdP : ∀ x, ql ≤ x → x ≤ qh → |dPf (a * coefAR M j) (b * coefBR M j) x| ≤ dp)
    (hL : ∀ x, ql ≤ x → x ≤ qh → |Lf M j x| ≤ la)
    (hLp : ∀ x, ql ≤ x → x ≤ qh → |Lpf M j x| ≤ lp) :
    kernel2 ((ql + qh) / 2) a b M j +
        (mu * (((j : ℝ) - (ql + qh) / 2 * M) * ((j : ℝ) - (ql + qh) / 2 * M)) +
          c * ((j : ℝ) - (ql + qh) / 2 * M)) -
      (qh - ql) / 2 * |k1f M j (a * coefAR M j) (b * coefBR M j) ((ql + qh) / 2) -
        (M : ℝ) * (c + 2 * mu * ((j : ℝ) - (ql + qh) / 2 * M))| -
      (qh - ql) / 2 * ((qh - ql) / 2) *
        (wm * (|2 * (a * coefAR M j + b * coefBR M j)| + 2 * la * dp + (la * la + lp) * pa) +
          2 * mu * ((M : ℝ) * (M : ℝ))) / 2 ≤
      kernel2 q a b M j + c * ((j : ℝ) - q * M) + mu * ((j : ℝ) - q * M) ^ 2 := by
  set a' := a * coefAR M j
  set b' := b * coefBR M j
  set f : ℝ → ℝ := fun y => Wf M j y * Pf a' b' y + (c * ((j : ℝ) - y * M) + mu * ((j : ℝ) - y * M) ^ 2)
  set f' : ℝ → ℝ := fun y => k1f M j a' b' y + -((M : ℝ) * (c + 2 * mu * ((j : ℝ) - y * M)))
  set f'' : ℝ → ℝ := fun y => k2f M j a' b' y + 2 * mu * ((M : ℝ) * (M : ℝ))
  have hin : ∀ y ∈ Set.Icc ql qh, 0 < y ∧ y < 1 := fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hf : ∀ y ∈ Set.Icc ql qh, HasDerivAt f (f' y) y := fun y hy =>
    (hasDerivAt_WP hj a' b' (hin y hy).1 (hin y hy).2).add (hasDerivAt_quadPart c mu j M y)
  have hf' : ∀ y ∈ Set.Icc ql qh, HasDerivAt f' (f'' y) y := fun y hy =>
    (hasDerivAt_k1f hj a' b' (hin y hy).1 (hin y hy).2).add (hasDerivAt_quadPart' c mu j M y)
  have hH : ∀ y ∈ Set.Icc ql qh, |f'' y| ≤
      wm * (|2 * (a' + b')| + 2 * la * dp + (la * la + lp) * pa) + 2 * mu * ((M : ℝ) * (M : ℝ)) := by
    intro y hy
    have hk := abs_k2f_le (Wf_pos hj (hin y hy).1 (hin y hy).2).le (hW y hy.1 hy.2) (hP y hy.1 hy.2)
      (hdP y hy.1 hy.2) (hL y hy.1 hy.2) (hLp y hy.1 hy.2)
    have h2 : 0 ≤ 2 * mu * ((M : ℝ) * (M : ℝ)) := by positivity
    calc |f'' y| ≤ |k2f M j a' b' y| + |2 * mu * ((M : ℝ) * (M : ℝ))| := abs_add_le _ _
      _ ≤ _ := by rw [abs_of_nonneg h2]; linarith
  have hT := taylor2_mid hlh hq hq' hf hf' hH
  have hq0 : 0 < (ql + qh) / 2 ∧ (ql + qh) / 2 < 1 := ⟨by linarith, by linarith⟩
  have ef : f q = kernel2 q a b M j + c * ((j : ℝ) - q * M) + mu * ((j : ℝ) - q * M) ^ 2 := by
    simp only [f]; rw [kernel2_eq_WP hj (by linarith) (by linarith)]; ring
  have ef0 : f ((ql + qh) / 2) = kernel2 ((ql + qh) / 2) a b M j +
      (mu * (((j : ℝ) - (ql + qh) / 2 * M) * ((j : ℝ) - (ql + qh) / 2 * M)) +
        c * ((j : ℝ) - (ql + qh) / 2 * M)) := by
    simp only [f]; rw [kernel2_eq_WP hj hq0.1 hq0.2]; ring
  have ef'0 : f' ((ql + qh) / 2) = k1f M j a' b' ((ql + qh) / 2) -
      (M : ℝ) * (c + 2 * mu * ((j : ℝ) - (ql + qh) / 2 * M)) := by all_goals (try simp only [f']); all_goals (try ring)
  rw [← ef, ← ef0, ← ef'0]
  exact hT

/-- **Soul's second-order bound, atom `j = −1`**: `κ₂ = −b(1 − q)^M`. -/
theorem kernel2_neg_one_ge_secondOrder (M : ℕ) {ql qh q c mu a b : ℝ} (h1 : qh < 1) (hlh : ql ≤ qh)
    (hq : ql ≤ q) (hq' : q ≤ qh) (hmu : 0 ≤ mu) (hb : 0 ≤ b) :
    -(b * (1 - (ql + qh) / 2) ^ M) + (mu * ((-1 - (ql + qh) / 2 * M) * (-1 - (ql + qh) / 2 * M)) +
        c * (-1 - (ql + qh) / 2 * M)) -
      (qh - ql) / 2 * |b * ((M : ℝ) * (1 - (ql + qh) / 2) ^ (M - 1)) -
        (M : ℝ) * (c + 2 * mu * (-1 - (ql + qh) / 2 * M))| -
      (qh - ql) / 2 * ((qh - ql) / 2) *
        (b * ((M : ℝ) * ((M : ℝ) - 1) * (1 - ql) ^ (M - 2)) + 2 * mu * ((M : ℝ) * (M : ℝ))) / 2 ≤
      kernel2 q a b M (-1) + c * (((-1 : ℤ) : ℝ) - q * M) + mu * (((-1 : ℤ) : ℝ) - q * M) ^ 2 := by
  have hsub : ∀ y, HasDerivAt (fun y : ℝ => 1 - y) (-1) y := fun y => by
    simpa using (hasDerivAt_id y).const_sub 1
  set f : ℝ → ℝ := fun y => -(b * (1 - y) ^ M) + (c * (-1 - y * M) + mu * (-1 - y * M) ^ 2)
  set f' : ℝ → ℝ := fun y => b * ((M : ℝ) * (1 - y) ^ (M - 1)) +
    -((M : ℝ) * (c + 2 * mu * (-1 - y * M)))
  set f'' : ℝ → ℝ := fun y => -(b * ((M : ℝ) * (((M - 1 : ℕ) : ℝ) * (1 - y) ^ (M - 1 - 1)))) +
    2 * mu * ((M : ℝ) * (M : ℝ))
  have hf : ∀ y ∈ Set.Icc ql qh, HasDerivAt f (f' y) y := by
    intro y _
    have := ((((hsub y).pow M).const_mul b).neg).add (hasDerivAt_quadPart c mu (-1) M y)
    convert this using 1
    all_goals (try simp only [f']); all_goals (try ring)
  have hf' : ∀ y ∈ Set.Icc ql qh, HasDerivAt f' (f'' y) y := by
    intro y _
    have := ((((hsub y).pow (M - 1)).const_mul (M : ℝ)).const_mul b).add
      (hasDerivAt_quadPart' c mu (-1) M y)
    convert this using 1
    all_goals (try simp only [f'']); all_goals (try ring)
  have hH : ∀ y ∈ Set.Icc ql qh, |f'' y| ≤
      b * ((M : ℝ) * ((M : ℝ) - 1) * (1 - ql) ^ (M - 2)) + 2 * mu * ((M : ℝ) * (M : ℝ)) := by
    intro y hy
    have hb' := natCast_pred_pow_le M (x := 1 - ql) (y := 1 - y) (by linarith [hy.2]) (by linarith [hy.1])
    have hbb := mul_le_mul_of_nonneg_left hb' hb
    have h2 : 0 ≤ 2 * mu * ((M : ℝ) * (M : ℝ)) := by positivity
    calc |f'' y| ≤ |-(b * ((M : ℝ) * (((M - 1 : ℕ) : ℝ) * (1 - y) ^ (M - 1 - 1))))| +
          |2 * mu * ((M : ℝ) * (M : ℝ))| := abs_add_le _ _
      _ ≤ _ := by
          rw [abs_neg, abs_of_nonneg h2, abs_mul, abs_of_nonneg hb]
          linarith
  have hT := taylor2_mid hlh hq hq' hf hf' hH
  have ef : f q = kernel2 q a b M (-1) + c * (((-1 : ℤ) : ℝ) - q * M) + mu * (((-1 : ℤ) : ℝ) - q * M) ^ 2 := by
    simp only [f]; rw [kernel2_neg_one (by linarith)]; push_cast; ring
  have ef0 : f ((ql + qh) / 2) = -(b * (1 - (ql + qh) / 2) ^ M) +
      (mu * ((-1 - (ql + qh) / 2 * M) * (-1 - (ql + qh) / 2 * M)) + c * (-1 - (ql + qh) / 2 * M)) := by
    simp only [f]; ring
  have ef'0 : f' ((ql + qh) / 2) = b * ((M : ℝ) * (1 - (ql + qh) / 2) ^ (M - 1)) -
      (M : ℝ) * (c + 2 * mu * (-1 - (ql + qh) / 2 * M)) := by all_goals (try simp only [f']); all_goals (try ring)
  rw [← ef, ← ef0, ← ef'0]
  exact hT

/-- **Soul's second-order bound, atom `j = M + 1`**: `κ₂ = −a q^M`. -/
theorem kernel2_top_ge_secondOrder (M : ℕ) {ql qh q c mu a b : ℝ} (h0 : 0 < ql) (hlh : ql ≤ qh)
    (hq : ql ≤ q) (hq' : q ≤ qh) (hmu : 0 ≤ mu) (ha : 0 ≤ a) :
    -(a * ((ql + qh) / 2) ^ M) +
        (mu * (((M : ℝ) + 1 - (ql + qh) / 2 * M) * ((M : ℝ) + 1 - (ql + qh) / 2 * M)) +
          c * ((M : ℝ) + 1 - (ql + qh) / 2 * M)) -
      (qh - ql) / 2 * |-(a * ((M : ℝ) * ((ql + qh) / 2) ^ (M - 1))) -
        (M : ℝ) * (c + 2 * mu * ((M : ℝ) + 1 - (ql + qh) / 2 * M))| -
      (qh - ql) / 2 * ((qh - ql) / 2) *
        (a * ((M : ℝ) * ((M : ℝ) - 1) * qh ^ (M - 2)) + 2 * mu * ((M : ℝ) * (M : ℝ))) / 2 ≤
      kernel2 q a b M ((M : ℤ) + 1) + c * ((((M : ℤ) + 1 : ℤ) : ℝ) - q * M) +
        mu * ((((M : ℤ) + 1 : ℤ) : ℝ) - q * M) ^ 2 := by
  set f : ℝ → ℝ := fun y => -(a * y ^ M) + (c * (((M : ℝ) + 1) - y * M) + mu * (((M : ℝ) + 1) - y * M) ^ 2)
  set f' : ℝ → ℝ := fun y => -(a * ((M : ℝ) * y ^ (M - 1))) +
    -((M : ℝ) * (c + 2 * mu * (((M : ℝ) + 1) - y * M)))
  set f'' : ℝ → ℝ := fun y => -(a * ((M : ℝ) * (((M - 1 : ℕ) : ℝ) * y ^ (M - 1 - 1)))) +
    2 * mu * ((M : ℝ) * (M : ℝ))
  have hf : ∀ y ∈ Set.Icc ql qh, HasDerivAt f (f' y) y := by
    intro y _
    have := (((hasDerivAt_pow M y).const_mul a).neg).add (hasDerivAt_quadPart c mu ((M : ℝ) + 1) M y)
    convert this using 1
  have hf' : ∀ y ∈ Set.Icc ql qh, HasDerivAt f' (f'' y) y := by
    intro y _
    have := ((((hasDerivAt_pow (M - 1) y).const_mul (M : ℝ)).const_mul a).neg).add
      (hasDerivAt_quadPart' c mu ((M : ℝ) + 1) M y)
    convert this using 1
  have hH : ∀ y ∈ Set.Icc ql qh, |f'' y| ≤
      a * ((M : ℝ) * ((M : ℝ) - 1) * qh ^ (M - 2)) + 2 * mu * ((M : ℝ) * (M : ℝ)) := by
    intro y hy
    have hb' := natCast_pred_pow_le M (x := qh) (y := y) (by linarith [hy.1]) hy.2
    have haa := mul_le_mul_of_nonneg_left hb' ha
    have h2 : 0 ≤ 2 * mu * ((M : ℝ) * (M : ℝ)) := by positivity
    calc |f'' y| ≤ |-(a * ((M : ℝ) * (((M - 1 : ℕ) : ℝ) * y ^ (M - 1 - 1))))| +
          |2 * mu * ((M : ℝ) * (M : ℝ))| := abs_add_le _ _
      _ ≤ _ := by
          rw [abs_neg, abs_of_nonneg h2, abs_mul, abs_of_nonneg ha]
          linarith
  have hT := taylor2_mid hlh hq hq' hf hf' hH
  have ef : f q = kernel2 q a b M ((M : ℤ) + 1) + c * ((((M : ℤ) + 1 : ℤ) : ℝ) - q * M) +
      mu * ((((M : ℤ) + 1 : ℤ) : ℝ) - q * M) ^ 2 := by
    simp only [f]; rw [kernel2_top (by linarith)]; push_cast; ring
  have ef0 : f ((ql + qh) / 2) = -(a * ((ql + qh) / 2) ^ M) +
      (mu * (((M : ℝ) + 1 - (ql + qh) / 2 * M) * ((M : ℝ) + 1 - (ql + qh) / 2 * M)) +
        c * ((M : ℝ) + 1 - (ql + qh) / 2 * M)) := by
    simp only [f]; ring
  have ef'0 : f' ((ql + qh) / 2) = -(a * ((M : ℝ) * ((ql + qh) / 2) ^ (M - 1))) -
      (M : ℝ) * (c + 2 * mu * ((M : ℝ) + 1 - (ql + qh) / 2 * M)) := by all_goals (try simp only [f']); all_goals (try ring)
  rw [← ef, ← ef0, ← ef'0]
  exact hT

/-! ## Casts of the checker's quantities -/

theorem MBox.q0_cast (b : MBox) : ((b.q0 : ℚ) : ℝ) = ((b.ql : ℝ) + b.qh) / 2 := by
  unfold MBox.q0; push_cast; ring

theorem MBox.rad_cast (b : MBox) : ((b.rad : ℚ) : ℝ) = ((b.qh : ℝ) - b.ql) / 2 := by
  unfold MBox.rad; push_cast; ring

theorem MBox.piQ_cast (b : MBox) (M : ℕ) :
    ((b.piQ M : ℚ) : ℝ) = (b.alpha : ℝ) + (b.beta : ℝ) * ((M : ℝ) - (b.m0 : ℝ)) -
      (b.gamma : ℝ) * ((M : ℝ) - (b.m0 : ℝ)) ^ 2 := by
  unfold MBox.piQ; push_cast; ring

theorem MBox.vtx_cast (b : MBox) : ((b.vtx : ℚ) : ℝ) = -(b.c : ℝ) / (2 * (b.nu : ℝ)) := by
  unfold MBox.vtx; push_cast; ring

/-- The checker's two-sided kernel from a binomial row is `κ₂` at `q`. -/
theorem kapRow2_cast {q : ℚ} {M j : ℕ} {f : ℕ → ℚ} (hf : BinomFn q M f) (hq0 : (0 : ℝ) < q)
    (hq1 : (q : ℝ) < 1) (a bb : ℚ) :
    ((kapRow2 q j f a bb : ℚ) : ℝ) = kernel2 (q : ℝ) (a : ℝ) (bb : ℝ) M (j : ℤ) := by
  have h0 : (q : ℝ) ≠ 0 := hq0.ne'
  have h1 : (1 : ℝ) - q ≠ 0 := by linarith
  unfold kapRow2 kernel2 fL fR
  push_cast
  rw [hf j, hf (j + 1)]
  have ep : (((j + 1 : ℕ) : ℤ)) = (j : ℤ) + 1 := by push_cast; ring
  rw [ep]
  split_ifs with hj
  · subst hj
    rw [binom_of_neg (by norm_num : ((0 : ℕ) : ℤ) - 1 < 0)]
    field_simp
    try ring
  · rw [hf (j - 1), show (((j - 1 : ℕ) : ℤ)) = (j : ℤ) - 1 by omega]
    field_simp
    try ring

theorem joint_cast (b : MBox) (M : ℕ) (j : ℤ) (kap k1 k2 : ℚ) :
    ((MGF.joint b M j kap k1 k2 : ℚ) : ℝ) =
      (kap : ℝ) + ((b.nu : ℝ) * (((j : ℝ) - ((b.ql : ℝ) + b.qh) / 2 * M) *
          ((j : ℝ) - ((b.ql : ℝ) + b.qh) / 2 * M)) + (b.c : ℝ) * ((j : ℝ) - ((b.ql : ℝ) + b.qh) / 2 * M)) -
        ((b.qh : ℝ) - b.ql) / 2 * |(k1 : ℝ) - (M : ℝ) * ((b.c : ℝ) + 2 * (b.nu : ℝ) *
          ((j : ℝ) - ((b.ql : ℝ) + b.qh) / 2 * M))| -
        ((b.qh : ℝ) - b.ql) / 2 * (((b.qh : ℝ) - b.ql) / 2) *
          ((k2 : ℝ) + 2 * (b.nu : ℝ) * ((M : ℝ) * (M : ℝ))) / 2 := by
  unfold MGF.joint
  simp only [Rat.cast_sub, Rat.cast_add, Rat.cast_mul, Rat.cast_div, qabs_cast, Rat.cast_intCast,
    Rat.cast_natCast, Rat.cast_ofNat, MBox.q0_cast, MBox.rad_cast]

/-- The checker's priced sum is `pricedTail` of the cast lists (for `p_k = s_k^M`, exponent `1`). -/
theorem pricedQ_cast (z p : List ℚ) :
    ((pricedQ z p : ℚ) : ℝ) =
      pricedTail (z.map (Rat.cast : ℚ → ℝ)) (p.map fun s : ℚ => ((s : ℝ), (0 : ℝ))) 1 := by
  induction z generalizing p with
  | nil => cases p <;> simp [pricedQ]
  | cons x xs ih =>
    cases p with
    | nil => simp [pricedQ]
    | cons s ps =>
      simp only [pricedQ, List.map_cons, pricedTail_cons_cons, pow_one]
      push_cast
      rw [ih]

/-! ## The skip test -/

/-- **The skip bound**: `κ₂ ≥ −B` and `ν(δ − vtx)² ≥ rhs + B + c²/(4ν)` give the atom. -/
theorem skip_sound {b : MBox} (hnu : 0 < b.nu) {M : ℕ} {q : ℝ} {j : ℤ} {rhs B : ℚ}
    (hκ : -((B : ℚ) : ℝ) ≤ kernel2 q b.a b.b M j)
    (hlev : ((rhs + B + b.c * b.c / (4 * b.nu) : ℚ) : ℝ) ≤
      (b.nu : ℝ) * (((j : ℝ) - q * M - ((b.vtx : ℚ) : ℝ)) * ((j : ℝ) - q * M - ((b.vtx : ℚ) : ℝ)))) :
    (rhs : ℝ) ≤ kernel2 q b.a b.b M j + (b.c : ℝ) * ((j : ℝ) - q * M) + (b.nu : ℝ) * ((j : ℝ) - q * M) ^ 2 := by
  have hnuR : (0 : ℝ) < b.nu := by exact_mod_cast hnu
  rw [MBox.vtx_cast] at hlev
  push_cast at hlev
  have e : (b.nu : ℝ) * (((j : ℝ) - q * M - -(b.c : ℝ) / (2 * (b.nu : ℝ))) *
      ((j : ℝ) - q * M - -(b.c : ℝ) / (2 * (b.nu : ℝ)))) =
      (b.c : ℝ) * ((j : ℝ) - q * M) + (b.nu : ℝ) * ((j : ℝ) - q * M) ^ 2 +
        (b.c : ℝ) * (b.c : ℝ) / (4 * (b.nu : ℝ)) := by
    field_simp; try ring
  rw [e] at hlev
  linarith

/-- The distance to an interval is at most the distance to any of its points. -/
theorem distMin_le {lo hi v : ℚ} {x : ℝ} (hx : (lo : ℝ) ≤ x) (hx' : x ≤ hi) :
    ((distMin lo hi v : ℚ) : ℝ) * ((distMin lo hi v : ℚ) : ℝ) ≤ (x - (v : ℝ)) * (x - (v : ℝ)) := by
  unfold distMin
  split_ifs with h1 h2
  · have h1' : (v : ℝ) < lo := by exact_mod_cast h1
    push_cast
    nlinarith
  · have h2' : (hi : ℝ) < v := by exact_mod_cast h2
    push_cast
    nlinarith
  · push_cast
    nlinarith [mul_self_nonneg (x - (v : ℝ))]

/-- **A passing exact skip test gives the atom** for every `q` of the box. -/
theorem atomSkip_sound {b : MBox} (h0 : (0 : ℝ) < b.ql) (h1 : (b.qh : ℝ) < 1) (hnu : 0 < b.nu) (ha : 0 ≤ b.a)
    (hb : 0 ≤ b.b) {M : ℕ} {rhs : ℚ} {j : ℤ} (hok : atomSkip b M rhs j = true) {q : ℝ} (hq : (b.ql : ℝ) ≤ q)
    (hq' : q ≤ b.qh) :
    (rhs : ℝ) ≤ kernel2 q b.a b.b M j + (b.c : ℝ) * ((j : ℝ) - q * M) + (b.nu : ℝ) * ((j : ℝ) - q * M) ^ 2 := by
  unfold atomSkip at hok
  simp only [decide_eq_true_eq] at hok
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hκ := kernel2_ge_kapB h0 h1 ha hb M hq hq' j
  refine skip_sound hnu hκ ?_
  have hd := distMin_le (lo := (j : ℚ) - b.qh * (M : ℚ)) (hi := (j : ℚ) - b.ql * (M : ℚ)) (v := b.vtx)
    (x := (j : ℝ) - q * M) (by push_cast; nlinarith) (by push_cast; nlinarith)
  have hl := (Rat.cast_le (K := ℝ)).mpr hok
  unfold skipLev at hl
  have hnuR : (0 : ℝ) ≤ b.nu := by exact_mod_cast hnu.le
  push_cast at hl ⊢
  nlinarith [mul_le_mul_of_nonneg_left hd hnuR]

/-! ## The atoms -/

/-- **The atom `(M, j)`, `0 ≤ j ≤ M`, of a passing fibre** (first- or second-order bound with the two-sided
coefficients). -/
theorem atomMid2_sound {b : MBox} {M j : ℕ} (hj : j ≤ M) {fl f0 fh : ℕ → ℚ} {pas : Array ℕ}
    (hfl : BinomFn b.ql M fl) (hf0 : BinomFn b.q0 M f0) (hfh : BinomFn b.qh M fh) (hpas : PasInv M pas)
    (h0 : (0 : ℝ) < b.ql) (hlh : (b.ql : ℝ) ≤ b.qh) (h1 : (b.qh : ℝ) < 1) (hnu : 0 < b.nu)
    {rhs : ℚ} (hok : MGF.atomMid b M j fl f0 fh pas rhs = true) {q : ℝ} (hq : (b.ql : ℝ) ≤ q)
    (hq' : q ≤ b.qh) :
    (rhs : ℝ) ≤ kernel2 q b.a b.b M (j : ℤ) + (b.c : ℝ) * (((j : ℤ) : ℝ) - q * M) +
      (b.nu : ℝ) * (((j : ℤ) : ℝ) - q * M) ^ 2 := by
  have hq0R : ((b.q0 : ℚ) : ℝ) = ((b.ql : ℝ) + b.qh) / 2 := MBox.q0_cast b
  have hkap : ((kapRow2 b.q0 j f0 b.a b.b : ℚ) : ℝ) = kernel2 (((b.ql : ℝ) + b.qh) / 2) b.a b.b M (j : ℤ) := by
    rw [kapRow2_cast hf0 (by rw [hq0R]; linarith) (by rw [hq0R]; linarith), hq0R]
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hW := fun x (hx : (b.ql : ℝ) ≤ x) (hx' : x ≤ b.qh) => wmax_bound hj hfl hfh hpas h0 h1 hx hx'
  have hP := fun x (hx : (b.ql : ℝ) ≤ x) (hx' : x ≤ b.qh) => by
    have := pabs_bound (a := b.a * coefA M j) (bb := b.b * coefB M j) hx hx'
    rwa [Rat.cast_mul, Rat.cast_mul, coefA_cast, coefB_cast] at this
  have hdP := fun x (hx : (b.ql : ℝ) ≤ x) (hx' : x ≤ b.qh) => by
    have := dpabs_bound (a := b.a * coefA M j) (bb := b.b * coefB M j) hx hx'
    rwa [Rat.cast_mul, Rat.cast_mul, coefA_cast, coefB_cast] at this
  have hL := fun x (hx : (b.ql : ℝ) ≤ x) (hx' : x ≤ b.qh) => labs_bound (M := M) (j := j) h0 h1 hx hx'
  unfold MGF.atomMid at hok
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hok
  rcases hok with hok | hok
  · have hR : (rhs : ℝ) ≤ ((kapRow2 b.q0 j f0 b.a b.b - b.rad * (wmax M j b.ql b.qh fl fh pas *
        (dpabs (b.a * coefA M j) (b.b * coefB M j) b.ql b.qh +
          labs M j b.ql b.qh * pabs (b.a * coefA M j) (b.b * coefB M j) b.ql b.qh)) +
        quadMinI b.nu b.c ((j : ℚ) - b.qh * (M : ℚ)) ((j : ℚ) - b.ql * (M : ℚ)) : ℚ) : ℝ) := by
      exact_mod_cast hok
    push_cast at hR
    have hFO := kernel2_ge_firstOrder hj h0 hlh h1 hq hq' (b.a : ℝ) (b.b : ℝ) hW hP hdP hL
    have hQ := quadMinI_le (mu := b.nu) (c := b.c) (lo := (j : ℚ) - b.qh * (M : ℚ))
      (hi := (j : ℚ) - b.ql * (M : ℚ)) hnu (x := ((j : ℤ) : ℝ) - q * M)
      (by push_cast; nlinarith) (by push_cast; nlinarith)
    rw [MBox.rad_cast, hkap] at hR
    push_cast at hQ ⊢
    nlinarith [hFO, hQ, hR]
  · have hR : (rhs : ℝ) ≤ ((MGF.joint b M (j : ℤ) (kapRow2 b.q0 j f0 b.a b.b)
        (f0 j / (b.q0 * (1 - b.q0)) * (dpval (b.a * coefA M j) (b.b * coefB M j) b.q0 +
          lcomb M j b.q0 b.q0 * pval (b.a * coefA M j) (b.b * coefB M j) b.q0))
        (wmax M j b.ql b.qh fl fh pas * (qabs (2 * (b.a * coefA M j + b.b * coefB M j)) +
          2 * labs M j b.ql b.qh * dpabs (b.a * coefA M j) (b.b * coefB M j) b.ql b.qh +
          (labs M j b.ql b.qh * labs M j b.ql b.qh + lpabs M j b.ql b.qh) *
            pabs (b.a * coefA M j) (b.b * coefB M j) b.ql b.qh)) : ℚ) : ℝ) := by
      exact_mod_cast hok
    rw [joint_cast, hkap] at hR
    have hk1 : ((f0 j / (b.q0 * (1 - b.q0)) * (dpval (b.a * coefA M j) (b.b * coefB M j) b.q0 +
          lcomb M j b.q0 b.q0 * pval (b.a * coefA M j) (b.b * coefB M j) b.q0) : ℚ) : ℝ) =
        k1f M j ((b.a : ℝ) * coefAR M j) ((b.b : ℝ) * coefBR M j) (((b.ql : ℝ) + b.qh) / 2) := by
      push_cast
      rw [hf0 j, dpval_cast, pval_cast, lcomb_cast, hq0R]
      push_cast
      rw [coefA_cast, coefB_cast]
      unfold k1f Wf lcombR Lf
      ring
    have hk2 : ((wmax M j b.ql b.qh fl fh pas * (qabs (2 * (b.a * coefA M j + b.b * coefB M j)) +
          2 * labs M j b.ql b.qh * dpabs (b.a * coefA M j) (b.b * coefB M j) b.ql b.qh +
          (labs M j b.ql b.qh * labs M j b.ql b.qh + lpabs M j b.ql b.qh) *
            pabs (b.a * coefA M j) (b.b * coefB M j) b.ql b.qh) : ℚ) : ℝ) =
        ((wmax M j b.ql b.qh fl fh pas : ℚ) : ℝ) * (|2 * ((b.a : ℝ) * coefAR M j + (b.b : ℝ) * coefBR M j)| +
          2 * ((labs M j b.ql b.qh : ℚ) : ℝ) *
            ((dpabs (b.a * coefA M j) (b.b * coefB M j) b.ql b.qh : ℚ) : ℝ) +
          (((labs M j b.ql b.qh : ℚ) : ℝ) * ((labs M j b.ql b.qh : ℚ) : ℝ) +
            ((lpabs M j b.ql b.qh : ℚ) : ℝ)) * ((pabs (b.a * coefA M j) (b.b * coefB M j) b.ql b.qh : ℚ) : ℝ)) := by
      push_cast
      rw [qabs_cast]
      push_cast
      rw [coefA_cast, coefB_cast]
    rw [hk1, hk2] at hR
    have hLp : ∀ x, (b.ql : ℝ) ≤ x → x ≤ b.qh → |Lpf M j x| ≤ ((lpabs M j b.ql b.qh : ℚ) : ℝ) :=
      fun x hx hx' => by rw [lpabs_cast]; exact abs_Lpf_le h0 h1 hx hx'
    have hSO := kernel2_ge_secondOrder hj h0 hlh h1 hq hq' (c := (b.c : ℝ)) (mu := (b.nu : ℝ))
      (by exact_mod_cast hnu.le) (b.a : ℝ) (b.b : ℝ) hW hP hdP hL hLp
    push_cast at hR ⊢
    linarith [hSO, hR]

/-- **The atom `(M, −1)` of a passing fibre.** -/
theorem atomNeg2_sound {b : MBox} {M : ℕ} (h1 : (b.qh : ℝ) < 1) (hlh : (b.ql : ℝ) ≤ b.qh) (hnu : 0 < b.nu)
    (hb : 0 ≤ b.b) {rhs : ℚ} (hok : MGF.atomNeg b M rhs = true) {q : ℝ} (hq : (b.ql : ℝ) ≤ q)
    (hq' : q ≤ b.qh) :
    (rhs : ℝ) ≤ kernel2 q b.a b.b M (-1) + (b.c : ℝ) * (((-1 : ℤ) : ℝ) - q * M) +
      (b.nu : ℝ) * (((-1 : ℤ) : ℝ) - q * M) ^ 2 := by
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hbR : (0 : ℝ) ≤ b.b := by exact_mod_cast hb
  unfold MGF.atomNeg at hok
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hok
  rcases hok with hok | hok
  · have hR : (rhs : ℝ) ≤ ((-(b.b * (1 - b.q0) ^ M) - b.rad * (b.b * ((M : ℚ) * (1 - b.ql) ^ (M - 1))) +
        quadMinI b.nu b.c (-1 - b.qh * (M : ℚ)) (-1 - b.ql * (M : ℚ)) : ℚ) : ℝ) := by
      exact_mod_cast hok
    push_cast at hR
    rw [MBox.q0_cast, MBox.rad_cast] at hR
    have hN := kappa_neg_one_ge M h1 hq hq'
    rw [kappa_neg_one (by linarith : ((b.ql : ℝ) + b.qh) / 2 < 1), kappa_neg_one (by linarith : q < 1)] at hN
    have hN' := mul_le_mul_of_nonneg_left hN hbR
    rw [kernel2_neg_one (by linarith : q < 1)]
    have hQ := quadMinI_le (mu := b.nu) (c := b.c) (lo := -1 - b.qh * (M : ℚ))
      (hi := -1 - b.ql * (M : ℚ)) hnu (x := ((-1 : ℤ) : ℝ) - q * M)
      (by push_cast; nlinarith) (by push_cast; nlinarith)
    push_cast at hQ ⊢
    nlinarith [hN', hQ, hR]
  · have hR : (rhs : ℝ) ≤ ((MGF.joint b M (-1) (-(b.b * (1 - b.q0) ^ M))
        (b.b * ((M : ℚ) * (1 - b.q0) ^ (M - 1)))
        (b.b * ((M : ℚ) * ((M : ℚ) - 1) * (1 - b.ql) ^ (M - 2))) : ℚ) : ℝ) := by
      exact_mod_cast hok
    rw [joint_cast] at hR
    push_cast at hR
    rw [MBox.q0_cast] at hR
    have hSO := kernel2_neg_one_ge_secondOrder M (c := (b.c : ℝ)) (mu := (b.nu : ℝ)) (a := (b.a : ℝ))
      (b := (b.b : ℝ)) h1 hlh hq hq' (by exact_mod_cast hnu.le) hbR
    push_cast at hSO ⊢
    linarith [hSO, hR]

/-- **The atom `(M, M + 1)` of a passing fibre.** -/
theorem atomTop2_sound {b : MBox} {M : ℕ} (h0 : (0 : ℝ) < b.ql) (hlh : (b.ql : ℝ) ≤ b.qh) (hnu : 0 < b.nu)
    (ha : 0 ≤ b.a) {rhs : ℚ} (hok : MGF.atomTop b M rhs = true) {q : ℝ} (hq : (b.ql : ℝ) ≤ q)
    (hq' : q ≤ b.qh) :
    (rhs : ℝ) ≤ kernel2 q b.a b.b M ((M : ℤ) + 1) + (b.c : ℝ) * ((((M : ℤ) + 1 : ℤ) : ℝ) - q * M) +
      (b.nu : ℝ) * ((((M : ℤ) + 1 : ℤ) : ℝ) - q * M) ^ 2 := by
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have haR : (0 : ℝ) ≤ b.a := by exact_mod_cast ha
  unfold MGF.atomTop at hok
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hok
  rcases hok with hok | hok
  · have hR : (rhs : ℝ) ≤ ((-(b.a * b.q0 ^ M) - b.rad * (b.a * ((M : ℚ) * b.qh ^ (M - 1))) +
        quadMinI b.nu b.c ((M : ℚ) + 1 - b.qh * (M : ℚ)) ((M : ℚ) + 1 - b.ql * (M : ℚ)) : ℚ) : ℝ) := by
      exact_mod_cast hok
    push_cast at hR
    rw [MBox.q0_cast, MBox.rad_cast] at hR
    have hT := kappa_top_ge M h0 hq hq'
    rw [kappa_top (by linarith : (0 : ℝ) < ((b.ql : ℝ) + b.qh) / 2), kappa_top (by linarith : (0 : ℝ) < q)] at hT
    have hT' := mul_le_mul_of_nonneg_left hT haR
    rw [kernel2_top (by linarith : (0 : ℝ) < q)]
    have hQ := quadMinI_le (mu := b.nu) (c := b.c) (lo := (M : ℚ) + 1 - b.qh * (M : ℚ))
      (hi := (M : ℚ) + 1 - b.ql * (M : ℚ)) hnu (x := (((M : ℤ) + 1 : ℤ) : ℝ) - q * M)
      (by push_cast; nlinarith) (by push_cast; nlinarith)
    push_cast at hQ ⊢
    nlinarith [hT', hQ, hR]
  · have hR : (rhs : ℝ) ≤ ((MGF.joint b M ((M : ℤ) + 1) (-(b.a * b.q0 ^ M))
        (-(b.a * ((M : ℚ) * b.q0 ^ (M - 1))))
        (b.a * ((M : ℚ) * ((M : ℚ) - 1) * b.qh ^ (M - 2))) : ℚ) : ℝ) := by
      exact_mod_cast hok
    rw [joint_cast] at hR
    push_cast at hR
    rw [MBox.q0_cast] at hR
    have hSO := kernel2_top_ge_secondOrder M (c := (b.c : ℝ)) (mu := (b.nu : ℝ)) (a := (b.a : ℝ))
      (b := (b.b : ℝ)) h0 hlh hq hq' (by exact_mod_cast hnu.le) haR
    push_cast at hSO ⊢
    linarith [hSO, hR]

/-- The atom at any integer `j ∈ [−1, M + 1]` of a passing fibre (the exact skip test or the bound of its kind). -/
theorem atomAt2_sound {b : MBox} {M : ℕ} {fl f0 fh : ℕ → ℚ} {pas : Array ℕ}
    (hfl : BinomFn b.ql M fl) (hf0 : BinomFn b.q0 M f0) (hfh : BinomFn b.qh M fh) (hpas : PasInv M pas)
    (h0 : (0 : ℝ) < b.ql) (hlh : (b.ql : ℝ) ≤ b.qh) (h1 : (b.qh : ℝ) < 1) (hnu : 0 < b.nu) (ha : 0 ≤ b.a)
    (hb : 0 ≤ b.b) {rhs : ℚ} {j : ℤ} (hj : -1 ≤ j) (hj' : j ≤ (M : ℤ) + 1)
    (hok : MGF.atomAt b M fl f0 fh pas rhs j = true) {q : ℝ} (hq : (b.ql : ℝ) ≤ q) (hq' : q ≤ b.qh) :
    (rhs : ℝ) ≤ kernel2 q b.a b.b M j + (b.c : ℝ) * ((j : ℝ) - q * M) + (b.nu : ℝ) * ((j : ℝ) - q * M) ^ 2 := by
  unfold MGF.atomAt at hok
  simp only [Bool.or_eq_true] at hok
  rcases hok with hsk | hok
  · exact atomSkip_sound h0 h1 hnu ha hb hsk hq hq'
  split_ifs at hok with hA hB
  · subst hA
    exact atomNeg2_sound h1 hlh hnu hb hok hq hq'
  · rw [hB]
    exact atomTop2_sound h0 hlh hnu ha hok hq hq'
  · have hj0 : 0 ≤ j := by omega
    have hjM : j.toNat ≤ M := by omega
    have e : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg hj0
    have := atomMid2_sound hjM hfl hf0 hfh hpas h0 hlh h1 hnu hok hq hq'
    rwa [e] at this

theorem atomsFrom2_sound {b : MBox} {M : ℕ} {fl f0 fh : ℕ → ℚ} {pas : Array ℕ} {rhs : ℚ} :
    ∀ (k : ℕ) (lo : ℤ), MGF.atomsFrom b M fl f0 fh pas rhs lo k = true →
      ∀ j : ℤ, lo ≤ j → j < lo + k → MGF.atomAt b M fl f0 fh pas rhs j = true := by
  intro k
  induction k with
  | zero => intro lo _ j h1 h2; push_cast at h2; omega
  | succ k ih =>
    intro lo h j h1 h2
    unfold MGF.atomsFrom at h
    simp only [Bool.and_eq_true] at h
    rcases eq_or_lt_of_le h1 with he | hlt
    · rw [← he]; exact h.1
    · exact ih (lo + 1) h.2 j (by omega) (by push_cast at h2 ⊢; omega)

end Erdos993Lean.Analytic.MGF
