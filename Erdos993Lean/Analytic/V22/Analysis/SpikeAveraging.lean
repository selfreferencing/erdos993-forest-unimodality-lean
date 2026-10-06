import Erdos993Lean.Analytic.V22.Analysis.Averaging
import Erdos993Lean.Analytic.V22.Analysis.FiberInfimum
import Erdos993Lean.Analytic.V22.Checks.EarlyStatements
import Erdos993Lean.Analytic.V22.Checks.LateStatements

/-!
# Section 5: finite spike prices and their actual-mixture consumer

Source: frozen `SOURCE_V5_note.tex`, labels `lem:spike`, `lem:KM`, `lem:Zc`.
The price below is the maximum over exactly all natural fibers below the
source cut. The all-integer infimum is attained by `FiberInfimum`; no
attainment premise is introduced. The eight small-fiber constants consume
the explicitly authorized finite statement `Checks.lemma_7_12`.
Root owns compilation; this drafting subagent runs no Lean or lake.
-/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set Finset Erdos993Lean.Analytic.NoValley

noncomputable def spikeAtomPrice (q mu b beta ell : ℝ) (M : ℕ) : ℝ :=
  (1 / (1 - q) ^ M) * Real.exp (-ell * mu) * V22.deficitG q mu b beta M

noncomputable def spikeMaxPrice (q mu b beta ell ts : ℝ) : ℝ :=
  if h : 0 < ts * mu then
    (Finset.range (Nat.ceil (ts * mu))).sup'
      ⟨0, Finset.mem_range.mpr (Nat.ceil_pos.mpr h)⟩ (spikeAtomPrice q mu b beta ell)
  else 0

theorem spikeAtomPrice_nonneg {q : ℝ} (hq : q < 1) (mu b beta ell : ℝ) (M : ℕ) :
    0 ≤ spikeAtomPrice q mu b beta ell M := by
  unfold spikeAtomPrice V22.deficitG V22.positivePart
  exact mul_nonneg (mul_nonneg (div_nonneg (by norm_num) (pow_nonneg (by linarith) _))
    (Real.exp_pos _).le) (le_max_right _ _)

theorem spikeMaxPrice_nonneg {q mu ts : ℝ} (hq : q < 1) (hmu : 0 < mu) (hts : 0 < ts)
    (b beta ell : ℝ) : 0 ≤ spikeMaxPrice q mu b beta ell ts := by
  have hcut := mul_pos hts hmu
  unfold spikeMaxPrice
  rw [dif_pos hcut]
  have hm : 0 ∈ Finset.range (Nat.ceil (ts * mu)) := mem_range.mpr (Nat.ceil_pos.mpr hcut)
  exact (spikeAtomPrice_nonneg hq mu b beta ell 0).trans
    (Finset.le_sup' (spikeAtomPrice q mu b beta ell) hm)

theorem spikeAtomPrice_le_max {q mu ts : ℝ} (hmu : 0 < mu) (hts : 0 < ts)
    (b beta ell : ℝ) {M : ℕ} (hM : (M : ℝ) < ts * mu) :
    spikeAtomPrice q mu b beta ell M ≤ spikeMaxPrice q mu b beta ell ts := by
  have hcut := mul_pos hts hmu
  unfold spikeMaxPrice
  rw [dif_pos hcut]
  exact Finset.le_sup' (spikeAtomPrice q mu b beta ell)
    (Finset.mem_range.mpr (Nat.lt_ceil.mpr hM))

theorem spike_deficit_priced {q mu ts : ℝ} (hq : q < 1) (hmu : 0 < mu) (hts : 0 < ts)
    (b beta ell : ℝ) {M : ℕ} (hM : (M : ℝ) < ts * mu) :
    V22.deficitG q mu b beta M ≤
      spikeMaxPrice q mu b beta ell ts * Real.exp (ell * mu) * (1 - q) ^ M := by
  have hbase : 0 < (1 - q) ^ M := pow_pos (by linarith) _
  have h := mul_le_mul_of_nonneg_right (spikeAtomPrice_le_max (q := q) hmu hts b beta ell hM)
    (mul_pos (Real.exp_pos (ell * mu)) hbase).le
  have heq : spikeAtomPrice q mu b beta ell M * (Real.exp (ell * mu) * (1 - q) ^ M) =
      V22.deficitG q mu b beta M := by
    unfold spikeAtomPrice
    have hexp : Real.exp (-ell * mu) * Real.exp (ell * mu) = 1 := by
      rw [← Real.exp_add, show -ell * mu + ell * mu = 0 by ring, Real.exp_zero]
    calc
      _ = (Real.exp (-ell * mu) * Real.exp (ell * mu)) * V22.deficitG q mu b beta M := by
        field_simp [hbase.ne'] <;> ring
      _ = _ := by rw [hexp, one_mul]
  rw [heq] at h
  simpa only [mul_assoc] using h

theorem spike_fiber_minorant {q mu ts b beta ell : ℝ}
    (hqa : 1 / 4 ≤ q) (hqb : q ≤ 3 / 4) (hmu : 0 < mu) (hts : 0 < ts)
    (hf : ∀ M : ℕ, ts * mu ≤ (M : ℝ) → ∀ j : ℤ,
      V22.psi ((M : ℝ) / mu) + V22.targetLine b beta ((M : ℝ) / mu) ≤ V22.fiberFunction q mu M j) :
    ∀ M : ℕ, ∀ j : ℤ, (1 + b) + (1 + beta) * ((M : ℝ) / mu - 1) -
      (9 / 2 : ℝ) * ((M : ℝ) / mu - 1) ^ 2 -
      (spikeMaxPrice q mu b beta ell ts * Real.exp (ell * mu)) * (1 - q) ^ M ≤ fiber q mu M j := by
  have hq0 : 0 ≤ q := by linarith
  have hq1 : q ≤ 1 := by linarith
  have hq : q < 1 := by linarith
  have hz := spikeMaxPrice_nonneg hq hmu hts b beta ell
  intro M j
  have hid : (1 + b) + (1 + beta) * ((M : ℝ) / mu - 1) -
      (9 / 2 : ℝ) * ((M : ℝ) / mu - 1) ^ 2 =
      V22.psi ((M : ℝ) / mu) + V22.targetLine b beta ((M : ℝ) / mu) := by
    unfold V22.psi V22.targetLine
    ring
  rw [hid, ← shared_fiberFunction_eq]
  by_cases hM : (M : ℝ) < ts * mu
  · have hp := shared_deficitG_pays (mu := mu) (b := b) (beta := beta) hq0 hq1 M j
    have hprice := spike_deficit_priced hq hmu hts b beta ell hM
    linarith
  · have hmain := hf M (le_of_not_gt hM) j
    have htail : 0 ≤ (spikeMaxPrice q mu b beta ell ts * Real.exp (ell * mu)) * (1 - q) ^ M :=
      mul_nonneg (mul_nonneg hz (Real.exp_pos (ell * mu)).le)
        (pow_nonneg (sub_pos.mpr hq).le M)
    linarith

/-- Lemma 5.1's averaging argument, with the inherited activity cap explicit.
`NoValleyAtMGF2` quantifies over actual finite probability mixtures and keeps
their mean, centered rank, variance and native zero-tilt expectation. -/
theorem spike_averaging_noValley_of_cap {q mu ts b beta ell theta D rhi : ℝ}
    (hqa : 1 / 4 ≤ q) (hqb : q ≤ 3 / 4) (hmu : 0 < mu) (hts : 0 < ts) (_hts1 : ts ≤ 1)
    (_hb : 0 ≤ b) (_hbeta : 0 ≤ beta) (hrhi : rhi ^ 2 < 1)
    (hcap : signedR q ^ 2 ≤ rhi ^ 2)
    (hf : ∀ M : ℕ, ts * mu ≤ (M : ℝ) → ∀ j : ℤ,
      V22.psi ((M : ℝ) / mu) + V22.targetLine b beta ((M : ℝ) / mu) ≤ V22.fiberFunction q mu M j)
    (hm : 0 < 1 + b - theta - 9 * D / (2 * mu) -
      rhi ^ 2 / ((1 - rhi ^ 2) * mu) - spikeMaxPrice q mu b beta ell ts) :
    NoValleyAtMGF2 q mu theta D [(1 - q, Real.exp (-ell * mu))] := by
  have hq : q < 1 := by linarith
  have hz := spikeMaxPrice_nonneg hq hmu hts b beta ell
  have hrq : signedR q ^ 2 < 1 := hcap.trans_lt hrhi
  have hdrq : 0 < 1 - signedR q ^ 2 := by linarith
  have hdrhi : 0 < 1 - rhi ^ 2 := by linarith
  have hpenalty : signedR q ^ 2 / ((1 - signedR q ^ 2) * mu) ≤
      rhi ^ 2 / ((1 - rhi ^ 2) * mu) := by
    calc
      _ ≤ rhi ^ 2 / ((1 - signedR q ^ 2) * mu) :=
        div_le_div_of_nonneg_right hcap (mul_pos hdrq hmu).le
      _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg rhi) (mul_pos hdrhi hmu)
        (mul_le_mul_of_nonneg_right (by linarith) hmu.le)
  have hexp : Real.exp (ell * mu) * Real.exp (-ell * mu) = 1 := by
    rw [← Real.exp_add, show ell * mu + -ell * mu = 0 by ring, Real.exp_zero]
  apply averaging_noValley hqa hqb hmu (by norm_num : (0 : ℝ) ≤ 9 / 2)
    (mul_nonneg hz (Real.exp_pos _).le) (spike_fiber_minorant hqa hqb hmu hts hf)
  rw [mul_assoc, hexp, mul_one]
  have heq : (9 / 2 : ℝ) * D / mu = 9 * D / (2 * mu) := by ring
  rw [heq]
  linarith

theorem smallFiberK_nonneg {M : ℕ} (hM : M ≤ 7) : 0 ≤ V22.Checks.smallFiberK M := by
  have hrat : (0 : ℚ) ≤ V22.smallK.getD M 0 := by
    interval_cases M <;> decide
  unfold V22.Checks.smallFiberK
  exact_mod_cast hrat

theorem smallFiberMargin_nonneg {M : ℕ} (hM : M ≤ 7) :
    0 ≤ (V22.smallMargins.getD M 0 : ℝ) := by
  have hrat : (0 : ℚ) ≤ V22.smallMargins.getD M 0 := by
    interval_cases M <;> decide
  exact_mod_cast hrat

/-- The exact eight small-fiber kernel bounds, conditional only on the
named finite B1 certificate authorized in the lane task. -/
theorem small_fiber_kernel_lower (hB1 : V22.Checks.lemma_7_12) {M : ℕ} (hM : M ≤ 7)
    {q : ℝ} (hqa : 1 / 4 ≤ q) (hqb : q ≤ 3 / 4) (j : ℤ) :
    -V22.Checks.smallFiberK M ≤ weightedKernel q M j := by
  have hc : V22.Checks.inCell (1 / 4) (3 / 4) q := ⟨hqa, hqb⟩
  obtain ⟨hint, hout⟩ := hB1 M hM j q hc
  by_cases hji : -1 ≤ j ∧ j ≤ (M : ℤ) + 1
  · have h := hint hji
    have hm := smallFiberMargin_nonneg hM
    simp only [weightedKernel, ← shared_weightL_eq, ← shared_weightR_eq]
    unfold V22.Checks.smallFiberK
    linarith
  · have hjo : j < -1 ∨ (M : ℤ) + 1 < j := by omega
    have h := hout hjo
    simp only [weightedKernel, ← shared_weightL_eq, ← shared_weightR_eq]
    rw [h]
    linarith [smallFiberK_nonneg hM]

/-- Exact kernel-to-fiber normalization, with its nonnegative penalty kept. -/
theorem fiber_kernel_scale {q mu : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hmu : 0 < mu)
    (M : ℕ) (j : ℤ) :
    fiber q mu M j = mu ^ (3 / 2 : ℝ) / (4 * Real.sqrt (variance q) * gaussianA) * weightedKernel q M j +
      offset q M j ^ 2 / sigma q mu ^ 2 := by
  have hv : 0 < variance q := mul_pos hq0 (sub_pos.mpr hq1)
  have hsv : 0 < Real.sqrt (variance q) := Real.sqrt_pos.2 hv
  have hga := gaussianA_pos
  have hpow : mu ^ (3 / 2 : ℝ) = Real.sqrt mu ^ 3 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hmu.le]
    norm_num
  have hs : sigma q mu = Real.sqrt (variance q) * Real.sqrt mu := Real.sqrt_mul hv.le mu
  have hs2 := Real.sq_sqrt hv.le
  have hs4 : Real.sqrt (variance q) ^ 4 = variance q ^ 2 := by
    calc
      Real.sqrt (variance q) ^ 4 = (Real.sqrt (variance q) ^ 2) ^ 2 := by ring
      _ = variance q ^ 2 := by rw [hs2]
  have hcoef : sigma q mu ^ 3 / (4 * variance q ^ 2 * gaussianA) =
      mu ^ (3 / 2 : ℝ) / (4 * Real.sqrt (variance q) * gaussianA) := by
    rw [hpow, hs]
    field_simp [hv.ne', hsv.ne', hga.ne']
    ring_nf
    rw [hs4]
  unfold fiber
  calc
    _ = sigma q mu ^ 3 / (4 * variance q ^ 2 * gaussianA) * weightedKernel q M j +
        offset q M j ^ 2 / sigma q mu ^ 2 := by ring
    _ = _ := by rw [hcoef]

theorem small_fiber_lower (hB1 : V22.Checks.lemma_7_12) {M : ℕ} (hM : M ≤ 7)
    {q mu : ℝ} (hqa : 1 / 4 ≤ q) (hqb : q ≤ 3 / 4) (hmu : 0 < mu) (j : ℤ) :
    -(V22.Checks.smallFiberK M / (4 * gaussianA * Real.sqrt (variance q))) * mu ^ (3 / 2 : ℝ) ≤
      V22.fiberFunction q mu M j := by
  have hq0 : 0 < q := by linarith
  have hq1 : q < 1 := by linarith
  have hv : 0 < variance q := mul_pos hq0 (sub_pos.mpr hq1)
  have hs := Real.sqrt_pos.2 hv
  have hga := gaussianA_pos
  rw [shared_fiberFunction_eq, fiber_kernel_scale hq0 hq1 hmu]
  have h := mul_le_mul_of_nonneg_left (small_fiber_kernel_lower hB1 hM hqa hqb j)
    (by positivity : 0 ≤ mu ^ (3 / 2 : ℝ) / (4 * Real.sqrt (variance q) * gaussianA))
  have hp := div_nonneg (sq_nonneg (offset q M j)) (sq_nonneg (sigma q mu))
  have heq : mu ^ (3 / 2 : ℝ) / (4 * Real.sqrt (variance q) * gaussianA) * (-V22.Checks.smallFiberK M) =
      -(V22.Checks.smallFiberK M / (4 * gaussianA * Real.sqrt (variance q))) * mu ^ (3 / 2 : ℝ) := by
    field_simp [hs.ne', hga.ne'] <;> ring
  rw [heq] at h
  linarith

theorem binomial_distinct_pair_le_one {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (M : ℕ) (j k : ℤ) (hjk : j ≠ k) : binom M q j + binom M q k ≤ 1 := by
  by_cases hj0 : j < 0
  · rw [binom_of_neg hj0, zero_add]
    exact binom_le_one hq0 hq1 k
  by_cases hjM : (M : ℤ) < j
  · rw [binom_of_gt hjM, zero_add]
    exact binom_le_one hq0 hq1 k
  by_cases hk0 : k < 0
  · rw [binom_of_neg hk0, add_zero]
    exact binom_le_one hq0 hq1 j
  by_cases hkM : (M : ℤ) < k
  · rw [binom_of_gt hkM, add_zero]
    exact binom_le_one hq0 hq1 j
  lift j to ℕ using (by omega : 0 ≤ j)
  lift k to ℕ using (by omega : 0 ≤ k)
  have hjn : j ≤ M := by omega
  have hkn : k ≤ M := by omega
  have hn : j ≠ k := by exact_mod_cast hjk
  have hsub : ({j, k} : Finset ℕ) ⊆ Finset.range (M + 1) := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun n : ℕ => binom M q (n : ℤ)) hsub
    (fun n _ _ => binom_nonneg (M := M) hq0 hq1 (n : ℤ))
  rw [Finset.sum_pair hn, sum_binom M q] at h
  exact h

/-- The native all-integer kernel floor used by note Lemma `lem:Zc`. -/
theorem weightedKernel_lower_quarter {q : ℝ} (hqa : 1 / 4 ≤ q) (hqb : q ≤ 3 / 4)
    (M : ℕ) (j : ℤ) : -(1 / 4 : ℝ) ≤ weightedKernel q M j := by
  have hq0 : 0 < q := by linarith
  have hq1 : q < 1 := by linarith
  have hl : weightL q ≤ (1 / 4 : ℝ) := by
    have heq : 1 / 4 - weightL q = (q - 1 / 2) ^ 2 * (4 * q + 1) := by unfold weightL; ring
    have h := mul_nonneg (sq_nonneg (q - 1 / 2)) (by linarith : 0 ≤ 4 * q + 1)
    linarith
  have hr : weightR q ≤ (1 / 4 : ℝ) := by
    have heq : 1 / 4 - weightR q = (1 - q - 1 / 2) ^ 2 * (4 * (1 - q) + 1) := by unfold weightR; ring
    have h := mul_nonneg (sq_nonneg (1 - q - 1 / 2)) (by linarith : 0 ≤ 4 * (1 - q) + 1)
    linarith
  have hbL := binom_nonneg hq0.le hq1.le (M := M) (j - 1)
  have hbR := binom_nonneg hq0.le hq1.le (M := M) (j + 1)
  have hsum := binomial_distinct_pair_le_one hq0.le hq1.le M (j - 1) (j + 1) (by omega)
  have hL := mul_le_mul_of_nonneg_right hl hbL
  have hR := mul_le_mul_of_nonneg_right hr hbR
  have hmid : 0 ≤ 2 * variance q * binom M q j := by
    have hv : 0 ≤ (2 : ℝ) * q * (1 - q) :=
      mul_nonneg (mul_nonneg (by norm_num) hq0.le) (sub_pos.mpr hq1).le
    have hb : 0 ≤ binom M q j := binom_nonneg (M := M) hq0.le hq1.le j
    simpa only [variance, mul_assoc] using mul_nonneg hv hb
  have hid : weightedKernel q M j = 2 * variance q * binom M q j -
      weightL q * binom M q (j - 1) - weightR q * binom M q (j + 1) := by
    unfold weightedKernel kernel2 fL fR weightL weightR variance
    field_simp [hq0.ne', (sub_pos.mpr hq1).ne'] <;> ring
  rw [hid]
  nlinarith

theorem very_small_fiber_lower {q mu : ℝ}
    (hqa : 1 / 4 ≤ q) (hqb : q ≤ 3 / 4) (hmu : 0 < mu) (M : ℕ) (j : ℤ) :
    -(mu ^ (3 / 2 : ℝ) / (16 * Real.sqrt (variance q) * gaussianA)) ≤ V22.fiberFunction q mu M j := by
  have hq0 : 0 < q := by linarith
  have hq1 : q < 1 := by linarith
  have hv : 0 < variance q := mul_pos hq0 (sub_pos.mpr hq1)
  have hs := Real.sqrt_pos.2 hv
  have hg := gaussianA_pos
  rw [shared_fiberFunction_eq, fiber_kernel_scale hq0 hq1 hmu]
  have h := mul_le_mul_of_nonneg_left (weightedKernel_lower_quarter hqa hqb M j)
    (by positivity : 0 ≤ mu ^ (3 / 2 : ℝ) / (4 * Real.sqrt (variance q) * gaussianA))
  have hp := div_nonneg (sq_nonneg (offset q M j)) (sq_nonneg (sigma q mu))
  have heq : mu ^ (3 / 2 : ℝ) / (4 * Real.sqrt (variance q) * gaussianA) * (-(1 / 4 : ℝ)) =
      -(mu ^ (3 / 2 : ℝ) / (16 * Real.sqrt (variance q) * gaussianA)) := by
    field_simp [hs.ne', hg.ne'] <;> ring
  rw [heq] at h
  linarith

/-- The exact decay test in `lem:Zc`, for its nonnegative additive excess. -/
theorem rpow_exp_price_antitone {A b c m : ℝ} (hA : 0 ≤ A) (hb : 0 ≤ b)
    (hm : 0 < m) (hcm : (3 / 2 : ℝ) ≤ c * m) :
    AntitoneOn (fun x : ℝ => (A * x ^ (3 / 2 : ℝ) + b) * Real.exp (-c * x)) (Ici m) := by
  have hc : 0 < c := by nlinarith
  let f : ℝ → ℝ := fun x => (A * x ^ (3 / 2 : ℝ) + b) * Real.exp (-c * x)
  have hd : ∀ x ∈ Ici m, HasDerivAt f
      (Real.exp (-c * x) * ((3 / 2 : ℝ) * A * x ^ (1 / 2 : ℝ) - c * (A * x ^ (3 / 2 : ℝ) + b))) x := by
    intro x hx
    have hx0 : 0 < x := hm.trans_le hx
    convert ((((Real.hasDerivAt_rpow_const (p := (3 / 2 : ℝ)) (Or.inl hx0.ne')).const_mul A).add_const b).mul
      (((hasDerivAt_id x).const_mul (-c)).exp)) using 1 <;>
      dsimp [f] <;> norm_num <;> ring
  have hf : ContinuousOn f (Ici m) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici m) hf
    (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
  intro x hx
  have hxm : m ≤ x := interior_subset hx
  have hx0 : 0 < x := hm.trans_le hxm
  have hcx : (3 / 2 : ℝ) ≤ c * x := hcm.trans (mul_le_mul_of_nonneg_left hxm hc.le)
  have hpow : x ^ (3 / 2 : ℝ) = x * x ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx0, Real.rpow_one]
  rw [hpow]
  apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
  have hprod : 0 ≤ (A * x ^ (1 / 2 : ℝ)) * (c * x - 3 / 2) :=
    mul_nonneg (mul_nonneg hA (Real.rpow_nonneg hx0.le (1 / 2 : ℝ)))
      (sub_nonneg.mpr hcx)
  have hcb := mul_nonneg hc.le hb
  nlinarith

theorem very_small_parabola_nonpos {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 11 / 50) : V22.psi t ≤ 0 := by
  unfold V22.psi
  nlinarith

theorem very_small_mean_lower {mu mu0 : ℝ} (hmu0 : mu0 ≤ mu) {M : ℕ}
    (hM : 8 ≤ M) (hcut : (M : ℝ) < (11 / 50 : ℝ) * mu) :
    max mu0 (400 / 11 : ℝ) ≤ mu := by
  have hMr : (8 : ℝ) ≤ M := by exact_mod_cast hM
  apply max_le hmu0
  linarith

/-- Lemma `lem:Zc`, with exactly the source profile data (`q_b`, `v_min`,
`ell_0`) exposed rather than replacing them by a new analytic assumption. -/
theorem very_small_spike_price {q qb vmin mu mu0 ell b : ℝ} {M : ℕ}
    (hqa : 1 / 4 ≤ q) (hqb : q ≤ 3 / 4) (hqqb : q ≤ qb) (hqb1 : qb < 1)
    (hvmin : 0 < vmin) (hvminq : vmin ≤ variance q) (hb : 0 ≤ b)
    (hmu0 : mu0 ≤ mu) (hM : 8 ≤ M) (hcut : (M : ℝ) < (11 / 50 : ℝ) * mu)
    (hdecay : (3 / 2 : ℝ) ≤ (ell - (11 / 50) * (-Real.log (1 - qb))) * max mu0 (400 / 11)) :
    spikeAtomPrice q mu b 0 ell M ≤
      ((max mu0 (400 / 11)) ^ (3 / 2 : ℝ) / (16 * Real.sqrt vmin * gaussianA) + b) *
        Real.exp (-(ell - (11 / 50) * (-Real.log (1 - qb))) * max mu0 (400 / 11)) := by
  let mc : ℝ := max mu0 (400 / 11)
  let c : ℝ := ell - (11 / 50) * (-Real.log (1 - qb))
  let A : ℝ := 1 / (16 * Real.sqrt vmin * gaussianA)
  have hmc : 0 < mc := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 400 / 11) (le_max_right _ _)
  have hmcmu : mc ≤ mu := very_small_mean_lower hmu0 hM hcut
  have hmu : 0 < mu := hmc.trans_le hmcmu
  have hq0 : 0 < q := by linarith
  have hq1 : q < 1 := by linarith
  have hbase : 0 < (1 - q) ^ M := pow_pos (by linarith) _
  have hsqvmin : 0 < Real.sqrt vmin := Real.sqrt_pos.2 hvmin
  have hga := gaussianA_pos
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hAM : 0 ≤ A * mu ^ (3 / 2 : ℝ) + b := by positivity
  have ht0 : 0 ≤ (M : ℝ) / mu := div_nonneg (Nat.cast_nonneg _) hmu.le
  have ht : (M : ℝ) / mu < (11 / 50 : ℝ) := (div_lt_iff₀ hmu).2 hcut
  have hpsi := very_small_parabola_nonpos ht0 ht
  obtain ⟨j, hj, _⟩ := shared_fiberInfimum_attained (mu := mu) hq0.le hq1.le M
  have hfinf := very_small_fiber_lower hqa hqb hmu M j
  rw [← hj] at hfinf
  have hscale : mu ^ (3 / 2 : ℝ) / (16 * Real.sqrt (variance q) * gaussianA) ≤
      mu ^ (3 / 2 : ℝ) / (16 * Real.sqrt vmin * gaussianA) := by
    apply div_le_div_of_nonneg_left (Real.rpow_nonneg hmu.le _) (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hvminq)
      (by norm_num : (0 : ℝ) ≤ 16)) hga.le
  have hdef : V22.deficitG q mu b 0 M ≤ A * mu ^ (3 / 2 : ℝ) + b := by
    unfold V22.deficitG V22.positivePart V22.targetLine
    norm_num only [zero_mul, add_zero]
    apply max_le
    · have hAeq : A * mu ^ (3 / 2 : ℝ) =
          mu ^ (3 / 2 : ℝ) / (16 * Real.sqrt vmin * gaussianA) := by
        dsimp [A]
        ring
      rw [hAeq]
      linarith
    · exact hAM
  have hLB : 0 ≤ -Real.log (1 - qb) := by
    have hlog : Real.log (1 - qb) ≤ 0 := by
      simpa only [Real.log_one] using Real.log_le_log (by linarith : 0 < 1 - qb)
        (by linarith : 1 - qb ≤ 1)
    linarith
  have hlog : -Real.log (1 - q) ≤ -Real.log (1 - qb) :=
    neg_le_neg (Real.log_le_log (by linarith : 0 < 1 - qb) (by linarith : 1 - qb ≤ 1 - q))
  have hInv : 1 / (1 - q) ^ M = Real.exp (-(M : ℝ) * Real.log (1 - q)) := by
    have hlogpow : -(M : ℝ) * Real.log (1 - q) = -Real.log ((1 - q) ^ M) := by
      rw [Real.log_pow] <;> ring
    rw [hlogpow, Real.exp_neg, Real.exp_log hbase] <;>
      simp only [one_div]
  have hweight : (1 / (1 - q) ^ M) * Real.exp (-ell * mu) ≤ Real.exp (-c * mu) := by
    rw [hInv, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
    have h2 := mul_le_mul_of_nonneg_right hcut.le hLB
    dsimp [c]
    nlinarith
  have hpricing : 0 ≤ (1 / (1 - q) ^ M) * Real.exp (-ell * mu) :=
    (mul_pos (div_pos (by norm_num : (0 : ℝ) < 1) hbase)
      (Real.exp_pos (-ell * mu))).le
  have hweighted := mul_le_mul_of_nonneg_left hdef hpricing
  have hweightProd := mul_le_mul_of_nonneg_right hweight hAM
  have hprice := (rpow_exp_price_antitone hA hb hmc hdecay) (le_refl mc) hmcmu hmcmu
  unfold spikeAtomPrice
  calc
    _ ≤ ((1 / (1 - q) ^ M) * Real.exp (-ell * mu)) * (A * mu ^ (3 / 2 : ℝ) + b) := hweighted
    _ ≤ Real.exp (-c * mu) * (A * mu ^ (3 / 2 : ℝ) + b) := hweightProd
    _ = (A * mu ^ (3 / 2 : ℝ) + b) * Real.exp (-c * mu) := by ring
    _ ≤ (A * mc ^ (3 / 2 : ℝ) + b) * Real.exp (-c * mc) := hprice
    _ = _ := by dsimp [A, mc, c]; ring

theorem smallFiberK_pos {M : ℕ} (hM : M ≤ 7) : 0 < V22.Checks.smallFiberK M := by
  have hrat : (0 : ℚ) < V22.smallK.getD M 0 := by
    interval_cases M <;> decide
  unfold V22.Checks.smallFiberK
  exact_mod_cast hrat

theorem spike_psi_mono {t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) (hs : s ≤ 1) :
    V22.psi t ≤ V22.psi s := by
  have hfac : 0 ≤ (s - t) * (10 - (9 / 2 : ℝ) * (s + t)) :=
    mul_nonneg (by linarith only [hts]) (by linarith only [ht, hts, hs])
  unfold V22.psi
  nlinarith

theorem small_fiber_psi_excess_negative {M : ℕ} (hM : M ≤ 7) {mu0 b : ℝ}
    (hmu0 : 19 ≤ mu0) (hb : b ≤ 1) : V22.psi ((M : ℝ) / mu0) + b < 0 := by
  have hmup : 0 < mu0 := by linarith
  have hMr : (M : ℝ) ≤ 7 := by exact_mod_cast hM
  have ht0 : 0 ≤ (M : ℝ) / mu0 := div_nonneg (Nat.cast_nonneg _) hmup.le
  have ht : (M : ℝ) / mu0 ≤ (7 / 19 : ℝ) := (div_le_iff₀ hmup).2 (by nlinarith)
  have hpsi := spike_psi_mono ht0 ht (by norm_num : (7 / 19 : ℝ) ≤ 1)
  norm_num [V22.psi] at hpsi ⊢
  linarith

/-- The negative additive constant in Lemma `lem:KM` is retained. The
source derivative proviso is sufficient at the starting mean; it then
continues to hold at every larger mean. -/
theorem rpow_exp_negative_shift_antitone {A C ell m : ℝ} (hA : 0 ≤ A)
    (hC : C ≤ 0) (hell : 0 < ell) (hm : 0 < m)
    (hstart : (3 / 2 : ℝ) * A * Real.sqrt m ≤ ell * (A * m ^ (3 / 2 : ℝ) + C)) :
    AntitoneOn (fun x : ℝ => (A * x ^ (3 / 2 : ℝ) + C) * Real.exp (-ell * x)) (Ici m) := by
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hpow : ∀ x : ℝ, 0 < x → x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
    intro x hx
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add hx, Real.rpow_one]
  have hstart' : -ell * C ≤ (ell * A * m - (3 / 2 : ℝ) * A) * Real.sqrt m := by
    rw [hpow m hm] at hstart
    nlinarith
  have hk : 0 ≤ ell * A * m - (3 / 2 : ℝ) * A := by
    have hneg : 0 ≤ -ell * C := by
      have h := mul_nonpos_of_nonneg_of_nonpos hell.le hC
      linarith
    nlinarith
  let f : ℝ → ℝ := fun x => (A * x ^ (3 / 2 : ℝ) + C) * Real.exp (-ell * x)
  have hd : ∀ x ∈ Ici m, HasDerivAt f
      (Real.exp (-ell * x) * ((3 / 2 : ℝ) * A * Real.sqrt x - ell * (A * x ^ (3 / 2 : ℝ) + C))) x := by
    intro x hx
    have hx0 : 0 < x := hm.trans_le hx
    convert ((((Real.hasDerivAt_rpow_const (p := (3 / 2 : ℝ)) (Or.inl hx0.ne')).const_mul A).add_const C).mul
      (((hasDerivAt_id x).const_mul (-ell)).exp)) using 1 <;>
      dsimp [f] <;> simp only [Real.sqrt_eq_rpow] <;> norm_num <;> ring
  have hf : ContinuousOn f (Ici m) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici m) hf
    (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
  intro x hx
  have hxm : m ≤ x := interior_subset hx
  have hx0 : 0 < x := hm.trans_le hxm
  have hcoef : ell * A * m - (3 / 2 : ℝ) * A ≤ ell * A * x - (3 / 2 : ℝ) * A := by
    have h := mul_le_mul_of_nonneg_left hxm (mul_nonneg hell.le hA)
    linarith
  have hsqrt := Real.sqrt_le_sqrt hxm
  have hprod := mul_le_mul hcoef hsqrt (Real.sqrt_nonneg m) (hk.trans hcoef)
  have hcondition : (3 / 2 : ℝ) * A * Real.sqrt x ≤ ell * (A * x ^ (3 / 2 : ℝ) + C) := by
    rw [hpow x hx0]
    nlinarith
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith)

theorem small_fiber_lower_of_vmin (hB1 : V22.Checks.lemma_7_12) {M : ℕ} (hM : M ≤ 7)
    {q mu vmin : ℝ} (hqa : 1 / 4 ≤ q) (hqb : q ≤ 3 / 4) (hmu : 0 < mu)
    (hvmin : 0 < vmin) (hvq : vmin ≤ variance q) (j : ℤ) :
    -(V22.Checks.smallFiberK M / (4 * gaussianA * Real.sqrt vmin)) * mu ^ (3 / 2 : ℝ) ≤
      V22.fiberFunction q mu M j := by
  have hK := smallFiberK_nonneg hM
  have hs := Real.sqrt_pos.2 hvmin
  have hga := gaussianA_pos
  have hcoeff : V22.Checks.smallFiberK M / (4 * gaussianA * Real.sqrt (variance q)) ≤
      V22.Checks.smallFiberK M / (4 * gaussianA * Real.sqrt vmin) := by
    apply div_le_div_of_nonneg_left hK (by positivity)
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hvq) (by positivity)
  have hscale := mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hmu.le (3 / 2))
  have hlocal := small_fiber_lower hB1 hM hqa hqb hmu j
  linarith

theorem small_fiber_deficit_bound (hB1 : V22.Checks.lemma_7_12) {M : ℕ} (hM : M ≤ 7)
    {q mu mu0 vmin b : ℝ} (hqa : 1 / 4 ≤ q) (hqb : q ≤ 3 / 4) (hmu0 : 19 ≤ mu0)
    (hmu : mu0 ≤ mu) (hvmin : 0 < vmin) (hvq : vmin ≤ variance q) :
    V22.deficitG q mu b 0 M ≤ max
      (V22.Checks.smallFiberK M / (4 * gaussianA * Real.sqrt vmin) * mu ^ (3 / 2 : ℝ) +
        V22.psi ((M : ℝ) / mu0) + b) 0 := by
  have hmup0 : 0 < mu0 := by linarith
  have hmup : 0 < mu := hmup0.trans_le hmu
  have ht0 : 0 ≤ (M : ℝ) / mu := div_nonneg (Nat.cast_nonneg _) hmup.le
  have hts : (M : ℝ) / mu ≤ (M : ℝ) / mu0 :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) hmup0 hmu
  have hMr : (M : ℝ) ≤ 7 := by exact_mod_cast hM
  have hs : (M : ℝ) / mu0 ≤ 1 := (div_le_iff₀ hmup0).2 (by linarith)
  have hpsi := spike_psi_mono ht0 hts hs
  obtain ⟨j, hj, _⟩ := shared_fiberInfimum_attained (mu := mu) (by linarith : 0 ≤ q) (by linarith : q ≤ 1) M
  have hfloor := small_fiber_lower_of_vmin hB1 hM hqa hqb hmup hvmin hvq j
  rw [← hj] at hfloor
  unfold V22.deficitG V22.positivePart V22.targetLine
  norm_num only [zero_mul, add_zero]
  apply max_le_max
  · linarith
  · exact le_rfl

theorem spike_inverse_weight_le {q qb : ℝ} (hqqb : q ≤ qb) (hqb : qb < 1) (M : ℕ) :
    1 / (1 - q) ^ M ≤ 1 / (1 - qb) ^ M := by
  apply div_le_div_of_nonneg_left (by norm_num) (pow_pos (by linarith) M)
  exact pow_le_pow_left₀ (by linarith : 0 ≤ 1 - qb) (by linarith : 1 - qb ≤ 1 - q) M

/-- The first price of Lemma `lem:KM`, including its exact derivative
proviso and the source positive part at the starting mean. -/
theorem small_spike_price_first (hB1 : V22.Checks.lemma_7_12) {M : ℕ} (hM : M ≤ 7)
    {q qb mu mu0 vmin ell b : ℝ} (hqa : 1 / 4 ≤ q) (hqb : q ≤ 3 / 4)
    (hqqb : q ≤ qb) (hqb1 : qb < 1) (hmu0 : 19 ≤ mu0) (hmu : mu0 ≤ mu)
    (hvmin : 0 < vmin) (hvq : vmin ≤ variance q) (hell : 0 < ell) (hb : b ≤ 1)
    (hstart : (3 / 2 : ℝ) * (V22.Checks.smallFiberK M / (4 * gaussianA * Real.sqrt vmin)) * Real.sqrt mu0 ≤
      ell * (V22.Checks.smallFiberK M / (4 * gaussianA * Real.sqrt vmin) * mu0 ^ (3 / 2 : ℝ) +
        V22.psi ((M : ℝ) / mu0) + b)) :
    spikeAtomPrice q mu b 0 ell M ≤ max
      (V22.Checks.smallFiberK M / (4 * gaussianA * Real.sqrt vmin) * mu0 ^ (3 / 2 : ℝ) +
        V22.psi ((M : ℝ) / mu0) + b) 0 * (1 / (1 - qb) ^ M) * Real.exp (-ell * mu0) := by
  let A := V22.Checks.smallFiberK M / (4 * gaussianA * Real.sqrt vmin)
  let C := V22.psi ((M : ℝ) / mu0) + b
  have hmup0 : 0 < mu0 := by linarith
  have hmup : 0 < mu := hmup0.trans_le hmu
  have hA : 0 < A := by dsimp [A]; exact div_pos (smallFiberK_pos hM) (by positivity [gaussianA_pos])
  have hC : C < 0 := small_fiber_psi_excess_negative hM hmu0 hb
  have hs0 : 0 < Real.sqrt mu0 := Real.sqrt_pos.2 hmup0
  have hstart' : (3 / 2 : ℝ) * A * Real.sqrt mu0 ≤ ell * (A * mu0 ^ (3 / 2 : ℝ) + C) := by
    dsimp [A, C]
    nlinarith [hstart]
  have hbase : 0 < A * mu0 ^ (3 / 2 : ℝ) + C := by
    have hleft : 0 < (3 / 2 : ℝ) * A * Real.sqrt mu0 := by positivity
    nlinarith
  have hpowers := Real.rpow_le_rpow hmup0.le hmu (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have hAm := mul_le_mul_of_nonneg_left hpowers hA.le
  have hbaseMu : 0 ≤ A * mu ^ (3 / 2 : ℝ) + C := by linarith
  have hdef := small_fiber_deficit_bound (M := M) (q := q) (mu := mu)
    (mu0 := mu0) (vmin := vmin) (b := b) hB1 hM hqa hqb hmu0 hmu hvmin hvq
  have hdef' : V22.deficitG q mu b 0 M ≤ max (A * mu ^ (3 / 2 : ℝ) + C) 0 := by
    simpa only [A, C, add_assoc] using hdef
  rw [max_eq_left hbaseMu] at hdef'
  have hprice := (rpow_exp_negative_shift_antitone hA.le hC.le hell hmup0 hstart')
    (le_refl mu0) hmu hmu
  have hpricing : 0 ≤ (1 / (1 - q) ^ M) * Real.exp (-ell * mu) :=
    mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 1)
      (pow_pos (by linarith : 0 < 1 - q) M).le) (Real.exp_pos (-ell * mu)).le
  have hweighted := mul_le_mul_of_nonneg_left hdef' hpricing
  have hw := spike_inverse_weight_le hqqb hqb1 M
  have hweight := mul_le_mul_of_nonneg_right hw
    (mul_nonneg hbaseMu (Real.exp_pos (-ell * mu)).le)
  have hqbWeight : 0 ≤ (1 : ℝ) / (1 - qb) ^ M :=
    div_nonneg (by norm_num) (pow_pos (sub_pos.mpr hqb1) M).le
  have hpriceWeighted := mul_le_mul_of_nonneg_left hprice hqbWeight
  unfold spikeAtomPrice
  change _ ≤ max (A * mu0 ^ (3 / 2 : ℝ) + V22.psi ((M : ℝ) / mu0) + b) 0 * _ * _
  have hbase0 : 0 ≤ A * mu0 ^ (3 / 2 : ℝ) + V22.psi ((M : ℝ) / mu0) + b := by
    dsimp [C] at hbase
    linarith
  rw [max_eq_left hbase0]
  calc
    _ ≤ ((1 / (1 - q) ^ M) * Real.exp (-ell * mu)) * (A * mu ^ (3 / 2 : ℝ) + C) := hweighted
    _ = (1 / (1 - q) ^ M) * ((A * mu ^ (3 / 2 : ℝ) + C) * Real.exp (-ell * mu)) := by ring
    _ ≤ (1 / (1 - qb) ^ M) * ((A * mu ^ (3 / 2 : ℝ) + C) * Real.exp (-ell * mu)) := hweight
    _ ≤ (1 / (1 - qb) ^ M) * ((A * mu0 ^ (3 / 2 : ℝ) + C) * Real.exp (-ell * mu0)) := hpriceWeighted
    _ = _ := by dsimp [C]; ring

/-- Lemma `lem:KM`'s second branch. The source hypothesis that the starting
base is nonpositive is retained, though the resulting larger price is valid
whenever its stated exponential decay test holds. -/
theorem small_spike_price_second (hB1 : V22.Checks.lemma_7_12) {M : ℕ} (hM : M ≤ 7)
    {q qb mu mu0 vmin ell b : ℝ} (hqa : 1 / 4 ≤ q) (hqb : q ≤ 3 / 4)
    (hqqb : q ≤ qb) (hqb1 : qb < 1) (hmu0 : 19 ≤ mu0) (hmu : mu0 ≤ mu)
    (hvmin : 0 < vmin) (hvq : vmin ≤ variance q) (hb : b ≤ 1)
    (_hbase : V22.Checks.smallFiberK M / (4 * gaussianA * Real.sqrt vmin) * mu0 ^ (3 / 2 : ℝ) +
      V22.psi ((M : ℝ) / mu0) + b ≤ 0)
    (hdecay : (3 / 2 : ℝ) ≤ ell * mu0) :
    spikeAtomPrice q mu b 0 ell M ≤
      (V22.Checks.smallFiberK M / (4 * gaussianA * Real.sqrt vmin) * mu0 ^ (3 / 2 : ℝ)) *
        (1 / (1 - qb) ^ M) * Real.exp (-ell * mu0) := by
  let A := V22.Checks.smallFiberK M / (4 * gaussianA * Real.sqrt vmin)
  have hmup0 : 0 < mu0 := by linarith
  have hmup : 0 < mu := hmup0.trans_le hmu
  have hA : 0 ≤ A := by dsimp [A]; positivity [smallFiberK_nonneg hM, gaussianA_pos]
  have hAm : 0 ≤ A * mu ^ (3 / 2 : ℝ) :=
    mul_nonneg hA (Real.rpow_nonneg hmup.le (3 / 2 : ℝ))
  have hC := small_fiber_psi_excess_negative hM hmu0 hb
  have hdef := small_fiber_deficit_bound (M := M) (q := q) (mu := mu)
    (mu0 := mu0) (vmin := vmin) (b := b) hB1 hM hqa hqb hmu0 hmu hvmin hvq
  have hmax : max (A * mu ^ (3 / 2 : ℝ) + V22.psi ((M : ℝ) / mu0) + b) 0 ≤ A * mu ^ (3 / 2 : ℝ) := by
    apply max_le <;> linarith
  have hdefA : V22.deficitG q mu b 0 M ≤ A * mu ^ (3 / 2 : ℝ) := hdef.trans hmax
  have hprice := (rpow_exp_price_antitone hA (by norm_num : (0 : ℝ) ≤ 0) hmup0 hdecay)
    (le_refl mu0) hmu hmu
  simp only [add_zero] at hprice
  have hpricing : 0 ≤ (1 / (1 - q) ^ M) * Real.exp (-ell * mu) :=
    mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 1)
      (pow_pos (by linarith : 0 < 1 - q) M).le) (Real.exp_pos (-ell * mu)).le
  have hweighted := mul_le_mul_of_nonneg_left hdefA hpricing
  have hw := spike_inverse_weight_le hqqb hqb1 M
  have hweight := mul_le_mul_of_nonneg_right hw (mul_nonneg hAm (Real.exp_pos (-ell * mu)).le)
  have hqbWeight : 0 ≤ (1 : ℝ) / (1 - qb) ^ M :=
    div_nonneg (by norm_num) (pow_pos (sub_pos.mpr hqb1) M).le
  have hpriceWeighted := mul_le_mul_of_nonneg_left hprice hqbWeight
  unfold spikeAtomPrice
  change _ ≤ (A * mu0 ^ (3 / 2 : ℝ)) * _ * _
  calc
    _ ≤ ((1 / (1 - q) ^ M) * Real.exp (-ell * mu)) * (A * mu ^ (3 / 2 : ℝ)) := hweighted
    _ = (1 / (1 - q) ^ M) * ((A * mu ^ (3 / 2 : ℝ)) * Real.exp (-ell * mu)) := by ring
    _ ≤ (1 / (1 - qb) ^ M) * ((A * mu ^ (3 / 2 : ℝ)) * Real.exp (-ell * mu)) := hweight
    _ ≤ (1 / (1 - qb) ^ M) * ((A * mu0 ^ (3 / 2 : ℝ)) * Real.exp (-ell * mu0)) := hpriceWeighted
    _ = _ := by ring

/-- The inherited endpoint variance is a lower bound throughout its actual
activity interval; no separate variance bound is assumed by the source
wrappers below. -/
theorem spike_endpoint_variance {qa qb q : ℝ} (hqa : 1 / 4 ≤ qa) (hqb : qb ≤ 3 / 4)
    (hqlo : qa ≤ q) (hqhi : q ≤ qb) :
    0 < min (qa * (1 - qa)) (qb * (1 - qb)) ∧
      min (qa * (1 - qa)) (qb * (1 - qb)) ≤ variance q := by
  have hqa0 : 0 < qa := by linarith
  have hqa1 : qa < 1 := by linarith
  have hqb0 : 0 < qb := by linarith
  have hqb1 : qb < 1 := by linarith
  refine ⟨lt_min (mul_pos hqa0 (sub_pos.mpr hqa1)) (mul_pos hqb0 (sub_pos.mpr hqb1)), ?_⟩
  unfold variance
  by_cases hqhalf : q ≤ 1 / 2
  · have hfac : 0 ≤ (q - qa) * (1 - q - qa) := mul_nonneg (by linarith) (by linarith)
    exact (min_le_left _ _).trans (by nlinarith)
  · have hfac : 0 ≤ (qb - q) * (q + qb - 1) := mul_nonneg (by linarith) (by linarith)
    exact (min_le_right _ _).trans (by nlinarith)

theorem spike_endpoint_r_cap {qa qb q : ℝ} (hqa : 1 / 4 ≤ qa) (hqb : qb ≤ 3 / 4)
    (hqlo : qa ≤ q) (hqhi : q ≤ qb) :
    (max |2 * qa - 1| |2 * qb - 1|) ^ 2 < 1 ∧
      signedR q ^ 2 ≤ (max |2 * qa - 1| |2 * qb - 1|) ^ 2 := by
  let rh : ℝ := max |2 * qa - 1| |2 * qb - 1|
  have hL : |2 * qa - 1| ≤ (1 / 2 : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hR : |2 * qb - 1| ≤ (1 / 2 : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hr0 : 0 ≤ rh := (abs_nonneg _).trans (le_max_left _ _)
  have hrh : rh ≤ 1 / 2 := max_le hL hR
  have hlow : -rh ≤ 2 * q - 1 := by
    have h := (neg_le_neg (le_max_left |2 * qa - 1| |2 * qb - 1|)).trans (neg_abs_le (2 * qa - 1))
    dsimp [rh]
    linarith
  have hhigh : 2 * q - 1 ≤ rh := by
    have h := (le_abs_self (2 * qb - 1)).trans (le_max_right |2 * qa - 1| |2 * qb - 1|)
    dsimp [rh]
    linarith
  have habs : |signedR q| ≤ rh := by unfold signedR; exact abs_le.mpr ⟨hlow, hhigh⟩
  refine ⟨by change rh ^ 2 < 1; nlinarith, ?_⟩
  simpa only [sq_abs] using ((sq_le_sq₀ (abs_nonneg _) hr0).mpr habs)

/-- Source Lemma `lem:spike`, with the inherited closed activity interval
as its only profile data. The endpoint cap is proved from the interval. -/
theorem source_spike_averaging {qa qb q mu ts b beta ell theta D : ℝ}
    (hqa : 1 / 4 ≤ qa) (hqb : qb ≤ 3 / 4) (hqlo : qa ≤ q) (hqhi : q ≤ qb)
    (hmu : 0 < mu) (hts : 0 < ts) (hts1 : ts ≤ 1) (hb : 0 ≤ b) (hbeta : 0 ≤ beta)
    (hf : ∀ M : ℕ, ts * mu ≤ (M : ℝ) → ∀ j : ℤ,
      V22.psi ((M : ℝ) / mu) + V22.targetLine b beta ((M : ℝ) / mu) ≤ V22.fiberFunction q mu M j)
    (hm : 0 < 1 + b - theta - 9 * D / (2 * mu) -
      (max |2 * qa - 1| |2 * qb - 1|) ^ 2 /
        ((1 - (max |2 * qa - 1| |2 * qb - 1|) ^ 2) * mu) - spikeMaxPrice q mu b beta ell ts) :
    NoValleyAtMGF2 q mu theta D [(1 - q, Real.exp (-ell * mu))] := by
  obtain ⟨hcap1, hcapq⟩ := spike_endpoint_r_cap hqa hqb hqlo hqhi
  exact spike_averaging_noValley_of_cap (hqa.trans hqlo) (hqhi.trans hqb) hmu hts hts1 hb hbeta
    hcap1 hcapq hf hm

/-- Source Lemma `lem:Zc`, with `v_min` reconstructed exactly from the
two activity endpoints. Its single decay proviso is unchanged. -/
theorem source_very_small_spike_price {qa qb q mu mu0 ell b : ℝ} {M : ℕ}
    (hqa : 1 / 4 ≤ qa) (hqb : qb ≤ 3 / 4) (hqlo : qa ≤ q) (hqhi : q ≤ qb)
    (hb : 0 ≤ b) (hmu : mu0 ≤ mu) (hM : 8 ≤ M) (hcut : (M : ℝ) < (11 / 50 : ℝ) * mu)
    (hdecay : (3 / 2 : ℝ) ≤ (ell - (11 / 50) * (-Real.log (1 - qb))) * max mu0 (400 / 11)) :
    spikeAtomPrice q mu b 0 ell M ≤
      ((max mu0 (400 / 11)) ^ (3 / 2 : ℝ) /
        (16 * Real.sqrt (min (qa * (1 - qa)) (qb * (1 - qb))) * gaussianA) + b) *
      Real.exp (-(ell - (11 / 50) * (-Real.log (1 - qb))) * max mu0 (400 / 11)) := by
  obtain ⟨hvmin, hvq⟩ := spike_endpoint_variance hqa hqb hqlo hqhi
  exact very_small_spike_price (hqa.trans hqlo) (hqhi.trans hqb) hqhi (by linarith) hvmin hvq hb hmu hM hcut hdecay

/-- Source Lemma `lem:KM`: both exact prices and both original provisos,
on the same inherited closed activity interval. The finite B1 statement
is the sole unproved certificate input; the variance floor is derived. -/
theorem source_small_spike_price (hB1 : V22.Checks.lemma_7_12) {M : ℕ} (hM : M ≤ 7)
    {qa qb q mu mu0 ell b : ℝ} (hqa : 1 / 4 ≤ qa) (hqb : qb ≤ 3 / 4)
    (hqlo : qa ≤ q) (hqhi : q ≤ qb) (hmu0 : 19 ≤ mu0) (hmu : mu0 ≤ mu)
    (hell : 0 < ell) (_hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    let A := V22.Checks.smallFiberK M /
      (4 * gaussianA * Real.sqrt (min (qa * (1 - qa)) (qb * (1 - qb))))
    ((3 / 2 : ℝ) * A * Real.sqrt mu0 ≤ ell * (A * mu0 ^ (3 / 2 : ℝ) + V22.psi ((M : ℝ) / mu0) + b) →
      spikeAtomPrice q mu b 0 ell M ≤ max (A * mu0 ^ (3 / 2 : ℝ) + V22.psi ((M : ℝ) / mu0) + b) 0 *
        (1 / (1 - qb) ^ M) * Real.exp (-ell * mu0)) ∧
    (A * mu0 ^ (3 / 2 : ℝ) + V22.psi ((M : ℝ) / mu0) + b ≤ 0 →
      (3 / 2 : ℝ) ≤ ell * mu0 →
      spikeAtomPrice q mu b 0 ell M ≤ (A * mu0 ^ (3 / 2 : ℝ)) * (1 / (1 - qb) ^ M) * Real.exp (-ell * mu0)) := by
  obtain ⟨hvmin, hvq⟩ := spike_endpoint_variance hqa hqb hqlo hqhi
  dsimp only
  constructor
  · intro hstart
    exact small_spike_price_first hB1 hM (hqa.trans hqlo) (hqhi.trans hqb) hqhi (by linarith)
      hmu0 hmu hvmin hvq hell hb1 hstart
  · intro hbase hdecay
    exact small_spike_price_second hB1 hM (hqa.trans hqlo) (hqhi.trans hqb) hqhi (by linarith)
      hmu0 hmu hvmin hvq hb1 hbase hdecay

end Erdos993Lean.Analytic.V22.Analysis
