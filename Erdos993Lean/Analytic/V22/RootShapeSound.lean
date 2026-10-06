import Erdos993Lean.Analytic.V22.RootBracketSound

/-!
# Exact root existence and shape bounds

Source: repaired note Lemma 3.5. Existence follows from explicit real
brackets and the locally proved intermediate value theorem interface.
The root, its defining equation, and its domain are retained throughout.
The bounds for `G` below use logarithm inequalities and real algebra.
No interval oracle or finite-cell assertion is used by this module.
-/

namespace Erdos993Lean.Analytic.V22

noncomputable section

/-- The definition's chosen branch retains the domain; its default is zero.
This domain fact does not assume that the defining equation has a solution. -/
theorem rootMap_gt_neg_one (l : ℝ) : -1 < rootMap l := by
  classical
  by_cases hex : ∃ s : ℝ, -1 < s ∧ s+Real.log (1+s)=l
  · simpa only [rootMap, dif_pos hex] using (Classical.choose_spec hex).1
  · simp only [rootMap, dif_neg hex]
    norm_num

theorem G_nonneg (l : ℝ) : 0 ≤ G l := by
  have hd : 0 < 1+rootMap l := by linarith [rootMap_gt_neg_one l]
  exact div_nonneg (sq_nonneg _) hd.le

theorem G2_pos (l : ℝ) : 0 < G2 l := by
  have hroot := rootMap_gt_neg_one l
  have h1 : 0 < 1+rootMap l := by linarith
  have h2 : 0 < 2+rootMap l := by linarith
  exact div_pos (by norm_num) (mul_pos h1 h2)

/-- Every real level has a solution in a retained explicit bracket. -/
theorem root_exists (l : ℝ) : ∃ s : ℝ, -1 < s ∧ rootEquation s=l := by
  by_cases hl : 0 ≤ l
  · have hlog : 0 ≤ Real.log (1+(l+1)) := Real.log_nonneg (by linarith)
    obtain ⟨s, _, hs, heq⟩ := root_exists_in_bracket
      (l := l) (a := 0) (b := l+1) (by norm_num) (by linarith)
      (by simpa using hl) (by linarith)
    exact ⟨s, hs, heq⟩
  · have hlneg : l < 0 := lt_of_not_ge hl
    have hexppos := Real.exp_pos (l-1)
    have hexple : Real.exp (l-1) ≤ 1 := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (show l-1 ≤ 0 by linarith)
    have harg : 1+(Real.exp (l-1)-1)=Real.exp (l-1) := by ring
    have hleft : Real.exp (l-1)-1+Real.log (1+(Real.exp (l-1)-1)) ≤ l := by
      rw [harg, Real.log_exp]
      linarith
    obtain ⟨s, _, hs, heq⟩ := root_exists_in_bracket
      (l := l) (a := Real.exp (l-1)-1) (b := 0) (by linarith) (by linarith)
      hleft (by simpa using hlneg.le)
    exact ⟨s, hs, heq⟩

/-- Global existence is proved, so the actual chosen root satisfies the
equation at every real level. -/
theorem rootMap_spec (l : ℝ) :
    -1 < rootMap l ∧ rootMap l+Real.log (1+rootMap l)=l :=
  rootMap_spec_of_exists (root_exists l)

theorem rootEquation_rootMap (l : ℝ) : rootEquation (rootMap l)=l :=
  (rootMap_spec l).2

theorem rootMap_zero : rootMap 0=0 :=
  rootMap_eq_of_solution (by norm_num) (by norm_num)

theorem rootMap_strictMono : StrictMono rootMap := by
  intro a b hab
  by_contra hn
  have hroot : rootMap b ≤ rootMap a := le_of_not_gt hn
  have hlevel := rootEquation_strictMonoOn.monotoneOn
    (rootMap_gt_neg_one b) (rootMap_gt_neg_one a) hroot
  rw [rootEquation_rootMap, rootEquation_rootMap] at hlevel
  linarith

theorem rootMap_monotone : Monotone rootMap := rootMap_strictMono.monotone

theorem rootMap_nonneg {l : ℝ} (hl : 0 ≤ l) : 0 ≤ rootMap l := by
  simpa only [rootMap_zero] using rootMap_monotone hl

theorem rootMap_nonpos {l : ℝ} (hl : l ≤ 0) : rootMap l ≤ 0 := by
  simpa only [rootMap_zero] using rootMap_monotone hl

theorem rootMap_le_level {l : ℝ} (hl : 0 ≤ l) : rootMap l ≤ l := by
  have hs := rootMap_nonneg hl
  have heq := (rootMap_spec l).2
  have hlog := Real.log_nonneg (show 1 ≤ 1+rootMap l by linarith)
  linarith

/-- Increasing the level by `h≥0` increases the root by at most `h`, with
the actual root equation retained at both levels. -/
theorem rootMap_shift_le (l h : ℝ) (hh : 0 ≤ h) :
    rootMap (l+h) ≤ rootMap l+h := by
  have hs := rootMap_gt_neg_one l
  have heq := (rootMap_spec l).2
  have hlog : Real.log (1+rootMap l) ≤ Real.log (1+(rootMap l+h)) :=
    Real.log_le_log (by linarith) (by linarith)
  exact (rootMap_mem_bracket (l := l+h) (a := rootMap l) (b := rootMap l+h)
    hs (by linarith) (by linarith) (by linarith)).2

theorem rootMap_shift_bounds (l h : ℝ) (hh : 0 ≤ h) :
    rootMap l ≤ rootMap (l+h) ∧ rootMap (l+h) ≤ rootMap l+h :=
  ⟨rootMap_monotone (by linarith), rootMap_shift_le l h hh⟩

/-- The root-square quotient increases for nonnegative levels. -/
theorem G_monotone_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : G a ≤ G b := by
  have hsa := rootMap_nonneg ha
  have hsb := rootMap_nonneg (ha.trans hab)
  have hs := rootMap_monotone hab
  have hda : 0 < 1+rootMap a := by linarith
  have hdb : 0 < 1+rootMap b := by linarith
  have hc : 0 ≤ rootMap a+rootMap b+rootMap a*rootMap b := by positivity
  have hprod := mul_nonneg (sub_nonneg.mpr hs) hc
  apply (div_le_div_iff₀ hda hdb).mpr
  nlinarith

/-- The root-square quotient decreases toward level zero on the negative
half-line. The domain `s>-1` is used in the quotient comparison. -/
theorem G_antitone_nonpos {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 0) : G b ≤ G a := by
  have hsa := rootMap_nonpos (hab.trans hb)
  have hsb := rootMap_nonpos hb
  have hs := rootMap_monotone hab
  have hda : 0 < 1+rootMap a := by linarith [rootMap_gt_neg_one a]
  have hdb : 0 < 1+rootMap b := by linarith [rootMap_gt_neg_one b]
  have hc : rootMap a+rootMap b+rootMap a*rootMap b ≤ 0 := by
    have hp := mul_nonpos_of_nonpos_of_nonneg hsa hdb.le
    nlinarith
  have hprod := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hs) hc
  apply (div_le_div_iff₀ hdb hda).mpr
  nlinarith

/-- The source's quadratic upper bound follows from the elementary lower
bound `log(1+s)≥s/(1+s)` and the actual root equation. -/
theorem G_le_quadratic {l : ℝ} (hl : 0 ≤ l) : G l ≤ l^2/4 := by
  have hs := rootMap_nonneg hl
  have hd : 0 < 1+rootMap l := by linarith
  have heq := (rootMap_spec l).2
  have hlog0 := Real.one_sub_inv_le_log_of_pos hd
  have hident : 1-(1+rootMap l)⁻¹=rootMap l/(1+rootMap l) := by
    field_simp [ne_of_gt hd]
    ring
  rw [hident] at hlog0
  have hlog := (div_le_iff₀ hd).mp hlog0
  have hcleared : rootMap l*(2+rootMap l) ≤ l*(1+rootMap l) := by nlinarith
  have hleft : 0 ≤ rootMap l*(2+rootMap l) := by positivity
  have hright : 0 ≤ l*(1+rootMap l) := mul_nonneg hl hd.le
  have hsq := (sq_le_sq₀ hleft hright).mpr hcleared
  have hbound : 4*(rootMap l)^2 ≤ l^2*(1+rootMap l) := by
    apply (mul_le_mul_iff_right₀ hd).mp
    nlinarith [sq_nonneg ((rootMap l)^2)]
  apply (div_le_iff₀ hd).mpr
  nlinarith

/-- Any positive shift is controlled either by the base value on the
negative half-line or by the source's positive-part quadratic bound. -/
theorem G_shift_upper (l h : ℝ) (hh : 0 ≤ h) :
    G (l+h) ≤ max (G l) ((positivePart (l+h))^2/4) := by
  by_cases hend : l+h ≤ 0
  · exact (G_antitone_nonpos (by linarith) hend).trans (le_max_left _ _)
  · have hnonneg : 0 ≤ l+h := (lt_of_not_ge hend).le
    have hpart : positivePart (l+h)=l+h := max_eq_left hnonneg
    rw [hpart]
    exact (G_le_quadratic hnonneg).trans (le_max_right _ _)

/-- A2's full two-endpoint `Ghat` bound for a retained nonnegative shift. -/
theorem G_max_shift_upper (l h : ℝ) (hh : 0 ≤ h) :
    max (G l) (G (l+h)) ≤ max (G l) ((positivePart (l+h))^2/4) :=
  max_le (le_max_left _ _) (G_shift_upper l h hh)

theorem hbar_nonneg {M : ℝ} (hM : 0 < M) : 0 ≤ hbar M := by
  have hquot : 0 ≤ (10:ℝ)/M := div_nonneg (by norm_num) hM.le
  have hk : 0 ≤ kbar M := by dsimp [kbar]; linarith
  exact div_nonneg hk (by linarith)

/-- The exact shifted `Ghat` comparison used in the A2 cell statement. -/
theorem Ghat_quadratic_upper (t : ℝ) {M : ℝ} (hM : 0 < M) :
    Ghat t M ≤ max (G (lambdaT t)) ((positivePart (lambdaT t+hbar M))^2/4) :=
  G_max_shift_upper (lambdaT t) (hbar M) (hbar_nonneg hM)

/-- The note's `t(s)` coordinate preserves the actual root equation. -/
theorem lambdaT_tOfS {s : ℝ} (hs : -1 < s) :
    lambdaT (tOfS s)=s+Real.log (1+s) := by
  have harg : 0 < 1+s := by linarith
  have hbase : 0 < Real.exp s*(1+s) := mul_pos (Real.exp_pos s) harg
  dsimp [lambdaT, tOfS]
  rw [Real.log_rpow hbase, Real.log_mul (Real.exp_ne_zero s) (ne_of_gt harg), Real.log_exp]
  ring

theorem rootMap_lambdaT_tOfS {s : ℝ} (hs : -1 < s) :
    rootMap (lambdaT (tOfS s))=s :=
  rootMap_eq_of_solution hs (lambdaT_tOfS hs).symm

/-- The exact A2 positive-root bound, expressed in its retained `s`
coordinate rather than an independent root parameter. -/
theorem sigma0_tOfS_upper {s M : ℝ} (hs : -1 < s) (hM : 0 < M) :
    sigma0 (tOfS s) M ≤ positivePart (s+hbar M) := by
  have hshift := rootMap_shift_le (lambdaT (tOfS s)) (hbar M) (hbar_nonneg hM)
  rw [rootMap_lambdaT_tOfS hs] at hshift
  exact max_le_max hshift (le_refl 0)

end

end Erdos993Lean.Analytic.V22
