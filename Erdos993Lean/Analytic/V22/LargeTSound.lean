import Erdos993Lean.Analytic.V22.Compute.LargeT
import Erdos993Lean.Analytic.V22.GridSound
import Erdos993Lean.Analytic.V22.CoefficientExprsSound
import Erdos993Lean.Analytic.V22.Checks.EarlyStatements

/-! Soundness on both sides of the exact A5/D4 radical split, followed by
the all-N decreasing exponential constant. -/

namespace Erdos993Lean.Analytic.V22.Compute.LargeT
open TailCert

@[simp] theorem evalR_cut (rm Nstar : Rat) (envR : Nat → ℝ) :
    (cut rm Nstar).evalR envR = (rm : ℝ)*Real.sqrt (Nstar : ℝ) := by
  simp [cut, Expr.evalR]

@[simp] theorem evalR_largeConstant (N : Expr) (envR : Nat → ℝ) :
    (largeConstant N).evalR envR = Checks.largeTConstant (N.evalR envR) := by
  norm_num [largeConstant, Expr.evalR, Checks.largeTConstant]
  rw [div_div]

theorem largeTConstant_antitone {N0 N : ℝ} (hN0 : 0 < N0) (hN : N0 ≤ N) :
    Checks.largeTConstant N ≤ Checks.largeTConstant N0 := by
  have h1 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3/4) hN0 hN
  have hs : N0^2 ≤ N^2 := pow_le_pow_left₀ hN0.le hN 2
  have h2 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 11/10)
    (sq_pos_of_pos hN0) hs
  have he := Real.exp_le_exp.mpr (add_le_add h1 h2)
  unfold Checks.largeTConstant
  have he' : Real.exp (3/(4*N)+(11/10)/N^2) ≤
      Real.exp (3/(4*N0)+(11/10)/N0^2) := by
    simpa only [div_div] using he
  exact mul_le_mul_of_nonneg_left he' (mul_nonneg
    (mul_nonneg (by norm_num) (Real.exp_pos _).le) (Real.rpow_nonneg (by norm_num) _))

theorem check_sound (rm Nstar : Rat) (hrm : 0 < (rm : ℝ))
    (hNstar : 0 < (Nstar : ℝ)) (hcut : (rm : ℝ)*Real.sqrt (Nstar : ℝ) < 6)
    (h : check rm Nstar = true) : Checks.largeTConditions rm Nstar := by
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hc1,hc2⟩,hp1⟩,hp2⟩,hp3⟩ := h
  have hcutpos : 0 < (rm : ℝ)*Real.sqrt (Nstar : ℝ) :=
    mul_pos hrm (Real.sqrt_pos.mpr hNstar)
  constructor
  · intro nu hnu
    let x := nu/((rm : ℝ)*Real.sqrt (Nstar : ℝ))
    have hx : ((0 : Rat) : ℝ) ≤ x ∧ x ≤ ((1 : Rat) : ℝ) := by
      norm_num only [Rat.cast_zero, Rat.cast_one]
      constructor
      · exact div_nonneg hnu.1 hcutpos.le
      · exact (div_le_one hcutpos).2 hnu.2
    have he := nonnegativeOn_sound hc1 hp1 hx
    have hmul : (rm : ℝ)*Real.sqrt (Nstar : ℝ)*x = nu := by
      dsimp [x]
      field_simp [ne_of_gt hcutpos]
    norm_num [firstMargin, threshold, firstNu, Expr.evalR, realSpanEnv, hmul] at he
    linarith
  constructor
  · intro nu hnu
    let x := (nu-(rm : ℝ)*Real.sqrt (Nstar : ℝ))/(6-(rm : ℝ)*Real.sqrt (Nstar : ℝ))
    have hden : 0 < 6-(rm : ℝ)*Real.sqrt (Nstar : ℝ) := sub_pos.mpr hcut
    have hx : ((0 : Rat) : ℝ) ≤ x ∧ x ≤ ((1 : Rat) : ℝ) := by
      norm_num only [Rat.cast_zero, Rat.cast_one]
      constructor
      · exact div_nonneg (sub_nonneg.mpr hnu.1) hden.le
      · apply (div_le_one hden).2
        linarith [hnu.2]
    have he := nonnegativeOn_sound hc2 hp2 hx
    have hmul : (rm : ℝ)*Real.sqrt (Nstar : ℝ)+(6-(rm : ℝ)*Real.sqrt (Nstar : ℝ))*x = nu := by
      dsimp [x]
      field_simp [ne_of_gt hden]
      <;> ring
    norm_num [secondMargin, threshold, secondN, secondNu, Expr.evalR, realSpanEnv, hmul] at he
    linarith
  · intro N hN
    have hm : ∀ i, (zeroEnv i).Mem ((fun _ => (0 : ℝ)) i) := by
      intro i
      simpa [zeroEnv] using mem_ofRat (0 : Rat)
    have he := (largeConstant (.rat Nstar)).upperOK_sound (249/400) hm hp3
    norm_num [Expr.evalR] at he
    exact (largeTConstant_antitone hNstar hN).trans he

theorem a5Check_sound (h : a5Check = true) : Checks.lemma_7_10 := by
  have hcut : ((1/4 : Rat) : ℝ)*Real.sqrt ((162/5 : Rat) : ℝ) < 6 := by
    have hs : Real.sqrt ((162/5 : Rat) : ℝ) < 24 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
    norm_num at hs ⊢
    linarith
  have hc := check_sound (1/4) (162/5) (by norm_num) (by norm_num) hcut h
  simpa [Checks.lemma_7_10] using hc

theorem d4Check_sound (h : d4Check = true) : Checks.lemma_7_11 := by
  have hcut : ((1/2 : Rat) : ℝ)*Real.sqrt ((66 : Rat) : ℝ) < 6 := by
    have hs : Real.sqrt ((66 : Rat) : ℝ) < 12 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
    norm_num at hs ⊢
    linarith
  have hc := check_sound (1/2) 66 (by norm_num) (by norm_num) hcut h
  simpa [Checks.lemma_7_11] using hc

end Erdos993Lean.Analytic.V22.Compute.LargeT
