import Erdos993Lean.Analytic.V22.Functions

/-!
# Monotonicity of the outer ray formula with a frozen remainder

Source: repaired note Lemma 5.4 and the block recipe used in Lemma 7.14.
The block remainder is held fixed, while the actual outer parameter `M`
increases. The proof retains the nonnegativity hypothesis for `G₂` and allows
`G₁` to have either sign. Its endpoint maximum is controlled by convexity on
the shrinking interval `[3.55, kbar M]`.

No coefficient-bound recipe or root existence is asserted here. A consuming
block certificate must supply its remainder bound and the displayed `G₂`
hypothesis. No finite cell is evaluated by this module.
-/

namespace Erdos993Lean.Analytic.V22

noncomputable section

/-- The two endpoint terms in the common outer ray formula. -/
def endpointPolynomial (M k g1 g2 : ℝ) : ℝ :=
  2 * k * g1 + k ^ 2 * g2 / (M + 3)

/-- At a fixed endpoint, increasing the outer parameter decreases the
nonnegative quadratic term. The linear coefficient may have either sign. -/
theorem endpointPolynomial_antitone_parameter {M M1 k g1 g2 : ℝ}
    (hM1 : 0 < M1 + 3) (hM : M1 ≤ M) (hg2 : 0 ≤ g2) :
    endpointPolynomial M k g1 g2 ≤ endpointPolynomial M1 k g1 g2 := by
  have hnum : 0 ≤ k ^ 2 * g2 := mul_nonneg (sq_nonneg k) hg2
  have hden : M1 + 3 ≤ M + 3 := by simpa only [add_comm] using add_le_add_right hM 3
  have hquad := div_le_div_of_nonneg_left hnum hM1 hden
  simpa only [endpointPolynomial, add_comm] using add_le_add_left hquad (2 * k * g1)

/-- Convexity retains the arbitrary linear term; only the quadratic
coefficient is required to be nonnegative. -/
theorem endpointPolynomial_convexOn {M g1 g2 : ℝ}
    (hM : 0 < M + 3) (hg2 : 0 ≤ g2) :
    ConvexOn ℝ Set.univ (fun k : ℝ => endpointPolynomial M k g1 g2) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  have hbEq : b = 1 - a := by linarith
  have hgap :
      a * endpointPolynomial M x g1 g2 + b * endpointPolynomial M y g1 g2
        - endpointPolynomial M (a * x + b * y) g1 g2 =
      (g2 / (M + 3)) * a * b * (x - y) ^ 2 := by
    rw [hbEq]
    dsimp [endpointPolynomial]
    ring
  have hnonneg : 0 ≤ (g2 / (M + 3)) * a * b * (x - y) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg hg2 hM.le) ha) hb)
      (sq_nonneg (x - y))
  linarith

/-- The note's upper endpoint decreases on positive outer parameters. -/
theorem kbar_antitone {M M1 : ℝ} (hM1 : 0 < M1) (hM : M1 ≤ M) :
    kbar M ≤ kbar M1 := by
  have hquot : (10 : ℝ) / M ≤ 10 / M1 :=
    div_le_div_of_nonneg_left (by norm_num) hM1 hM
  simpa only [kbar, add_comm] using add_le_add_left hquot (77 / 20)

/-- The lower endpoint `3.55` remains inside the note's endpoint interval. -/
theorem kbar_lower {M : ℝ} (hM : 0 ≤ M) : (71 / 20 : ℝ) ≤ kbar M := by
  have hquot : 0 ≤ (10 : ℝ) / M := div_nonneg (by norm_num) hM
  dsimp [kbar]
  linarith

/-- The maximum of both endpoints decreases as the actual outer parameter
increases. This does not assert monotonicity of the upper endpoint by itself:
convexity compares it with both endpoints of the larger retained interval. -/
theorem endpointPolynomial_max_antitone {M M1 g1 g2 : ℝ}
    (hM1 : 8 ≤ M1) (hM : M1 ≤ M) (hg2 : 0 ≤ g2) :
    max (endpointPolynomial M (71 / 20) g1 g2)
        (endpointPolynomial M (kbar M) g1 g2) ≤
      max (endpointPolynomial M1 (71 / 20) g1 g2)
        (endpointPolynomial M1 (kbar M1) g1 g2) := by
  have hM1pos : 0 < M1 := by linarith
  have hMpos : 0 < M := hM1pos.trans_le hM
  have hM1den : 0 < M1 + 3 := by linarith
  have hconvex := endpointPolynomial_convexOn (g1 := g1) hM1den hg2
  have hinterval : kbar M ∈ Set.Icc (71 / 20 : ℝ) (kbar M1) :=
    ⟨kbar_lower hMpos.le, kbar_antitone hM1pos hM⟩
  have hupper : endpointPolynomial M1 (kbar M) g1 g2 ≤
      max (endpointPolynomial M1 (71 / 20) g1 g2)
        (endpointPolynomial M1 (kbar M1) g1 g2) :=
    hconvex.le_max_of_mem_Icc (Set.mem_univ _) (Set.mem_univ _) hinterval
  refine max_le ?_ ?_
  · exact (endpointPolynomial_antitone_parameter hM1den hM hg2).trans
      (le_max_left _ _)
  · exact (endpointPolynomial_antitone_parameter hM1den hM hg2).trans hupper

/-- Increasing the actual outer parameter decreases the common ray formula
with the same frozen remainder. The root-related nonnegativity assumption is
retained explicitly for the consuming certificate. -/
theorem phiWithRemainder_antitone_parameter {t M M1 D : ℝ}
    (ht : 0 ≤ t) (hM1 : 8 ≤ M1) (hM : M1 ≤ M)
    (hg2 : 0 ≤ G2 (lambdaT t)) :
    phiWithRemainder t M D ≤ phiWithRemainder t M1 D := by
  have hM1pos : 0 < M1 := by linarith
  have hquot : t / M ≤ t / M1 := div_le_div_of_nonneg_left ht hM1pos hM
  have hendpoint := endpointPolynomial_max_antitone
    (g1 := G1 (lambdaT t)) hM1 hM hg2
  have hbody :
      6 * G (lambdaT t) - 2 + D +
        max (endpointPolynomial M (71 / 20) (G1 (lambdaT t)) (G2 (lambdaT t)))
          (endpointPolynomial M (kbar M) (G1 (lambdaT t)) (G2 (lambdaT t))) ≤
      6 * G (lambdaT t) - 2 + D +
        max (endpointPolynomial M1 (71 / 20) (G1 (lambdaT t)) (G2 (lambdaT t)))
          (endpointPolynomial M1 (kbar M1) (G1 (lambdaT t)) (G2 (lambdaT t))) :=
    by simpa only [add_comm] using
      add_le_add_left hendpoint (6 * G (lambdaT t) - 2 + D)
  have hpart := max_le_max hbody (le_refl (0 : ℝ))
  have hfactor : 0 ≤ t / M1 := div_nonneg ht hM1pos.le
  have hproduct :
      t / M * positivePart
        (6 * G (lambdaT t) - 2 + D +
          max (endpointPolynomial M (71 / 20) (G1 (lambdaT t)) (G2 (lambdaT t)))
            (endpointPolynomial M (kbar M) (G1 (lambdaT t)) (G2 (lambdaT t)))) ≤
      t / M1 * positivePart
        (6 * G (lambdaT t) - 2 + D +
          max (endpointPolynomial M1 (71 / 20) (G1 (lambdaT t)) (G2 (lambdaT t)))
            (endpointPolynomial M1 (kbar M1) (G1 (lambdaT t)) (G2 (lambdaT t)))) := by
    calc
      _ ≤ t / M1 * positivePart
          (6 * G (lambdaT t) - 2 + D +
            max (endpointPolynomial M (71 / 20) (G1 (lambdaT t)) (G2 (lambdaT t)))
              (endpointPolynomial M (kbar M) (G1 (lambdaT t)) (G2 (lambdaT t)))) :=
        mul_le_mul_of_nonneg_right hquot (le_max_right _ _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hpart hfactor
  simpa only [phiWithRemainder, endpointPolynomial, add_comm] using
    add_le_add_left hproduct (t * positivePart (-gaussianSlack t))

end

end Erdos993Lean.Analytic.V22
