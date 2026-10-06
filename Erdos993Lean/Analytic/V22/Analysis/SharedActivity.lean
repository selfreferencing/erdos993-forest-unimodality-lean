import Erdos993Lean.Analytic.V22.Analysis.SharedRoot
import Erdos993Lean.Analytic.V22.Analysis.GaussianEndpoints
import Erdos993Lean.Analytic.V22.Analysis.TemplateMonotonicity
import Erdos993Lean.Analytic.V22.Checks.EarlyStatements

/-!
# Exact shared activity-one and Gaussian slack statements

The D1 functions are bridged to the genuine analytic root and the proved
coordinate, slack and polynomial formulas. The public source Lemma 3.12 below
assumes only `Checks.lemma_7_2`, with its exact margin and all-real input domain.
Its endpoint comparisons are supplied by rational exponential sums, rather
than by extra assumptions. The parent owns Lean compilation.
-/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

theorem shared_tOfS_eq (s : ℝ) :
    Erdos993Lean.Analytic.V22.tOfS s = activityOneCoordinate s := rfl

theorem shared_lambdaT_eq (t : ℝ) :
    Erdos993Lean.Analytic.V22.lambdaT t = activityOneLambda_t t := rfl

theorem shared_gaussianSlack_eq (t : ℝ) :
    Erdos993Lean.Analytic.V22.gaussianSlack t = activityOneS t := by
  simp only [Erdos993Lean.Analytic.V22.gaussianSlack, activityOneS, activityOneG0,
    shared_G_eq, shared_lambdaT_eq]
  ring

theorem shared_templateTerm_eq (t M k : ℝ) :
    Erdos993Lean.Analytic.V22.templateTerm t M k = activityOneEndpointValue t M k := by
  simp only [Erdos993Lean.Analytic.V22.templateTerm, activityOneEndpointValue,
    activityOneG0, activityOneG1, activityOneG2, shared_gaussianSlack_eq,
    shared_G_eq, shared_G1_eq, shared_G2_eq, shared_lambdaT_eq]

theorem shared_templateT_eq (t M : ℝ) :
    Erdos993Lean.Analytic.V22.templateT t M = activityOneT t M := by
  simp only [Erdos993Lean.Analytic.V22.templateT, activityOneT, shared_templateTerm_eq,
    Erdos993Lean.Analytic.V22.kbar]

theorem shared_psi_eq (t : ℝ) : Erdos993Lean.Analytic.V22.psi t = activityOnePsi t := rfl

theorem shared_phi_eq (s : ℝ) : Erdos993Lean.Analytic.V22.phi s = gaussianPhi s := rfl

theorem shared_Lambda_eq (a : ℝ) :
    Erdos993Lean.Analytic.V22.Lambda a = gaussianLambda a := rfl

theorem shared_polynomialLambdaQuotient_eq (a : ℝ) :
    Erdos993Lean.Analytic.V22.polynomialLambdaQuotient a = gaussianLambdaQuotient a := rfl

theorem shared_Q_eq (a : ℝ) : Erdos993Lean.Analytic.V22.Q a = gaussianQ a := rfl

/-- The exact D7.2 proposition supplies the sole finite Gaussian premise. -/
theorem shared_gaussianQCertificate (hQ : Checks.lemma_7_2) : GaussianSlackQCertificate := by
  intro a ha
  have h := hQ a ⟨ha.1, ha.2⟩
  simpa only [shared_Q_eq] using h

theorem shared_tOfS_pos {s : ℝ} (hs : -1 < s) :
    0 < Erdos993Lean.Analytic.V22.tOfS s := by
  rw [shared_tOfS_eq]
  exact activityOneCoordinate_pos hs

theorem shared_tOfS_strictMonoOn :
    StrictMonoOn Erdos993Lean.Analytic.V22.tOfS (Ioi (-1)) := by
  intro s hs t ht hst
  simpa only [shared_tOfS_eq] using activityOneCoordinate_strictMonoOn hs ht hst

theorem shared_gaussianSlack_positive {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 67 / 100) :
    s ^ 2 * Erdos993Lean.Analytic.V22.phi s ≤
        Erdos993Lean.Analytic.V22.gaussianSlack (Erdos993Lean.Analytic.V22.tOfS s) ∧
      0 ≤ s ^ 2 * Erdos993Lean.Analytic.V22.phi s := by
  simpa only [shared_phi_eq, shared_gaussianSlack_eq, shared_tOfS_eq] using
    gaussianSlack_positive hs0 hs1

theorem shared_gaussianSlack_negative (hQ : Checks.lemma_7_2) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 66 / 125) :
    a ^ 2 / (1 - a) * Erdos993Lean.Analytic.V22.Q a ≤
        Erdos993Lean.Analytic.V22.gaussianSlack (Erdos993Lean.Analytic.V22.tOfS (-a)) ∧
      0 ≤ a ^ 2 / (1 - a) * Erdos993Lean.Analytic.V22.Q a := by
  simpa only [shared_Q_eq, shared_gaussianSlack_eq, shared_tOfS_eq] using
    gaussianSlack_negative (shared_gaussianQCertificate hQ) ha0 ha1

theorem shared_gaussianSlack_coordinate_nonneg (hQ : Checks.lemma_7_2) {s : ℝ}
    (hs0 : -(66 / 125 : ℝ) ≤ s) (hs1 : s ≤ 67 / 100) :
    0 ≤ Erdos993Lean.Analytic.V22.gaussianSlack (Erdos993Lean.Analytic.V22.tOfS s) := by
  simpa only [shared_gaussianSlack_eq, shared_tOfS_eq] using
    gaussianSlack_nonneg_coordinate (shared_gaussianQCertificate hQ) hs0 hs1

theorem shared_gaussianSlack_endpoints :
    Erdos993Lean.Analytic.V22.tOfS (-(66 / 125 : ℝ)) ≤ (1499 / 2500 : ℝ) ∧
      (321 / 200 : ℝ) ≤ Erdos993Lean.Analytic.V22.tOfS (67 / 100) := by
  simpa only [shared_tOfS_eq] using gaussianSlack_endpoint_certificate

theorem shared_gaussianSlack_source_range (hQ : Checks.lemma_7_2) {t : ℝ}
    (ht0 : (1499 / 2500 : ℝ) ≤ t) (ht1 : t ≤ 321 / 200) :
    0 ≤ Erdos993Lean.Analytic.V22.gaussianSlack t := by
  rw [shared_gaussianSlack_eq]
  exact gaussianSlack_nonneg_source_range_of_Q (shared_gaussianQCertificate hQ) ht0 ht1

/-- Paper Lemma 3.12 on the native D1 functions, including both lower-bound
chains, coordinate domain, exact endpoint containment and final interval. -/
theorem source_lemma_3_12 (hQ : Checks.lemma_7_2) :
    (∀ s : ℝ, 0 ≤ s → s ≤ 67 / 100 →
      s ^ 2 * Erdos993Lean.Analytic.V22.phi s ≤
          Erdos993Lean.Analytic.V22.gaussianSlack (Erdos993Lean.Analytic.V22.tOfS s) ∧
        0 ≤ s ^ 2 * Erdos993Lean.Analytic.V22.phi s) ∧
    (∀ a : ℝ, 0 ≤ a → a ≤ 66 / 125 →
      a ^ 2 / (1 - a) * Erdos993Lean.Analytic.V22.Q a ≤
          Erdos993Lean.Analytic.V22.gaussianSlack (Erdos993Lean.Analytic.V22.tOfS (-a)) ∧
        0 ≤ a ^ 2 / (1 - a) * Erdos993Lean.Analytic.V22.Q a) ∧
    (∀ s : ℝ, -(66 / 125 : ℝ) ≤ s → s ≤ 67 / 100 →
      0 ≤ Erdos993Lean.Analytic.V22.gaussianSlack (Erdos993Lean.Analytic.V22.tOfS s)) ∧
    (Erdos993Lean.Analytic.V22.tOfS (-(66 / 125 : ℝ)) ≤ (1499 / 2500 : ℝ) ∧
      (321 / 200 : ℝ) ≤ Erdos993Lean.Analytic.V22.tOfS (67 / 100)) ∧
    (∀ t : ℝ, (1499 / 2500 : ℝ) ≤ t → t ≤ 321 / 200 →
      0 ≤ Erdos993Lean.Analytic.V22.gaussianSlack t) :=
  ⟨fun _ hs0 hs1 => shared_gaussianSlack_positive hs0 hs1,
    fun _ ha0 ha1 => shared_gaussianSlack_negative hQ ha0 ha1,
    fun _ hs0 hs1 => shared_gaussianSlack_coordinate_nonneg hQ hs0 hs1,
    shared_gaussianSlack_endpoints,
    fun _ ht0 ht1 => shared_gaussianSlack_source_range hQ ht0 ht1⟩

/-- Shared template monotonicity, preserving the exact D1 endpoint formula. -/
theorem shared_templateT_mono {t M0 M : ℝ} (hM0 : 0 < M0) (hM : M0 ≤ M)
    (hS : 0 ≤ Erdos993Lean.Analytic.V22.gaussianSlack t) :
    Erdos993Lean.Analytic.V22.templateT t M0 ≤ Erdos993Lean.Analytic.V22.templateT t M := by
  rw [shared_templateT_eq, shared_templateT_eq]
  rw [shared_gaussianSlack_eq] at hS
  exact activityOneT_mono hM0 hM hS

end Erdos993Lean.Analytic.V22.Analysis
