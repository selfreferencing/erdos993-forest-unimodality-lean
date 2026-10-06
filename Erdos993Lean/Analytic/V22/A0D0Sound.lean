import Erdos993Lean.Analytic.V22.Compute.A0D0
import Erdos993Lean.Analytic.V22.Checks.Statements
import Erdos993Lean.Analytic.TailCert.IvalSound

/-! Soundness of the exact-rational A0/D0 recipes. The A0 interior is
transported by its exact chord remainder, rather than endpoint sampling. -/

namespace Erdos993Lean.Analytic.V22
open Erdos993Lean.Analytic.TailCert
open Erdos993Lean.Analytic.TailCert.Compute
open Compute Checks

theorem phiQ_cast (s : Rat) : (phiQ s : ℝ) = phi s := by
  simp [phiQ, phi]

theorem psiQ_cast (t : Rat) : (psiQ t : ℝ) = psi t := by
  simp [psiQ, psi]

/-- Lemma 7.1's concavity consequence through an exact nonnegative remainder. -/
theorem phi_ge_endpoint_chord {s : ℝ} (hs : 0 ≤ s) (hsh : s ≤ 67/100) :
    (22/25 : ℝ)+(phi (67/100)-22/25)*s/(67/100) ≤ phi s := by
  have hd : 0 < (1+s)*(1+(67/100 : ℝ)) := mul_pos (by linarith) (by norm_num)
  have hc : (9/50 : ℝ) ≤ 2/((1+s)*(1+(67/100 : ℝ))) := by
    apply (le_div_iff₀ hd).2
    nlinarith
  have hp : 0 ≤ s*((67/100 : ℝ)-s) := mul_nonneg hs (sub_nonneg.mpr hsh)
  have hr : 0 ≤ s*((67/100 : ℝ)-s)*(2/((1+s)*(1+(67/100 : ℝ)))-9/50) :=
    mul_nonneg hp (sub_nonneg.mpr hc)
  have hz : (1+s) ≠ 0 := ne_of_gt (by linarith)
  have hi : phi s = (22/25 : ℝ)+(phi (67/100)-22/25)*s/(67/100)
      + s*((67/100 : ℝ)-s)*(2/((1+s)*(1+(67/100 : ℝ)))-9/50) := by
    unfold phi
    field_simp [hz]
    <;> ring
  linarith

/-- Every A0 recipe lower endpoint is a lower bound on its actual endpoint margin. -/
theorem a0_recipe_mem :
    a0Recipe0.Mem (phi 0-399/500) ∧ a0Recipe1.Mem (phi (67/100)-399/500) := by
  constructor
  · simpa [a0Recipe0, phiQ_cast] using mem_ofRat (phiQ 0-399/500)
  · simpa [a0Recipe1, phiQ_cast] using mem_ofRat (phiQ (67/100)-399/500)

/-- The passed A0 endpoint recipe implies the exact full real statement. -/
theorem lemma_7_1_of_pass (h : a0Pass = true) : lemma_7_1 := by
  simp only [a0Pass, Bool.and_eq_true, decide_eq_true_eq] at h
  have h0 : 0 ≤ phi 0-399/500 := (toR_nonneg.mpr h.1).trans a0_recipe_mem.1.1
  have h1 : 0 ≤ phi (67/100)-399/500 := (toR_nonneg.mpr h.2).trans a0_recipe_mem.2.1
  refine ⟨by norm_num [phi], by linarith, ?_⟩
  intro s hs
  have hch := phi_ge_endpoint_chord hs.1 hs.2
  have hline : (399/500 : ℝ) ≤ (22/25 : ℝ)+(phi (67/100)-22/25)*s/(67/100) := by
    norm_num [phi]
    nlinarith [hs.1, hs.2]
  convert hline.trans hch using 1 <;> norm_num

theorem d0_recipe_mem (c : V22Class) :
    (d0Recipe c).Mem (-(psi c.thi+(c.b : ℝ)+(c.beta : ℝ)*((c.thi : ℝ)-1))) := by
  simpa [d0Recipe, d0Margin, psiQ_cast] using mem_ofRat (d0Margin c)

/-- A positive exact D0 recipe gives strict negativity at the class cutoff. -/
theorem d0_sound (c : V22Class) (h : d0Pass c = true) :
    psi c.thi+(c.b : ℝ)+(c.beta : ℝ)*((c.thi : ℝ)-1) < 0 := by
  have hh : 0 < (d0Recipe c).lo := by simpa [d0Pass] using h
  have hp := (toR_pos.mpr hh).trans_le (d0_recipe_mem c).1
  linarith

theorem lemma_7_16_of_pass (h : ∀ c ∈ classes, d0Pass c = true) : lemma_7_16 := by
  intro c hc
  exact d0_sound c (h c hc)

end Erdos993Lean.Analytic.V22
