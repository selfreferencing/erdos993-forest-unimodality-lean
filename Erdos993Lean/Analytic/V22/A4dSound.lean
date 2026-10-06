import Erdos993Lean.Analytic.V22.Compute.A4d
import Erdos993Lean.Analytic.V22.WindowExprsSound
import Erdos993Lean.Analytic.V22.Checks.EarlyStatements

/-! Real semantics and full statement consumption for A4d (Lemma 7.8).
No evaluation theorem is assumed here; D4 supplies the Boolean check. -/

namespace Erdos993Lean.Analytic.V22.Compute.A4d

@[simp] theorem evalR_yTilde (r N : Expr) (envR : Nat → ℝ) :
    (yTilde r N).evalR envR = V22.yTilde (r.evalR envR) (N.evalR envR) := by
  simp [yTilde, Expr.evalR, V22.yTilde]

@[simp] theorem evalR_lower (ra rb Na Nb : Expr) (envR : Nat → ℝ) :
    (lower ra rb Na Nb).evalR envR = V22.phiRBlockLower
      (ra.evalR envR) (rb.evalR envR) (Na.evalR envR) (Nb.evalR envR) := by
  norm_num [lower, Expr.evalR, V22.phiRBlockLower]

theorem passes_sound (b : Block) (h : passes b = true) :
    0 ≤ V22.phiRBlockLower (b.1 : ℝ) (b.2.1 : ℝ) (b.2.2.1 : ℝ) (b.2.2.2 : ℝ) := by
  have hm : ∀ i, (env i).Mem ((fun _ => (0 : ℝ)) i) := by
    intro i
    simpa [env] using TailCert.mem_ofRat (0 : Rat)
  have hh := (recipe b).nonnegativeOK_sound hm h
  simpa [recipe, Expr.evalR] using hh

theorem check_sound (h : check = true) : Checks.lemma_7_8 := by
  intro b hb
  have hmem : b ∈ blocks := by
    simpa only [blocks, Checks.phiRBlocks, Checks.phiRTailBlocks] using hb
  exact passes_sound b (List.all_eq_true.mp h b hmem)

end Erdos993Lean.Analytic.V22.Compute.A4d
