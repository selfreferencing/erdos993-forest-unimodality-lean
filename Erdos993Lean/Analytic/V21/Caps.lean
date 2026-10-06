import Erdos993Lean.Analytic.MGF.Sound

/-! Paper v2.1 Theorem 5.8(a,b): monotonicity in the checked moment caps.
Source: s5_part_b.tex, the cap comparisons in cases (a) and (b).
This uses the same mixture, integer rank and Laplace rows throughout. -/

namespace Erdos993Lean.Analytic.V21

/-- Source: Theorem 5.8, antitonicity of no-valley certificates in theta and D.
The nonnegative mean and binomial variance are explicit; no data are inferred. -/
theorem noValleyAtMGF2_mono {q m θ θ' D D' : ℝ} {rows : List (ℝ × ℝ)}
    (hm : 0 ≤ m) (hv : 0 ≤ q * (1 - q)) (hθ : θ ≤ θ') (hD : D ≤ D')
    (h : NoValleyAtMGF2 q m θ' D' rows) : NoValleyAtMGF2 q m θ D rows := by
  intro ι X k hP hmean hδ hδ2 hvar hLap
  apply h ι X k hP hmean hδ
  · exact hδ2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hθ hv) hm)
  · exact hvar.trans (mul_le_mul_of_nonneg_right hD hm)
  · exact hLap

end Erdos993Lean.Analytic.V21
