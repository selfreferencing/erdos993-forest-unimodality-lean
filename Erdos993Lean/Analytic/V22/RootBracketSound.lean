import Erdos993Lean.Analytic.V22.Functions

/-!
# Soundness of a retained local root bracket

Source: repaired note Lemmas 3.3 and 3.5, the root map of
`s + log(1+s) = λ` on `s > -1`.

These proofs require a concrete local bracket. They do not assume an inverse
function, a black-box root oracle, or global existence of roots. A finite
interval recipe must prove both endpoint inequalities before using the
enclosure theorem. No finite cell is evaluated by this module.
-/

namespace Erdos993Lean.Analytic.V22

noncomputable section

/-- The increasing equation whose local inverse is the note's root map. -/
def rootEquation (s : ℝ) : ℝ := s + Real.log (1 + s)

/-- On the retained domain, increasing the identity term already makes the
equation strictly increase; the logarithm term is nondecreasing. -/
theorem rootEquation_strictMonoOn : StrictMonoOn rootEquation (Set.Ioi (-1 : ℝ)) := by
  intro x hx y hy hxy
  have hxpos : 0 < 1 + x := by
    have hxdomain : (-1 : ℝ) < x := hx
    linarith
  have hlog : Real.log (1 + x) ≤ Real.log (1 + y) :=
    Real.log_le_log hxpos (by linarith)
  dsimp [rootEquation]
  linarith

/-- Continuity on any closed bracket which retains `s > -1`. -/
theorem rootEquation_continuousOn {a b : ℝ} (ha : -1 < a) :
    ContinuousOn rootEquation (Set.Icc a b) := by
  have harg : ContinuousOn (fun s : ℝ => 1 + s) (Set.Icc a b) :=
    continuousOn_const.add continuousOn_id
  have hlog : ContinuousOn (fun s : ℝ => Real.log (1 + s)) (Set.Icc a b) :=
    harg.log (by
      intro s hs
      have hslo : a ≤ s := hs.1
      have hspos : 0 < 1 + s := by linarith
      exact ne_of_gt hspos)
  exact continuousOn_id.add hlog

/-- A local bracket produces an actual solution in that same bracket by the
intermediate value theorem, retaining its domain and defining equation. -/
theorem root_exists_in_bracket {l a b : ℝ}
    (ha : -1 < a) (hab : a ≤ b)
    (hleft : a + Real.log (1 + a) ≤ l)
    (hright : l ≤ b + Real.log (1 + b)) :
    ∃ s : ℝ, s ∈ Set.Icc a b ∧ -1 < s ∧ rootEquation s = l := by
  have hlevel : l ∈ Set.Icc (rootEquation a) (rootEquation b) := ⟨hleft, hright⟩
  obtain ⟨s, hs, heq⟩ := intermediate_value_Icc hab (rootEquation_continuousOn ha) hlevel
  exact ⟨s, hs, ha.trans_le hs.1, heq⟩

/-- The choice definition retains the exact domain and equation whenever a
solution has been exhibited. This theorem introduces no root-existence axiom. -/
theorem rootMap_spec_of_exists {l : ℝ}
    (hex : ∃ s : ℝ, -1 < s ∧ rootEquation s = l) :
    -1 < rootMap l ∧ rootMap l + Real.log (1 + rootMap l) = l := by
  classical
  have hex' : ∃ s : ℝ, -1 < s ∧ s + Real.log (1 + s) = l := hex
  simp only [rootMap, dif_pos hex']
  exact Classical.choose_spec hex'

/-- Every solution on the retained domain is the chosen root, by uniqueness
of the strictly increasing root equation. -/
theorem rootMap_eq_of_solution {l s : ℝ}
    (hs : -1 < s) (heq : s + Real.log (1 + s) = l) : rootMap l = s := by
  have hroot := rootMap_spec_of_exists (l := l) ⟨s, hs, heq⟩
  apply rootEquation_strictMonoOn.injOn hroot.1 hs
  change rootMap l + Real.log (1 + rootMap l) = s + Real.log (1 + s)
  exact hroot.2.trans heq.symm

/-- A checked local bracket installs the domain and equation of the actual
chosen root. Both endpoint inequalities are required, even for a point bracket. -/
theorem rootMap_spec_of_bracket {l a b : ℝ}
    (ha : -1 < a) (hab : a ≤ b)
    (hleft : a + Real.log (1 + a) ≤ l)
    (hright : l ≤ b + Real.log (1 + b)) :
    -1 < rootMap l ∧ rootMap l + Real.log (1 + rootMap l) = l := by
  obtain ⟨s, _, hs, heq⟩ := root_exists_in_bracket ha hab hleft hright
  exact rootMap_spec_of_exists ⟨s, hs, heq⟩

/-- Soundness interface for the interval expression's certified root node:
the actual root lies between its retained real endpoints. -/
theorem rootMap_mem_bracket {l a b : ℝ}
    (ha : -1 < a) (hab : a ≤ b)
    (hleft : a + Real.log (1 + a) ≤ l)
    (hright : l ≤ b + Real.log (1 + b)) :
    a ≤ rootMap l ∧ rootMap l ≤ b := by
  obtain ⟨s, hs, hsdom, heq⟩ := root_exists_in_bracket ha hab hleft hright
  have hroot : rootMap l = s := rootMap_eq_of_solution hsdom heq
  simpa only [hroot] using hs

end

end Erdos993Lean.Analytic.V22
