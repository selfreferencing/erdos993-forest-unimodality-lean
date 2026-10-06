import Erdos993Lean.Analytic.Reserve.Defs

/-!
# The six segments of the hand variance proof

Source: `for_tong/TWIN_v1.8/apx_hand.tex`, Definition `mc:def:curve` and
Table `mc:tab:curve`, in `ProofRuns/2026-09-28_analytic_large_n/LEAN`.
These definitions retain the existing reserve and its actual forest mixture.
They do not assert the step comparisons or import the old certified bounds.
-/

namespace Erdos993Lean.Analytic.HandVariance

open Reserve

/-- Source: Table `mc:tab:curve`; each constructor names one closed segment. -/
inductive Segment where
  | lo | mid | u1 | u2 | u3 | u4
  deriving DecidableEq, Repr

/-- Source: Table `mc:tab:curve`, with fields `(lo, hi, D, aCoef, gDen)`. -/
def Segment.band : Segment → Band
  | .lo => ⟨1/3, 11/20, 6/5, 11/25, 21/2⟩
  | .mid => ⟨11/20, 263/200, 6/5, 23/50, 13⟩
  | .u1 => ⟨263/200, 3/2, 7/5, 9/20, 23/2⟩
  | .u2 => ⟨3/2, 7/4, 8/5, 47/100, 43/4⟩
  | .u3 => ⟨7/4, 2, 9/5, 1/2, 41/4⟩
  | .u4 => ⟨2, 7/3, 21/10, 57/100, 39/4⟩

/-- Source: Definition `mc:def:curve`. On the window this is the least cap of
a containing segment; the smaller cap applies at a common endpoint. -/
noncomputable def handCap (lam : ℝ) : ℝ :=
  if lam ≤ 263/200 then 6/5
  else if lam ≤ 3/2 then 7/5
  else if lam ≤ 7/4 then 8/5
  else if lam ≤ 2 then 9/5
  else 21/10

/-- Source: Definition `mc:def:curve`; all six multiplier choices satisfy
the unchanged side conditions of the reserve induction. -/
theorem segment_bandSide (s : Segment) : BandSide s.band := by
  cases s <;> norm_num [BandSide, Segment.band]

/-- Source: Table `mc:tab:curve`; the two lower segments share cap `6/5`. -/
theorem handCap_of_le {lam : ℝ} (h : lam ≤ 263/200) : handCap lam = 6/5 := by
  simp [handCap, h]

/-- Source: Table `mc:tab:curve`; the cap never exceeds `21/10`. -/
theorem handCap_le (lam : ℝ) : handCap lam ≤ 21/10 := by
  unfold handCap
  split_ifs <;> norm_num

/-- Source: Table `mc:tab:curve`; every cap is at least one. -/
theorem one_le_handCap (lam : ℝ) : 1 ≤ handCap lam := by
  unfold handCap
  split_ifs <;> norm_num

end Erdos993Lean.Analytic.HandVariance
