import Erdos993Lean.Analytic.V22.Analysis.InterfaceDefinitions
import Erdos993Lean.Analytic.V22.Analysis.E6ProfileDomains
import Erdos993Lean.Analytic.V22.Analysis.CentralWing
import Erdos993Lean.Analytic.V22.Analysis.OuterWindow

/-!
# Paper v2.2: the above-starting-mean interface for lane F

Source: Theorems 5.6 and 5.8 and Corollary 5.15 of the frozen v5 note.
The conclusion is exactly the native version 2.1 parameter consumer with
its band-rate premises removed and the Table 2 starting mean used.
The original activity, piece identity, mixture, zero first moment, second
moment, hand variance and all inherited MGF rows survive. The sole external
premise is the bundled lane D finite-check statement.
-/

namespace Erdos993Lean.Analytic.V22

open Erdos993Lean.Analytic N44
open Analysis

/-- Source above-mu_0 no-valley conclusion on every inherited activity
subinterval. Lane F discharges the single finite-certificate bundle. -/
theorem parameterNoValley_of_finiteChecks (hfin : FiniteChecks) :
    ParameterNoValley := by
  intro t ht mu hmu ι X k hprob hmean hzero hsecond hvariance hrows
  have hp : pieceOf t < 55 := (pieceOf_spec ht).1
  obtain ⟨hqa, hqb⟩ := e6_q_bounds ht
  obtain ⟨hsecondRow, hvarianceRow, hzeroRow⟩ :=
    e6_profile_inputs X ht hmu hsecond hvariance hrows
  have hsingle : ∀ row ∈
      ([(1 - actQ t, Real.exp (-Checks.rowEll0 (pieceOf t) * mu))] : List (ℝ × ℝ)),
      X.expect (fun M _ => row.1 ^ M) ≤ row.2 := by
    intro row hr
    simp only [List.mem_singleton] at hr
    subst row
    exact hzeroRow
  have hnv : NoValleyAtMGF2 (actQ t) mu
      ((pieceV22 (pieceOf t)).theta : ℝ) ((pieceV22 (pieceOf t)).D : ℝ)
      [(1 - actQ t, Real.exp (-Checks.rowEll0 (pieceOf t) * mu))] := by
    rcases e6_piece_partition hp with hc | hw | ho
    · exact source_central_noValley hfin hc.1 hc.2 hqa hqb hmu
    · exact source_wing_noValley hfin hw.1 hw.2 hqa hqb hmu
    · exact source_outer_noValley hfin hp ho hqa hqb hmu
  exact hnv ι X k hprob hmean hzero hsecondRow hvarianceRow hsingle

end Erdos993Lean.Analytic.V22
