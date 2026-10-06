import Erdos993Lean.Analytic.V22.Compute.WindowCellExprs
import Erdos993Lean.Analytic.V22.WindowExprsSound
import Erdos993Lean.Analytic.V22.Checks.LateStatements

/-!
# Soundness of the fixed-class D3 recipes

The fallback is bounded above by the actual fixed-class window lower recipe
without a sign or window-condition premise. Branch requirements retain the
positive, nonpositive and sign-crossing hypotheses of statement 7.20.
No numerical certificate is asserted here.
-/

namespace Erdos993Lean.Analytic.V22.Compute.WindowCellExprs

noncomputable section
attribute [local instance] Classical.propDecidable

variable (env : Nat → ℝ) (t r N : Expr)

@[simp] theorem evalR_GAt (arg : Expr) (lo hi : Rat) :
    (GAt arg lo hi).evalR env = V22.G (arg.evalR env) := by
  simp [GAt, Expr.evalR, V22.G]

@[simp] theorem evalR_yTilde :
    (yTilde r N).evalR env = V22.yTilde (r.evalR env) (N.evalR env) := by
  simp [yTilde, Expr.evalR, V22.yTilde]

@[simp] theorem evalR_epsilonPrime :
    (epsilonPrime r N).evalR env = V22.epsilonPrime (r.evalR env) (N.evalR env) := by
  simp [epsilonPrime, Expr.evalR, V22.epsilonPrime]

@[simp] theorem evalR_c0Prime :
    (c0Prime r N).evalR env = V22.c0Prime (r.evalR env) (N.evalR env) := by
  simp [c0Prime, Expr.evalR, V22.c0Prime]

@[simp] theorem evalR_rhoU :
    (rhoU r N).evalR env = V22.rhoU (r.evalR env) (N.evalR env) := by
  simp [rhoU, Expr.evalR, V22.rhoU]

@[simp] theorem evalR_eUDrop :
    (eUDrop r N).evalR env = V22.eU (r.evalR env) (N.evalR env) + V22.c0Prime (r.evalR env) (N.evalR env) := by
  simp [eUDrop, Expr.evalR, V22.eU]

@[simp] theorem evalR_eU : (eU r N).evalR env = V22.eU (r.evalR env) (N.evalR env) := by
  simp [eU, Expr.evalR]

@[simp] theorem evalR_Wlo (Dlo : Rat) : (Wlo Dlo).evalR env = min 3 (1 + (Dlo : ℝ)) := by
  simp [Wlo, Expr.evalR]

def qShiftReal (N0 t r : ℝ) : ℝ := V22.lambdaT t + V22.hbar (N0 - 2) + V22.windowEL r N0

@[simp] theorem evalR_qShift (N0 : Rat) :
    (qShift N0 t r).evalR env = qShiftReal N0 (t.evalR env) (r.evalR env) := by
  simp [qShift, Expr.evalR, qShiftReal]

@[simp] theorem evalR_ghat (N0 : Rat) (br : RootBrackets) :
    (ghat N0 t br).evalR env = V22.windowGhat (t.evalR env) (N0 : ℝ) := by
  simp [ghat, Expr.evalR, V22.windowGhat, V22.Ghat]

@[simp] theorem evalR_sbar (N0 : Rat) (br : RootBrackets) :
    (sbar N0 t r br).evalR env = V22.windowSbar (t.evalR env) (r.evalR env) (N0 : ℝ) := by
  simp [sbar, Expr.evalR]

def XsplitReal (Dlo N0 t r : ℝ) : ℝ :=
  1 - 2 / V22.rho N0 * V22.windowGhat t N0
    + Dlo / (1 + V22.windowSbar t r N0 + V22.windowRhoLbar r N0 * Dlo / 2)
    - 2 * V22.windowEL r N0 / V22.rho N0

@[simp] theorem evalR_Xsplit (Dlo N0 : Rat) (br : RootBrackets) :
    (Xsplit Dlo N0 t r br).evalR env = XsplitReal Dlo N0 (t.evalR env) (r.evalR env) := by
  simp [Xsplit, Expr.evalR, XsplitReal]

def logByRhoReal (N0 t r : ℝ) : ℝ := 1 - 2 * qShiftReal N0 t r / V22.rho N0
def logByRhoLbarReal (N0 t r : ℝ) : ℝ := 1 - 2 * qShiftReal N0 t r / V22.windowRhoLbar r N0

@[simp] theorem evalR_logByRho (N0 : Rat) :
    (logByRho N0 t r).evalR env = logByRhoReal N0 (t.evalR env) (r.evalR env) := by
  simp [logByRho, Expr.evalR, logByRhoReal]

@[simp] theorem evalR_logByRhoLbar (N0 : Rat) :
    (logByRhoLbar N0 t r).evalR env = logByRhoLbarReal N0 (t.evalR env) (r.evalR env) := by
  simp [logByRhoLbar, Expr.evalR, logByRhoLbarReal]

def fallbackLowerReal (Dlo N0 t r : ℝ) : ℝ :=
  min (min 3 (1 + Dlo)) (max (XsplitReal Dlo N0 t r)
    (min (logByRhoReal N0 t r) (logByRhoLbarReal N0 t r)))

@[simp] theorem evalR_fallbackLower (Dlo N0 : Rat) (br : RootBrackets) :
    (fallbackLower Dlo N0 t r br).evalR env = fallbackLowerReal Dlo N0 (t.evalR env) (r.evalR env) := by
  simp [fallbackLower, Expr.evalR, fallbackLowerReal]

def upperLambdaReal (N0 t r : ℝ) : ℝ :=
  V22.lambdaT t + (71/20) / (N0 + 1) + V22.rhoU r N0 * V22.Delta r N0 / 2
    - (V22.eU r N0 + V22.c0Prime r N0)

@[simp] theorem evalR_upperLambda (N0 : Rat) :
    (upperLambda N0 t r).evalR env = upperLambdaReal N0 (t.evalR env) (r.evalR env) := by
  norm_num [upperLambda, Expr.evalR, upperLambdaReal]

def upperRecipeReal (Dlo N0 rb t r : ℝ) : ℝ :=
  1 + Dlo - 2 / V22.rhoStar N0 rb * V22.G (min 0 (upperLambdaReal N0 t r))

@[simp] theorem evalR_upperRecipe (Dlo N0 rb : Rat) (br : RootBrackets) :
    (upperRecipe Dlo N0 rb t r br).evalR env = upperRecipeReal Dlo N0 rb (t.evalR env) (r.evalR env) := by
  simp [upperRecipe, Expr.evalR, upperRecipeReal]

@[simp] theorem evalR_lowerRecipe (Dlo N0 rb : Rat) (br : RootBrackets) :
    (lowerRecipe Dlo N0 rb t r br).evalR env =
      min (fallbackLowerReal Dlo N0 (t.evalR env) (r.evalR env))
        (min 3 (upperRecipeReal Dlo N0 rb (t.evalR env) (r.evalR env))) := by
  simp [lowerRecipe, Expr.evalR]

def conditionMarginReal (Dlo N0 t r : ℝ) : ℝ :=
  let lhs := qShiftReal N0 t r + V22.windowRhoLbar r N0
  if 2 ≤ Dlo then Real.log (1 + V22.rho N0 * (Dlo - 2) / 2) - lhs else -lhs

@[simp] theorem evalR_conditionMargin (Dlo N0 : Rat) :
    (conditionMargin Dlo N0 t r).evalR env = conditionMarginReal Dlo N0 (t.evalR env) (r.evalR env) := by
  by_cases h : (2 : Rat) ≤ Dlo
  · have hR : (2 : ℝ) ≤ (Dlo : ℝ) := by exact_mod_cast h
    simp [conditionMargin, h, Expr.evalR, conditionMarginReal, hR]
  · have hR : ¬(2 : ℝ) ≤ (Dlo : ℝ) := by exact_mod_cast h
    simp [conditionMargin, h, Expr.evalR, conditionMarginReal, hR]

@[simp] theorem evalR_licensedRecipe (Dlo N0 rb : Rat) (br : RootBrackets) :
    (licensedRecipe Dlo N0 rb t r br).evalR env =
      min (min 3 (1 + (Dlo : ℝ))) (min 3 (upperRecipeReal Dlo N0 rb (t.evalR env) (r.evalR env))) := by
  simp [licensedRecipe, Expr.evalR]

@[simp] theorem evalR_target (b beta : Rat) :
    (target b beta t).evalR env = V22.psi (t.evalR env) + (b : ℝ) + (beta : ℝ) * (t.evalR env - 1) := by
  norm_num [target, Expr.evalR, V22.psi]

@[simp] theorem evalR_positiveRequirement (b beta : Rat) :
    (positiveRequirement b beta t).evalR env =
      (V22.psi (t.evalR env) + (b : ℝ) + (beta : ℝ) * (t.evalR env - 1)) / t.evalR env := by
  simp [positiveRequirement, Expr.evalR]

@[simp] theorem evalR_negativeRequirement (N0 b beta : Rat) :
    (negativeRequirement N0 b beta t).evalR env =
      (V22.psi (t.evalR env) + (b : ℝ) + (beta : ℝ) * (t.evalR env - 1)) * ((N0 : ℝ) - 2) /
        (t.evalR env * (N0 : ℝ)) := by
  simp [negativeRequirement, Expr.evalR]

@[simp] theorem evalR_crossingRequirement (b beta : Rat) :
    (crossingRequirement b beta t).evalR env = max
      ((V22.psi (t.evalR env) + (b : ℝ) + (beta : ℝ) * (t.evalR env - 1)) / t.evalR env) 0 := by
  simp [crossingRequirement, Expr.evalR]

theorem cellStart_cast (c : V22Class) (cell : V22Cell) :
    (cellStart c cell : ℝ) = (c.muD : ℝ) * (cell.lo : ℝ) + 2 := by simp [cellStart]

theorem classDlo_cast (c : V22Class) (cell : V22Cell) :
    (classDlo c cell : ℝ) = V22.Delta c.ra (cellStart c cell : ℝ) := by
  simp [classDlo, V22.Delta]

theorem logFallback_le_windowLogAt (N0 t r : ℝ) :
    min (logByRhoReal N0 t r) (logByRhoLbarReal N0 t r) ≤ V22.windowLogAt t r N0 := by
  unfold V22.windowLogAt
  dsimp only
  split_ifs
  · exact min_le_left _ _
  · exact min_le_right _ _

theorem fallback_le_conditional (W X log1 log2 logActual : ℝ) (wc : Prop) [Decidable wc]
    (hlog : min log1 log2 ≤ logActual) :
    min W (max X (min log1 log2)) ≤ if wc then W else min W (max X logActual) := by
  by_cases h : wc
  · simp only [if_pos h]
    exact min_le_left _ _
  · simp only [if_neg h]
    exact min_le_min le_rfl (max_le_max le_rfl hlog)

theorem fallbackLowerReal_le_windowCellLower (c : V22Class) (cell : V22Cell) (t r : ℝ) :
    fallbackLowerReal (V22.Delta c.ra ((c.muD : ℝ) * (cell.lo : ℝ) + 2))
      ((c.muD : ℝ) * (cell.lo : ℝ) + 2) t r ≤ Checks.windowCellLower c cell t r := by
  unfold fallbackLowerReal Checks.windowCellLower XsplitReal
  dsimp only
  apply fallback_le_conditional
  exact logFallback_le_windowLogAt _ _ _

theorem classUpper_eq (c : V22Class) (cell : V22Cell) (br : RootBrackets) :
    (upperRecipe (classDlo c cell) (cellStart c cell) c.rb t r br).evalR env =
      Checks.windowCellUpper c cell (t.evalR env) (r.evalR env) := by
  simp [upperRecipeReal, upperLambdaReal, Checks.windowCellUpper, classDlo_cast, cellStart_cast]

/-- The conservative fallback never exceeds the source's exact cell minimum. -/
theorem classLowerRecipe_le (c : V22Class) (cell : V22Cell) (br : RootBrackets) :
    (classLowerRecipe c cell t r br).evalR env ≤
      Checks.windowCellMinimum c cell (t.evalR env) (r.evalR env) := by
  have hf : (fallbackLower (classDlo c cell) (cellStart c cell) t r br).evalR env ≤
      Checks.windowCellLower c cell (t.evalR env) (r.evalR env) := by
    simpa only [evalR_fallbackLower, classDlo_cast, cellStart_cast] using
      fallbackLowerReal_le_windowCellLower c cell (t.evalR env) (r.evalR env)
  have hu := classUpper_eq env t r c cell br
  change min ((fallbackLower (classDlo c cell) (cellStart c cell) t r br).evalR env)
    (min 3 ((upperRecipe (classDlo c cell) (cellStart c cell) c.rb t r br).evalR env)) ≤
      min (Checks.windowCellLower c cell (t.evalR env) (r.evalR env))
        (min 3 (Checks.windowCellUpper c cell (t.evalR env) (r.evalR env)))
  rw [hu]
  exact min_le_min hf le_rfl

theorem conditionMarginReal_nonneg_implies_condition (Dlo N0 t r : ℝ)
    (hm : 0 ≤ conditionMarginReal Dlo N0 t r) :
    if 2 ≤ Dlo then qShiftReal N0 t r + V22.windowRhoLbar r N0 ≤
      Real.log (1 + V22.rho N0 * (Dlo - 2) / 2)
    else qShiftReal N0 t r + V22.windowRhoLbar r N0 ≤ 0 := by
  by_cases h : 2 ≤ Dlo
  · simp only [conditionMarginReal, if_pos h] at hm
    simp only [if_pos h]
    linarith
  · simp only [conditionMarginReal, if_neg h] at hm
    simp only [if_neg h]
    linarith

/-- The independent condition margin licenses the stronger Wlo branch. -/
theorem classLicensedRecipe_eq (c : V22Class) (cell : V22Cell) (br : RootBrackets)
    (hm : 0 ≤ (classConditionMargin c cell t r).evalR env) :
    (classLicensedRecipe c cell t r br).evalR env =
      Checks.windowCellMinimum c cell (t.evalR env) (r.evalR env) := by
  have hmR : 0 ≤ conditionMarginReal
      (V22.Delta c.ra ((c.muD : ℝ) * (cell.lo : ℝ) + 2))
      ((c.muD : ℝ) * (cell.lo : ℝ) + 2) (t.evalR env) (r.evalR env) := by
    simpa only [classConditionMargin, evalR_conditionMargin, classDlo_cast, cellStart_cast] using hm
  have hwc := conditionMarginReal_nonneg_implies_condition _ _ _ _ hmR
  have hl : Checks.windowCellLower c cell (t.evalR env) (r.evalR env) =
      min 3 (1 + V22.Delta c.ra ((c.muD : ℝ) * (cell.lo : ℝ) + 2)) := by
    unfold Checks.windowCellLower
    dsimp only
    exact if_pos hwc
  have hu := classUpper_eq env t r c cell br
  change min ((Wlo (classDlo c cell)).evalR env)
      (min 3 ((upperRecipe (classDlo c cell) (cellStart c cell) c.rb t r br).evalR env)) =
    min (Checks.windowCellLower c cell (t.evalR env) (r.evalR env))
      (min 3 (Checks.windowCellUpper c cell (t.evalR env) (r.evalR env)))
  rw [hu, hl]
  simp only [evalR_Wlo, classDlo_cast, cellStart_cast]

/-- A passing positive-branch margin is consumed under its exact sign guard. -/
theorem positive_branch_of_margin (c : V22Class) (cell : V22Cell) (br : RootBrackets)
    (hm : 0 ≤ (positiveMargin c cell t r br).evalR env)
    (_hs : 0 < Checks.classTarget c (t.evalR env)) :
    Checks.classTarget c (t.evalR env) / t.evalR env ≤
      Checks.windowCellMinimum c cell (t.evalR env) (r.evalR env) := by
  have hreq : Checks.classTarget c (t.evalR env) / t.evalR env ≤
      (classLowerRecipe c cell t r br).evalR env := by
    simp only [positiveMargin, Expr.evalR, evalR_positiveRequirement] at hm
    unfold Checks.classTarget
    linarith
  exact hreq.trans (classLowerRecipe_le env t r c cell br)

/-- The nonpositive branch retains the exact maximum-B denominator. -/
theorem negative_branch_of_margin (c : V22Class) (cell : V22Cell) (br : RootBrackets)
    (hm : 0 ≤ (negativeMargin c cell t r br).evalR env)
    (_hs : Checks.classTarget c (t.evalR env) ≤ 0) :
    let N0 := (c.muD : ℝ) * (cell.lo : ℝ) + 2
    Checks.classTarget c (t.evalR env) * (N0 - 2) / (t.evalR env * N0) ≤
      Checks.windowCellMinimum c cell (t.evalR env) (r.evalR env) := by
  have hreq : Checks.classTarget c (t.evalR env) * ((cellStart c cell : ℝ) - 2) /
      (t.evalR env * (cellStart c cell : ℝ)) ≤ (classLowerRecipe c cell t r br).evalR env := by
    simp only [negativeMargin, Expr.evalR, evalR_negativeRequirement] at hm
    unfold Checks.classTarget
    linarith
  simpa only [cellStart_cast] using hreq.trans (classLowerRecipe_le env t r c cell br)

/-- A crossing cell requires the source's stronger maximum with zero. -/
theorem crossing_branch_of_margin (c : V22Class) (cell : V22Cell) (br : RootBrackets)
    (hm : 0 ≤ (crossingMargin c cell t r br).evalR env)
    (_hs : Checks.targetChangesSign c cell) :
    max (Checks.classTarget c (t.evalR env) / t.evalR env) 0 ≤
      Checks.windowCellMinimum c cell (t.evalR env) (r.evalR env) := by
  have hreq : max (Checks.classTarget c (t.evalR env) / t.evalR env) 0 ≤
      (classLowerRecipe c cell t r br).evalR env := by
    simp only [crossingMargin, Expr.evalR, evalR_crossingRequirement] at hm
    unfold Checks.classTarget
    linarith
  exact hreq.trans (classLowerRecipe_le env t r c cell br)

end

end Erdos993Lean.Analytic.V22.Compute.WindowCellExprs
