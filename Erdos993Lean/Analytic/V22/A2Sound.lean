import Erdos993Lean.Analytic.V22.RootShapeSound
import Erdos993Lean.Analytic.V22.SpikeLowerMonotone
import Erdos993Lean.Analytic.V22.EarlyCoefficientsSound
import Erdos993Lean.Analytic.V22.GridSound
import Erdos993Lean.Analytic.V22.Compute.A2Checks

/-!
# Conservative A2 recipe transport

The sigma and Ghat recipes remain upper bounds rather than identities with
the actual roots. Positive recipe denominators are transported to the actual
denominators, and their corresponding quotient remainders increase under the
recipe replacement. Numerical checks and exact partition coverage remain
separate inputs. No finite numerical pass is asserted here.
-/

namespace Erdos993Lean.Analytic.V22.A2Sound
open Checks Compute

noncomputable section

def sigmaBoundReal (s M : ℝ) : ℝ := positivePart (s+hbar M)
def ghatBoundReal (s M : ℝ) : ℝ :=
  max (s^2/(1+s)) ((positivePart (s+Real.log (1+s)+hbar M))^2/4)

def dLRecipeReal (s N M rm nm : ℝ) : ℝ :=
  (sigmaBoundReal s M*alpha1 N rm)^2 /
    EarlyCoefficients.betaLRecipeReal s N M rm nm

def upperDenRecipeReal (s N M rm : ℝ) : ℝ :=
  N-1-kappaA N rm*ghatBoundReal s M/rhoStar N rm

def dURecipeReal (s N M rm nm : ℝ) : ℝ :=
  4*(ghatBoundReal s M)^2/((rhoStar N rm)^2*upperDenRecipeReal s N M rm)
    + positivePart (-(s/(1+s)))*4/((rhoStar N rm)^2*betaE N rm nm)

def templateBaseReal (s M k : ℝ) : ℝ :=
  2-6*(s^2/(1+s))-2*k*(s/(1+s))-k^2*(1/((1+s)*(2+s)))/(M+3)

def envelopeRecipeReal (sa : Rat) (s M k : ℝ) : ℝ :=
  let N := M+2
  let nm := (1/4)*Real.sqrt N
  let base := templateBaseReal s M k
  let base := if 0 ≤ sa then base+M*s^2*phi s else base
  let dl := dLRecipeReal s N M (1/4) nm
  base-(if sa < 0 then max dl (dURecipeReal s N M (1/4) nm) else dl)

theorem sigmaBound_upper {s M : ℝ} (hs : -1 < s) (hM : 0 < M) :
    sigma0 (tOfS s) M ≤ sigmaBoundReal s M := sigma0_tOfS_upper hs hM

theorem ghatBound_upper {s M : ℝ} (hs : -1 < s) (hM : 0 < M) :
    Ghat (tOfS s) M ≤ ghatBoundReal s M := by
  have h := Ghat_quadratic_upper (tOfS s) hM
  have hbase : G (lambdaT (tOfS s)) = s^2/(1+s) := by
    simp only [G, rootMap_lambdaT_tOfS hs]
  rw [hbase] at h
  simpa only [lambdaT_tOfS hs, ghatBoundReal] using h

theorem betaLRecipe_le_actual {s N M rm nm : ℝ}
    (hs : -1 < s) (hM : 0 < M) (hN : 10 ≤ N)
    (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) :
    EarlyCoefficients.betaLRecipeReal s N M rm nm ≤ betaL (tOfS s) N M rm nm := by
  have hsigma := sigmaBound_upper hs hM
  have ha2 := alpha2_nonneg hN hrm hrmhi
  have hterm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsigma (by norm_num : (0:ℝ) ≤ 2)) ha2
  dsimp [EarlyCoefficients.betaLRecipeReal, betaL, sigmaBoundReal] at *
  linarith

theorem dLbar_le_recipe {s N M rm nm : ℝ}
    (hs : -1 < s) (hM : 0 < M) (hN : 10 ≤ N)
    (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2)
    (hden : 0 < EarlyCoefficients.betaLRecipeReal s N M rm nm) :
    dLbar (tOfS s) N M rm nm ≤ dLRecipeReal s N M rm nm := by
  have hdenorder := betaLRecipe_le_actual (nm := nm) hs hM hN hrm hrmhi
  have hsigma := sigmaBound_upper hs hM
  have ha1 := alpha1_nonneg hN hrm hrmhi
  have hsigmanonneg : 0 ≤ sigma0 (tOfS s) M := le_max_right _ _
  have hboundnonneg : 0 ≤ sigmaBoundReal s M := le_max_right _ _
  have hprod := mul_le_mul_of_nonneg_right hsigma ha1
  have hsquare := (sq_le_sq₀ (mul_nonneg hsigmanonneg ha1)
    (mul_nonneg hboundnonneg ha1)).mpr hprod
  exact nonneg_quotient_antitone hsquare (sq_nonneg _) hden hdenorder

theorem kappaA_nonneg {N rm : ℝ} (hN : 10 ≤ N) (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) :
    0 ≤ kappaA N rm := by
  have hd := spike_activity_den_pos hrm hrmhi
  have hn : 0 < N := by linarith
  have hn1 : 0 < N+1 := by linarith
  have hc : 0 < cCoef N := by
    have hrecip : (1:ℝ)/N < 1 := (div_lt_one hn).mpr (by linarith)
    dsimp [cCoef]
    linarith
  have hs : 0 < Real.sqrt (cCoef N) := Real.sqrt_pos.mpr hc
  dsimp [kappaA]
  positivity

theorem upperDenRecipe_le_actual {s N M rm : ℝ}
    (hs : -1 < s) (hM : 0 < M) (hN : 10 ≤ N)
    (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) (hrs : 0 < rhoStar N rm) :
    upperDenRecipeReal s N M rm ≤
      N-1-kappaA N rm*Ghat (tOfS s) M/rhoStar N rm := by
  have hgh := ghatBound_upper hs hM
  have hk := kappaA_nonneg hN hrm hrmhi
  have hterm := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hgh hk) hrs.le
  dsimp [upperDenRecipeReal]
  linarith

theorem dURecipeReal_nonneg {s N M rm nm : ℝ}
    (hrs : 0 < rhoStar N rm) (hden : 0 < upperDenRecipeReal s N M rm)
    (hbeta : 0 < betaE N rm nm) : 0 ≤ dURecipeReal s N M rm nm := by
  have hpart : 0 ≤ positivePart (-(s/(1+s))) := le_max_right _ _
  dsimp [dURecipeReal]
  positivity

theorem dUbar_le_recipe {s N M rm nm : ℝ}
    (hs : -1 < s) (hsnonpos : s ≤ 0) (hM : 0 < M) (hN : 10 ≤ N)
    (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) (hrs : 0 < rhoStar N rm)
    (hden : 0 < upperDenRecipeReal s N M rm) :
    dUbar (tOfS s) N M rm nm ≤ dURecipeReal s N M rm nm := by
  have hdenorder := upperDenRecipe_le_actual hs hM hN hrm hrmhi hrs
  have hgh := ghatBound_upper hs hM
  have hghnonneg : 0 ≤ Ghat (tOfS s) M := (G_nonneg _).trans (le_max_left _ _)
  have hboundnonneg := hghnonneg.trans hgh
  have hghsq := (sq_le_sq₀ hghnonneg hboundnonneg).mpr hgh
  have hfirst := nonneg_quotient_antitone
    (mul_le_mul_of_nonneg_left hghsq (by norm_num : (0:ℝ) ≤ 4))
    (by positivity : 0 ≤ 4*(ghatBoundReal s M)^2)
    (mul_pos (sq_pos_of_pos hrs) hden)
    (mul_le_mul_of_nonneg_left hdenorder (sq_nonneg (rhoStar N rm)))
  have hsden : 0 < 1+s := by linarith
  have hg1 : G1 (lambdaT (tOfS s))=s/(1+s) := by
    simp only [G1, rootMap_lambdaT_tOfS hs]
  have hfrac : s/(1+s) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hsnonpos hsden.le
  have habs : |G1 (lambdaT (tOfS s))|=positivePart (-(s/(1+s))) := by
    rw [hg1, abs_of_nonpos hfrac]
    exact (max_eq_left (neg_nonneg.mpr hfrac)).symm
  dsimp [dUbar, dURecipeReal]
  rw [habs]
  exact add_le_add hfirst (le_refl _)

@[simp] theorem evalR_dURecipe (env : Nat → ℝ) (s N M rm nm : Expr) :
    (EarlyCoefficients.dURecipe s N M rm nm).evalR env =
      dURecipeReal (s.evalR env) (N.evalR env) (M.evalR env) (rm.evalR env) (nm.evalR env) := by
  simp [EarlyCoefficients.dURecipe, EarlyCoefficients.upperDenominator, Expr.evalR,
    dURecipeReal, upperDenRecipeReal, ghatBoundReal]

@[simp] theorem evalR_upperDenominator (env : Nat → ℝ) (s N M rm : Expr) :
    (EarlyCoefficients.upperDenominator s N M rm).evalR env =
      upperDenRecipeReal (s.evalR env) (N.evalR env) (M.evalR env) (rm.evalR env) := by
  simp [EarlyCoefficients.upperDenominator, Expr.evalR, upperDenRecipeReal, ghatBoundReal]

@[simp] theorem evalR_dLRecipeReal (env : Nat → ℝ) (s N M rm nm : Expr) :
    (EarlyCoefficients.dLRecipe s N M rm nm).evalR env =
      dLRecipeReal (s.evalR env) (N.evalR env) (M.evalR env) (rm.evalR env) (nm.evalR env) := by
  simp [dLRecipeReal, sigmaBoundReal]

@[simp] theorem evalR_templateBase (env : Nat → ℝ) (s M k : Expr) :
    (EarlyCoefficients.templateBase s M k).evalR env =
      templateBaseReal (s.evalR env) (M.evalR env) (k.evalR env) := by
  simp [EarlyCoefficients.templateBase, Expr.evalR, templateBaseReal]

@[simp] theorem evalR_a2Envelope (env : Nat → ℝ) (sa : Rat) (s M k : Expr) :
    (EarlyCoefficients.a2Envelope sa s M (Expr.rat (1/4)) k).evalR env =
      envelopeRecipeReal sa (s.evalR env) (M.evalR env) (k.evalR env) := by
  by_cases hpos : 0 ≤ sa <;> by_cases hneg : sa < 0 <;>
    norm_num [EarlyCoefficients.a2Envelope, hpos, hneg, Expr.evalR, envelopeRecipeReal,
      dLRecipeReal, sigmaBoundReal]

/-- The nominal sign selects a conservative recipe on its whole closed
cell. A negative cell may include `s=0`; the extra upper remainder is then
harmless and the Gaussian term is exactly zero. -/
theorem envelopeRecipe_le_actual {sa : Rat} {s M k : ℝ}
    (hs : -1 < s) (hM : 0 < M) (hN : 10 ≤ M+2)
    (hclasspos : 0 ≤ sa → 0 ≤ s) (hclassneg : sa < 0 → s ≤ 0)
    (hL : 0 < EarlyCoefficients.betaLRecipeReal s (M+2) M (1/4) ((1/4)*Real.sqrt (M+2)))
    (hU : sa < 0 →
      0 < rhoStar (M+2) (1/4) ∧ 0 < betaE (M+2) (1/4) ((1/4)*Real.sqrt (M+2)) ∧
      0 < upperDenRecipeReal s (M+2) M (1/4)) :
    envelopeRecipeReal sa s M k ≤ envelopeExpression s M k := by
  have hLorder := betaLRecipe_le_actual (nm := (1/4)*Real.sqrt (M+2))
    hs hM hN (by norm_num : (0:ℝ) ≤ 1/4)
    (by norm_num : (1/4:ℝ) ≤ 1/2)
  have hLactual := hL.trans_le hLorder
  have hDl := dLbar_le_recipe hs hM hN (by norm_num : (0:ℝ) ≤ 1/4)
    (by norm_num : (1/4:ℝ) ≤ 1/2) hL
  have hDlnonneg : 0 ≤ dLbar (tOfS s) (M+2) M (1/4) ((1/4)*Real.sqrt (M+2)) :=
    div_nonneg (sq_nonneg _) hLactual.le
  have hrem :
      max (dLbar (tOfS s) (M+2) M (1/4) ((1/4)*Real.sqrt (M+2)))
        (if s < 0 then dUbar (tOfS s) (M+2) M (1/4) ((1/4)*Real.sqrt (M+2)) else 0) ≤
      (if sa < 0 then
        max (dLRecipeReal s (M+2) M (1/4) ((1/4)*Real.sqrt (M+2)))
          (dURecipeReal s (M+2) M (1/4) ((1/4)*Real.sqrt (M+2)))
        else dLRecipeReal s (M+2) M (1/4) ((1/4)*Real.sqrt (M+2))) := by
    by_cases hsa : sa < 0
    · rw [if_pos hsa]
      have hu := hU hsa
      have hif : (if s < 0 then dUbar (tOfS s) (M+2) M (1/4) ((1/4)*Real.sqrt (M+2)) else 0) ≤
          dURecipeReal s (M+2) M (1/4) ((1/4)*Real.sqrt (M+2)) := by
        by_cases hsn : s < 0
        · rw [if_pos hsn]
          exact dUbar_le_recipe hs (hclassneg hsa) hM hN (by norm_num) (by norm_num) hu.1 hu.2.2
        · rw [if_neg hsn]
          exact dURecipeReal_nonneg hu.1 hu.2.2 hu.2.1
      exact max_le_max hDl hif
    · have hspos := hclasspos (le_of_not_gt hsa)
      rw [if_neg hsa, if_neg (not_lt.mpr hspos), max_eq_left hDlnonneg]
      exact hDl
  have hgauss :
      (if 0 ≤ sa then M*s^2*phi s else 0)=(if 0 ≤ s then M*s^2*phi s else 0) := by
    by_cases hsa : 0 ≤ sa
    · simp only [if_pos hsa, if_pos (hclasspos hsa)]
    · have hsnonpos := hclassneg (lt_of_not_ge hsa)
      by_cases hspos : 0 ≤ s
      · have hs0 : s=0 := by linarith
        simp [hsa, hs0]
      · simp only [if_neg hsa, if_neg hspos]
  have hcmp := sub_le_sub_left hrem
    ((if 0 ≤ s then M*s^2*phi s else 0)+templateBaseReal s M k)
  convert hcmp using 1
  · dsimp [envelopeRecipeReal]
    by_cases hsa : 0 ≤ sa
    · simp only [if_pos hsa]
      have hg := hgauss
      simp only [if_pos hsa] at hg
      rw [← hg]
      ring
    · simp only [if_neg hsa]
      have hg := hgauss
      simp only [if_neg hsa] at hg
      rw [← hg]
      ring
  · dsimp [envelopeExpression, templateBaseReal]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

/-- A passing exact partition of one nominal cell supplies its complete
source statement, with actual roots and both template endpoint values. -/
theorem cellPasses_sound {c : Span} {pieces : List Span}
    (hpass : A2Checks.cellPasses c pieces=true) {s : ℝ} (hs : inCell c.1 c.2 s) :
    let M := 19*tOfS c.1
    let N := M+2
    let nm := (1/4)*Real.sqrt N
    let t := tOfS s
    0 < betaL t N M (1/4) nm ∧ ebar N (1/4) nm < 1 ∧
      (s < 0 → 0 < rhoStar N (1/4) ∧ 0 < betaE N (1/4) nm ∧
        0 < N-1-kappaA N (1/4)*Ghat t M/rhoStar N (1/4)) ∧
      Ghat t M ≤ max (G (lambdaT t)) ((positivePart (lambdaT t+hbar M))^2/4) ∧
      sigma0 t M ≤ positivePart (s+hbar M) ∧
      ∀ k ∈ ([71/20,kbar M] : List ℝ), 0 ≤ envelopeExpression s M k := by
  let sexpr := Expr.var 0
  let mexpr := EarlyCoefficients.a2M0 19 (Expr.rat c.1)
  let nexpr := EarlyCoefficients.a2N0 mexpr
  let nmexpr := EarlyCoefficients.a2NuMax nexpr (Expr.rat (1/4))
  let M : ℝ := 19*tOfS c.1
  let N : ℝ := M+2
  let nm : ℝ := (1/4)*Real.sqrt N
  have hfields :
      ((-1:Rat)<c.1 ∧ c.1 ≤ c.2 ∧ (0 ≤ c.1 ∨ c.2 ≤ 0)) ∧
      partitionFrom c.1 c.2 pieces=true ∧ positiveOn mexpr pieces=true ∧
      nonnegativeOn (Expr.sub nexpr (Expr.rat 10)) pieces=true ∧
      (EarlyCoefficients.a2CoefficientConditions c.1 sexpr mexpr (Expr.rat (1/4))).all
        (fun e => positiveOn e pieces)=true ∧
      nonnegativeOn (EarlyCoefficients.a2EndpointRecipes c.1 sexpr mexpr (Expr.rat (1/4))).1 pieces=true ∧
      nonnegativeOn (EarlyCoefficients.a2EndpointRecipes c.1 sexpr mexpr (Expr.rat (1/4))).2 pieces=true := by
    simpa only [A2Checks.cellPasses, sexpr, mexpr, nexpr, Bool.and_eq_true,
      decide_eq_true_eq, and_assoc] using hpass
  rcases hfields with ⟨hguard,hcover,hMpass,hNpass,hconds,hleft,hright⟩
  have hlo : (-1:ℝ)<(c.1:ℝ) := by exact_mod_cast hguard.1
  have hsroot : -1<s := hlo.trans_le hs.1
  have hM : 0 < M := by
    have h := positiveOn_sound hcover hMpass hs
    simpa [mexpr, M, realSpanEnv, Expr.evalR] using h
  have hN : 10 ≤ N := by
    have h := nonnegativeOn_sound hcover hNpass hs
    have hh : 0 ≤ N-10 := by simpa [nexpr, mexpr, N, M, realSpanEnv, Expr.evalR] using h
    linarith
  have hcondition : ∀ e ∈ EarlyCoefficients.a2CoefficientConditions c.1 sexpr mexpr (Expr.rat (1/4)),
      0 < e.evalR (realSpanEnv s) := by
    intro e he
    exact positiveOn_sound hcover ((List.all_eq_true.mp hconds) e he) hs
  have hL : 0 < EarlyCoefficients.betaLRecipeReal s N M (1/4) nm := by
    have h := hcondition (EarlyCoefficients.betaLRecipe sexpr nexpr mexpr (Expr.rat (1/4)) nmexpr)
      (by simp [EarlyCoefficients.a2CoefficientConditions, nexpr, nmexpr])
    simpa [sexpr,nexpr,mexpr,nmexpr,N,M,nm,realSpanEnv,Expr.evalR] using h
  have hebar : ebar N (1/4) nm < 1 := by
    have h := hcondition (Expr.sub (Expr.rat 1) (CoefficientExprs.ebar nexpr (Expr.rat (1/4)) nmexpr))
      (by simp [EarlyCoefficients.a2CoefficientConditions,nexpr,nmexpr])
    have hh : 0 < 1-ebar N (1/4) nm := by
      simpa [sexpr,nexpr,mexpr,nmexpr,N,M,nm,realSpanEnv,Expr.evalR] using h
    linarith
  have hU : c.1 < 0 → 0 < rhoStar N (1/4) ∧ 0 < betaE N (1/4) nm ∧
      0 < upperDenRecipeReal s N M (1/4) := by
    intro hsa
    have hr := hcondition (CoefficientExprs.rhoStar nexpr (Expr.rat (1/4)))
      (by simp [EarlyCoefficients.a2CoefficientConditions,nexpr,nmexpr,hsa])
    have hb := hcondition (CoefficientExprs.betaE nexpr (Expr.rat (1/4)) nmexpr)
      (by simp [EarlyCoefficients.a2CoefficientConditions,nexpr,nmexpr,hsa])
    have hd := hcondition (EarlyCoefficients.upperDenominator sexpr nexpr mexpr (Expr.rat (1/4)))
      (by simp [EarlyCoefficients.a2CoefficientConditions,nexpr,nmexpr,hsa])
    constructor
    · simpa [sexpr,nexpr,mexpr,nmexpr,N,M,nm,realSpanEnv,Expr.evalR] using hr
    constructor
    · simpa [sexpr,nexpr,mexpr,nmexpr,N,M,nm,realSpanEnv,Expr.evalR] using hb
    · simpa [sexpr,nexpr,mexpr,nmexpr,N,M,nm,realSpanEnv,Expr.evalR] using hd
  have hclasspos : 0 ≤ c.1 → 0 ≤ s := by
    intro hsa
    have hlo0 : (0:ℝ) ≤ (c.1:ℝ) := by exact_mod_cast hsa
    exact hlo0.trans hs.1
  have hclassneg : c.1 < 0 → s ≤ 0 := by
    intro hsa
    rcases hguard.2.2 with hcontra | hhi
    · exact False.elim (not_lt_of_ge hcontra hsa)
    · have hhireal : (c.2:ℝ) ≤ (0:ℝ) := by exact_mod_cast hhi
      exact hs.2.trans hhireal
  have hLactual := hL.trans_le (betaLRecipe_le_actual hsroot hM hN (by norm_num) (by norm_num))
  refine ⟨hLactual,hebar,?_,Ghat_quadratic_upper (tOfS s) hM,sigma0_tOfS_upper hsroot hM,?_⟩
  · intro hsneg
    have hsa : c.1 < 0 := by
      have hreal : (c.1:ℝ)<0 := hs.1.trans_lt hsneg
      exact_mod_cast hreal
    have hu := hU hsa
    exact ⟨hu.1,hu.2.1,hu.2.2.trans_le
      (upperDenRecipe_le_actual hsroot hM hN (by norm_num) (by norm_num) hu.1)⟩
  · intro k hk
    have hleftreal : 0 ≤ envelopeRecipeReal c.1 s M (71/20) := by
      have h := nonnegativeOn_sound hcover hleft hs
      norm_num [EarlyCoefficients.a2EndpointRecipes,sexpr,mexpr,M,realSpanEnv,Expr.evalR] at h
      exact h
    have hrightreal : 0 ≤ envelopeRecipeReal c.1 s M (kbar M) := by
      have h := nonnegativeOn_sound hcover hright hs
      norm_num [EarlyCoefficients.a2EndpointRecipes,sexpr,mexpr,M,realSpanEnv,Expr.evalR] at h
      exact h
    have hactual := envelopeRecipe_le_actual (k := k) hsroot hM hN hclasspos hclassneg hL hU
    simp at hk
    rcases hk with hkeq | hkeq
    · subst k
      exact hleftreal.trans hactual
    · subst k
      exact hrightreal.trans hactual

/-- The complete exact nine-cell A2 statement consumes the finite checker. -/
theorem check_sound {parts : Span → List Span} (hcheck : A2Checks.check parts=true) :
    Checks.lemma_7_3 := by
  intro c hc s hs
  have hp := (List.all_eq_true.mp hcheck) c hc
  exact cellPasses_sound hp hs

end
end Erdos993Lean.Analytic.V22.A2Sound
