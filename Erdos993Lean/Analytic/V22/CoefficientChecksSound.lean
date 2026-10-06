import Erdos993Lean.Analytic.V22.Compute.CoefficientChecks
import Erdos993Lean.Analytic.V22.EarlyCoefficientsSound
import Erdos993Lean.Analytic.V22.CappedCoefficientMonotone

/-! Checker success supplies only finite endpoint facts. The proved capped
coefficient transports then consume them to obtain exact statements 7.4–7.7.
Every physical outer spike-cell start is retained in A3′. -/

namespace Erdos993Lean.Analytic.V22.Compute.CoefficientChecks

open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute

noncomputable def closedRealEnv : Nat → ℝ := fun _ => 0

theorem closedEnv_mem : ∀ i, (closedEnv i).Mem (closedRealEnv i) := by
  intro i
  simpa [closedEnv, closedRealEnv] using mem_ofRat (0 : Rat)

theorem closedPositive_sound {e : Expr} (h : closedPositive e = true) :
    0 < e.evalR closedRealEnv := e.positiveOK_sound closedEnv_mem h

theorem closedNonnegative_sound {e : Expr} (h : closedNonnegative e = true) :
    0 ≤ e.evalR closedRealEnv := e.nonnegativeOK_sound closedEnv_mem h

theorem closedUpper_sound {e : Expr} {q : Rat} (h : closedUpper e q = true) :
    e.evalR closedRealEnv ≤ (q : ℝ) := e.upperOK_sound q closedEnv_mem h

theorem allClosedPositive_sound {es : List Expr} (h : allClosedPositive es = true) :
    ∀ e ∈ es, 0 < e.evalR closedRealEnv := by
  intro e he
  exact closedPositive_sound ((List.all_eq_true.mp h) e he)

theorem betaGuardsOK_sound {rm : Rat} {Nlo : Expr} (h : betaGuardsOK rm Nlo = true) :
    0 < (rm : ℝ) ∧ (rm : ℝ) ≤ 1/2 ∧ 1 < Nlo.evalR closedRealEnv ∧
      0 < rhoStar (Nlo.evalR closedRealEnv) (rm : ℝ) := by
  simp only [betaGuardsOK, Bool.and_eq_true] at h
  have hp := allClosedPositive_sound h.1
  have hr : 0 < (rm : ℝ) := by
    simpa [Expr.evalR] using hp (.rat rm) (by simp [betaGuards])
  have hrhi : (rm : ℝ) ≤ 1/2 := by
    simpa [Expr.evalR] using closedUpper_sound h.2
  have hn : 0 < Nlo.evalR closedRealEnv - 1 := by
    simpa [Expr.evalR] using hp (.sub Nlo (.rat 1)) (by simp [betaGuards])
  have hrs : 0 < rhoStar (Nlo.evalR closedRealEnv) (rm : ℝ) := by
    simpa [Expr.evalR] using hp (CoefficientExprs.rhoStar Nlo (.rat rm)) (by simp [betaGuards])
  exact ⟨hr, hrhi, by linarith, hrs⟩

/-- The tail branch is admitted only when a separate exact cap comparison
passes, never by dropping a negative derivative check. -/
theorem betaRangeOK_sound {rm : Rat} {Nlo : Expr} (h : betaRangeOK rm Nlo = true) :
    Checks.betaRange (rm : ℝ) (Nlo.evalR closedRealEnv) := by
  simp only [betaRangeOK, Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨hr, hrhi, hn, hrs⟩ := betaGuardsOK_sound h.1
  apply betaRange_of_endpoint hr hrhi hn hrs
  intro hbefore
  rcases h.2 with hmargin | htail
  · simpa [Expr.evalR] using closedPositive_sound hmargin
  · have hcap : 0 ≤ Nlo.evalR closedRealEnv - (6/(rm : ℝ))^2 := by
      simpa [Expr.evalR] using closedNonnegative_sound htail
    linarith

theorem a3OK_sound (h : a3OK = true) : Checks.lemma_7_4 := by
  simp only [a3OK, Bool.and_eq_true] at h
  have hg := betaGuardsOK_sound h.1
  have hrs : 0 < rhoStar (67/5) (1/4) := by
    simpa [Expr.evalR] using hg.2.2.2
  have hm : 0 ≤ Checks.betaDerivativeBound (1/4) (67/5) - 744/1000 := by
    simpa using closedNonnegative_sound h.2
  refine ⟨by linarith, ?_, ?_⟩
  · intro N hN
    have hmem : N ∈ Set.Icc (67/5 : ℝ) ((6/(1/4 : ℝ))^2) := by
      norm_num
      exact hN
    exact betaDerivativeOn_lower (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hmem hrs
  · convert cappedBeta_monotone_tail (rm := (1/4 : ℝ)) (N0 := (67/5 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hrs using 1 <;> norm_num

theorem spikeRmRat_cast (cell : V22SpikeCell) : (spikeRmRat cell : ℝ) = spikeRm cell := by
  cases hfind : classes.find? (fun c => c.classId == cell.classId) with
  | none => norm_num [spikeRmRat, spikeRm, spikeClass, hfind]
  | some c => simp [spikeRmRat, spikeRm, spikeClass, hfind]

theorem outerBetaOK_sound {cell : V22SpikeCell} (h : outerBetaOK cell = true)
    (houter : cell.classId ≠ 0) :
    Checks.betaRange (spikeRm cell) (16*(cell.ma : ℝ)+2) ∧
      (cell.classId = 1 → (6/spikeRm cell)^2+46/5 ≤ 16*(cell.ma : ℝ)+2) := by
  simp only [outerBetaOK, if_neg houter, Bool.and_eq_true] at h
  have hb := betaRangeOK_sound h.1
  refine ⟨?_, ?_⟩
  · simpa [outerStart, Expr.evalR, spikeRmRat_cast] using hb
  · intro hclass1
    have hc : (6 / spikeRmRat cell)^2 + 46/5 ≤ 16*cell.ma + 2 := by
      have hdec : decide ((6 / spikeRmRat cell)^2 + 46/5 ≤ 16*cell.ma + 2) = true := by
        simpa [hclass1] using h.2
      exact decide_eq_true_eq.mp hdec
    have hcast : (((6 / spikeRmRat cell)^2 + 46/5 : Rat) : ℝ) ≤
        ((16*cell.ma + 2 : Rat) : ℝ) := Rat.cast_le.mpr hc
    have hm : (6/(spikeRmRat cell : ℝ))^2+46/5 ≤ 16*(cell.ma : ℝ)+2 := by
      simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat] using hcast
    simpa only [spikeRmRat_cast] using hm

theorem a3PrimeOK_sound (h : a3PrimeOK = true) : Checks.lemma_7_5 := by
  simp only [a3PrimeOK, Bool.and_eq_true] at h
  have hw := List.all_eq_true.mp h.1.1.1
  have hw1 := betaRangeOK_sound (hw (741/10000,651/50) (by simp [EarlyCoefficients.a3WingPairs]))
  have hw2 := betaRangeOK_sound (hw (139/1250,13) (by simp [EarlyCoefficients.a3WingPairs]))
  have hw3 := betaRangeOK_sound (hw (1667/10000,388/25) (by simp [EarlyCoefficients.a3WingPairs]))
  have he19 := betaRangeOK_sound h.1.1.2
  have he30 := betaRangeOK_sound h.1.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Expr.evalR] using hw1
  · simpa [Expr.evalR] using hw2
  · simpa [Expr.evalR] using hw3
  · norm_num [Expr.evalR] at he19 ⊢
    exact he19
  · norm_num [Expr.evalR] at he30 ⊢
    exact he30
  · intro cell hcell houter
    exact outerBetaOK_sound ((List.all_eq_true.mp h.2) cell hcell) houter

@[simp] theorem evalR_bonusTail (env : Nat → ℝ) (rm N : Expr) :
    (bonusTail rm N).evalR env = Checks.bonusTail (rm.evalR env) (N.evalR env) := by
  norm_num [bonusTail, Expr.evalR, Checks.bonusTail]

@[simp] theorem evalR_bonusTailDerivative (env : Nat → ℝ) (rm N : Expr) :
    (bonusTailDerivative rm N).evalR env = V22.bonusTailDerivative (rm.evalR env) (N.evalR env) := by
  norm_num [bonusTailDerivative, Expr.evalR, V22.bonusTailDerivative]

@[simp] theorem evalR_bonusPreMargin (env : Nat → ℝ) (rm : Rat) (Nlo : Expr) :
    (bonusPreMargin rm Nlo).evalR env = rhoStar (Nlo.evalR env) (rm : ℝ)/2 -
      Checks.e2DerivativeBound (rm : ℝ) (Nlo.evalR env) := by
  simp [bonusPreMargin, Expr.evalR]

theorem bonusEndpointsOK_sound {rm : Rat} {Nlo : Expr} (h : bonusEndpointsOK rm Nlo = true) :
    Checks.bonusConditions (rm : ℝ) (Nlo.evalR closedRealEnv) := by
  simp only [bonusEndpointsOK, Bool.and_eq_true] at h
  have hp := allClosedPositive_sound h.1
  have hr : 0 < (rm : ℝ) := by
    simpa [Expr.evalR] using hp (.rat rm) (by simp [bonusEndpointExprs])
  have hrhi : (rm : ℝ) ≤ 1/2 := by
    simpa [Expr.evalR] using closedUpper_sound h.2
  have hn1 : 0 < Nlo.evalR closedRealEnv - 1 := by
    simpa [Expr.evalR] using hp (.sub Nlo (.rat 1)) (by simp [bonusEndpointExprs])
  have hn : 1 < Nlo.evalR closedRealEnv := by linarith
  have hrs : 0 < rhoStar (Nlo.evalR closedRealEnv) (rm : ℝ) := by
    simpa [Expr.evalR] using hp (CoefficientExprs.rhoStar Nlo (.rat rm)) (by simp [bonusEndpointExprs])
  have hcap1 : 0 < (6/(rm : ℝ))^2 - Nlo.evalR closedRealEnv := by
    simpa [Expr.evalR] using hp (.sub (EarlyCoefficients.capN (.rat rm)) Nlo) (by simp [bonusEndpointExprs])
  have hcap : Nlo.evalR closedRealEnv < (6/(rm : ℝ))^2 := by linarith
  have hf : 0 < lambdaBonusF (Nlo.evalR closedRealEnv) (rm : ℝ) := by
    simpa [Expr.evalR] using hp (CoefficientExprs.lambdaBonusF Nlo (.rat rm)) (by simp [bonusEndpointExprs])
  have hm : 0 < rhoStar (Nlo.evalR closedRealEnv) (rm : ℝ)/2 -
      Checks.e2DerivativeBound (rm : ℝ) (Nlo.evalR closedRealEnv) := by
    simpa using hp (bonusPreMargin rm Nlo) (by simp [bonusEndpointExprs])
  have ht : 0 < Checks.bonusTail (rm : ℝ) ((6/(rm : ℝ))^2) := by
    simpa [Expr.evalR] using hp (bonusTail (.rat rm) (EarlyCoefficients.capN (.rat rm))) (by simp [bonusEndpointExprs])
  have hd : 0 < V22.bonusTailDerivative (rm : ℝ) ((6/(rm : ℝ))^2) := by
    simpa [Expr.evalR] using hp (bonusTailDerivative (.rat rm) (EarlyCoefficients.capN (.rat rm))) (by simp [bonusEndpointExprs])
  have hdActual : 0 < deriv (Checks.bonusTail (rm : ℝ)) ((6/(rm : ℝ))^2) := by
    rw [(bonusTail_hasDerivAt (rm : ℝ) ((6/(rm : ℝ))^2)).deriv]
    exact hd
  exact bonusConditions_of_endpoints hr hrhi hn hcap hrs hf hm ht hdActual

theorem a4OK_sound (h : a4OK = true) : Checks.lemma_7_6 := by
  simpa [Checks.lemma_7_6, a4OK, Expr.evalR] using bonusEndpointsOK_sound h

theorem a4Pairs_eq : a4Pairs = Checks.bonusPairs := rfl

theorem a4PrimeOK_sound (h : a4PrimeOK = true) : Checks.lemma_7_7 := by
  intro p hp
  have hp' : p ∈ a4Pairs := by simpa only [a4Pairs_eq] using hp
  have hnum := (List.all_eq_true.mp h) p hp'
  simpa [Expr.evalR] using bonusEndpointsOK_sound hnum

theorem a3GroupCount_eq : a3GroupCount = 1 := rfl
theorem a3PrimeGroupCount_eq : a3PrimeGroupCount = 13 := by decide
theorem a3PrimePhysicalStartCount_eq : a3PrimePhysicalStartCount = 31 := by decide
theorem a4GroupCount_eq : a4GroupCount = 3 := rfl
theorem a4PrimeGroupCount_eq : a4PrimeGroupCount = 6 := by decide

end Erdos993Lean.Analytic.V22.Compute.CoefficientChecks
