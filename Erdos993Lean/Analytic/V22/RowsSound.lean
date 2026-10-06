import Erdos993Lean.Analytic.V22.Compute.Rows
import Erdos993Lean.Analytic.V22.ExprSound
import Erdos993Lean.Analytic.V22.GridSound
import Erdos993Lean.Analytic.V22.Checks.LateStatements
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Row-recipe semantics and retained branch guards

Pi is enclosed using proved rational bounds. The exact inherited rows and
class lookup are preserved. The semantic identities below concern the actual
prices and margins, rather than the rounded values in the source log.
No finite-check certificate or row positivity is assumed here.
-/

namespace Erdos993Lean.Analytic.V22.RowsSound

open Erdos993Lean.Analytic.TailCert
open Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.V22.Compute
open Erdos993Lean.Analytic.V22.Compute.Rows

noncomputable section
attribute [local instance] Classical.propDecidable

def realEnv : Nat → ℝ := realSpanEnv Real.pi

theorem env_mem : ∀ i, (env i).Mem (realEnv i) := by
  apply spanEnv_mem
  constructor
  · convert Real.pi_gt_d20.le using 1 <;> norm_num [piSpan]
  · convert Real.pi_lt_d20.le using 1 <;> norm_num [piSpan]

@[simp] theorem classQ_eq (p : Nat) : classQ p = classForPiece p := rfl
@[simp] theorem wingQ_eq (p : Nat) : wingQ p = wingForPiece p := rfl

@[simp] theorem meanQ_meaning (p : Nat) : (meanQ p : ℝ) = startingMean p := rfl

@[simp] theorem excessQ_meaning (p : Nat) : (excessQ p : ℝ) = excess p := by
  cases h : classForPiece p <;> simp [excessQ, excess, classQ_eq, h]

@[simp] theorem cutoffQ_meaning (p : Nat) : (cutoffQ p : ℝ) = spikeCutoff p := by
  cases h : classForPiece p with
  | none => cases hw : wingForPiece p <;> simp [cutoffQ, spikeCutoff, classQ_eq, wingQ_eq, h, hw]
  | some c => simp [cutoffQ, spikeCutoff, classQ_eq, h]

@[simp] theorem qaQ_meaning (p : Nat) : (qaQ p : ℝ) = Checks.rowQa p := by
  simp [qaQ, Checks.rowQa, pieceQ, pieceV22]

@[simp] theorem qbQ_meaning (p : Nat) : (qbQ p : ℝ) = Checks.rowQb p := by
  simp [qbQ, Checks.rowQb, pieceQ, pieceV22]

@[simp] theorem ellQ_meaning (p : Nat) : (ellQ p : ℝ) = Checks.rowEll0 p := rfl

@[simp] theorem vminQ_meaning (p : Nat) : (vminQ p : ℝ) = Checks.rowVmin p := by
  simp [vminQ, Checks.rowVmin, Rat.cast_min]

@[simp] theorem rhiQ_meaning (p : Nat) : (rhiQ p : ℝ) = Checks.rowRhi p := by
  simp [rhiQ, absQ, Checks.rowRhi, Rat.cast_max, abs_eq_max_neg]

theorem usesCell_iff (p : Nat) (cell : V22SpikeCell) :
    usesCell p cell = true ↔ Checks.rowUsesCell p cell := by
  cases h : classForPiece p with
  | some c =>
    simp only [usesCell, classQ_eq, h, Checks.rowUsesCell, decide_eq_true_eq]
  | none =>
    simp only [usesCell, classQ_eq, h, Checks.rowUsesCell, decide_eq_true_eq]
    constructor
    · rintro ⟨hclass, hcutoff⟩
      refine ⟨hclass, ?_⟩
      rw [← cutoffQ_meaning p]
      exact_mod_cast hcutoff
    · rintro ⟨hclass, hcutoff⟩
      refine ⟨hclass, ?_⟩
      rw [← cutoffQ_meaning p] at hcutoff
      exact_mod_cast hcutoff

@[simp] theorem gaussianE_meaning : gaussianE.evalR realEnv = gaussianAmplitude := by
  norm_num [gaussianE, Expr.evalR, realEnv, realSpanEnv, gaussianAmplitude]

@[simp] theorem meanE_meaning (p : Nat) : (meanE p).evalR realEnv = startingMean p := by
  simp [meanE, Expr.evalR]

@[simp] theorem excessE_meaning (p : Nat) : (excessE p).evalR realEnv = excess p := by
  simp [excessE, Expr.evalR]

@[simp] theorem ellE_meaning (p : Nat) : (ellE p).evalR realEnv = Checks.rowEll0 p := by
  simp [ellE, Expr.evalR]

@[simp] theorem vminE_meaning (p : Nat) : (vminE p).evalR realEnv = Checks.rowVmin p := by
  simp [vminE, Expr.evalR]

@[simp] theorem rhiE_meaning (p : Nat) : (rhiE p).evalR realEnv = Checks.rowRhi p := by
  simp [rhiE, Expr.evalR]

@[simp] theorem lbE_meaning (p : Nat) : (lbE p).evalR realEnv = Checks.rowLb p := by
  simp [lbE, Expr.evalR, Checks.rowLb]

@[simp] theorem psiE_meaning (t : Expr) : (psiE t).evalR realEnv = psi (t.evalR realEnv) := by
  simp [psiE, Expr.evalR, psi]

@[simp] theorem AE_meaning (p M : Nat) : (AE p M).evalR realEnv = Checks.rowA p M := by
  simp [AE, Expr.evalR, Checks.rowA, Checks.smallFiberK]

@[simp] theorem smallAmplitudeE_meaning (p M : Nat) :
    (smallAmplitudeE p M).evalR realEnv =
      Checks.rowA p M * Real.rpow (startingMean p) (3 / 2) := by
  simp [smallAmplitudeE, Expr.evalR]

@[simp] theorem smallBaseE_meaning (p M : Nat) :
    (smallBaseE p M).evalR realEnv = Checks.rowSmallBase p M := by
  simp [smallBaseE, Expr.evalR, Checks.rowSmallBase]

@[simp] theorem smallPositiveSideE_meaning (p M : Nat) :
    (smallPositiveSideE p M).evalR realEnv =
      Checks.rowEll0 p * Checks.rowSmallBase p M -
        (3 / 2) * Checks.rowA p M * Real.sqrt (startingMean p) := by
  simp [smallPositiveSideE, Expr.evalR]

@[simp] theorem smallNonpositiveSideE_meaning (p : Nat) :
    (smallNonpositiveSideE p).evalR realEnv = Checks.rowEll0 p * startingMean p - (3 / 2) := by
  simp [smallNonpositiveSideE, Expr.evalR]

theorem smallPositive_sound {p M : Nat} (h : smallPositive p M = true) :
    0 < Checks.rowSmallBase p M := by
  have hp := (smallBaseE p M).positiveOK_sound env_mem h
  simpa using hp

theorem smallNonpositive_sound {p M : Nat} (h : smallNonpositive p M = true) :
    Checks.rowSmallBase p M ≤ 0 := by
  have hp := (smallBaseE p M).upperOK_sound 0 env_mem h
  simpa using hp

/-- The selected AST branch equals the actual strict-positive branch. -/
theorem smallPriceE_meaning {p M : Nat} (hguard : smallGuard p M = true) :
    (smallPriceE p M).evalR realEnv = Checks.rowSmallPrice p M := by
  cases hp : smallPositive p M with
  | true =>
    have hbase := smallPositive_sound hp
    simp [smallPriceE, hp, Checks.rowSmallPrice, hbase, Expr.evalR]
  | false =>
    have hn : smallNonpositive p M = true := by
      have hg : smallNonpositive p M = true ∧
          (smallNonpositiveSideE p).nonnegativeOK env = true := by
        simpa [smallGuard, hp] using hguard
      exact hg.1
    have hbase := smallNonpositive_sound hn
    simp [smallPriceE, hp, Checks.rowSmallPrice, not_lt_of_ge hbase, Expr.evalR]

/-- Both source provisos survive the selected branch, including equality zero. -/
theorem smallGuard_sound {p M : Nat} (hguard : smallGuard p M = true) :
    (0 < Checks.rowSmallBase p M →
      (3 / 2) * Checks.rowA p M * Real.sqrt (startingMean p) ≤
        Checks.rowEll0 p * Checks.rowSmallBase p M) ∧
    (Checks.rowSmallBase p M ≤ 0 → (3 / 2 : ℝ) ≤ Checks.rowEll0 p * startingMean p) := by
  cases hp : smallPositive p M with
  | true =>
    have hbase := smallPositive_sound hp
    have hs : (smallPositiveSideE p M).nonnegativeOK env = true := by
      simpa [smallGuard, hp] using hguard
    have hside := (smallPositiveSideE p M).nonnegativeOK_sound env_mem hs
    simp only [smallPositiveSideE_meaning] at hside
    constructor
    · intro _; linarith
    · intro h; exact False.elim (not_le_of_gt hbase h)
  | false =>
    have hg : smallNonpositive p M = true ∧
        (smallNonpositiveSideE p).nonnegativeOK env = true := by
      simpa [smallGuard, hp] using hguard
    have hbase := smallNonpositive_sound hg.1
    have hside := (smallNonpositiveSideE p).nonnegativeOK_sound env_mem hg.2
    simp only [smallNonpositiveSideE_meaning] at hside
    constructor
    · intro h; exact False.elim (not_lt_of_ge hbase h)
    · intro _; linarith

theorem foldMaximum_meaning (xs : List Expr) (a : Expr) :
    (xs.foldl Expr.maximum a).evalR realEnv =
      (xs.map (fun e => e.evalR realEnv)).foldl max (a.evalR realEnv) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simpa [List.foldl, Expr.evalR] using ih (Expr.maximum a x)

theorem maxE_meaning (xs : List Expr) :
    (maxE xs).evalR realEnv = Checks.maxList (xs.map (fun e => e.evalR realEnv)) := by
  simpa [maxE, Checks.maxList, Expr.evalR] using foldMaximum_meaning xs (.rat 0)

theorem zaE_meaning {p : Nat} (hsmall : ∀ M : Nat, M < 8 → smallGuard p M = true) :
    (zaE p).evalR realEnv = Checks.rowZa p := by
  rw [zaE, maxE_meaning]
  unfold Checks.rowZa
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro M hM
  exact smallPriceE_meaning (hsmall M (List.mem_range.mp hM))

@[simp] theorem blockMlowE_meaning (p : Nat) (cell : V22SpikeCell) (i : Nat) :
    (blockMlowE p cell i).evalR realEnv = Checks.rowBlockMlow p cell i := by
  simp [blockMlowE, Expr.evalR, multiplierQ, Checks.rowBlockMlow, blockMultipliers]

@[simp] theorem blockExponentE_meaning (p : Nat) (cell : V22SpikeCell) (i : Nat) :
    (blockExponentE p cell i).evalR realEnv = Checks.rowBlockExponent p cell i := by
  simp [blockExponentE, Expr.evalR, Checks.rowBlockExponent]

@[simp] theorem blockPriceE_meaning (p : Nat) (cell : V22SpikeCell) (i : Nat) :
    (blockPriceE p cell i).evalR realEnv = Checks.rowBlockPrice p cell i := by
  simp [blockPriceE, Expr.evalR, Checks.rowBlockPrice]

theorem zbE_meaning (p : Nat) : (zbE p).evalR realEnv = Checks.rowZb p := by
  rw [zbE, maxE_meaning]
  unfold Checks.rowZb
  congr 1
  simp only [List.map_flatMap]
  apply congrArg (fun f => spikeCells.flatMap f)
  funext cell
  by_cases h : usesCell p cell = true
  · have hr := (usesCell_iff p cell).mp h
    simp [h, hr, List.map_map]
  · have hr : ¬Checks.rowUsesCell p cell := fun hc => h ((usesCell_iff p cell).mpr hc)
    simp [h, hr]

@[simp] theorem mcE_meaning (p : Nat) : (mcE p).evalR realEnv = Checks.rowMc p := by
  simp [mcE, Expr.evalR, Checks.rowMc]

@[simp] theorem smallRateE_meaning (p : Nat) :
    (smallRateE p).evalR realEnv = Checks.rowSmallRate p := by
  simp [smallRateE, Expr.evalR, Checks.rowSmallRate]

@[simp] theorem zcE_meaning (p : Nat) : (zcE p).evalR realEnv = Checks.rowZc p := by
  simp [zcE, Expr.evalR, Checks.rowZc]

@[simp] theorem decayE_meaning (p : Nat) (cell : V22SpikeCell) :
    (decayE p cell).evalR realEnv = Checks.rowEll0 p / (cell.hi : ℝ) - Checks.rowLb p := by
  simp [decayE, Expr.evalR]

@[simp] theorem verySmallSideE_meaning (p : Nat) :
    (verySmallSideE p).evalR realEnv = Checks.rowSmallRate p * Checks.rowMc p - (3 / 2) := by
  simp [verySmallSideE, Expr.evalR]

theorem marginE_meaning {p : Nat} (hsmall : ∀ M : Nat, M < 8 → smallGuard p M = true) :
    (marginE p).evalR realEnv = Checks.rowMargin p := by
  simp [marginE, Expr.evalR, zaE_meaning hsmall, zbE_meaning, Checks.rowMargin, pieceQ, pieceV22]

/-- All row guards and the positive margin imply the complete row assertion.
No printed log margin or free positivity certificate replaces rowMargin. -/
theorem rowPass_sound {p : Nat} (hpass : rowPass p = true) :
    19 ≤ startingMean p ∧ 0 ≤ excess p ∧ excess p ≤ 1 ∧
    0 < Checks.rowEll0 p ∧ 0 < Checks.rowVmin p ∧ Checks.rowSmallSideConditions p ∧
    (3 / 2 : ℝ) ≤ Checks.rowSmallRate p * Checks.rowMc p ∧
    (∀ cell ∈ spikeCells, Checks.rowUsesCell p cell →
      Checks.rowLb p < Checks.rowEll0 p / (cell.hi : ℝ)) ∧
    0 < Checks.rowMargin p := by
  simp only [rowPass, Bool.and_eq_true] at hpass
  have hg := hpass.1
  simp only [rowGuard, Bool.and_eq_true, decide_eq_true_eq] at hg
  rcases hg with ⟨⟨⟨⟨hbasic, hpos⟩, hsmall⟩, hvery⟩, hdecay⟩
  have hsmall' : ∀ M : Nat, M < 8 → smallGuard p M = true := by
    intro M hM
    exact List.all_eq_true.mp hsmall M (List.mem_range.mpr hM)
  have hmean : (19 : ℝ) ≤ startingMean p := by
    rw [← meanQ_meaning]
    exact_mod_cast hbasic.1
  have hb0 : (0 : ℝ) ≤ excess p := by
    rw [← excessQ_meaning]
    exact_mod_cast hbasic.2.1
  have hb1 : excess p ≤ (1 : ℝ) := by
    rw [← excessQ_meaning]
    exact_mod_cast hbasic.2.2
  have hell : (0 : ℝ) < Checks.rowEll0 p := by
    rw [← ellQ_meaning]
    exact_mod_cast hpos.1
  have hv : (0 : ℝ) < Checks.rowVmin p := by
    rw [← vminQ_meaning]
    exact_mod_cast hpos.2
  have hs : Checks.rowSmallSideConditions p := by
    intro M hM
    exact smallGuard_sound (hsmall' M hM)
  have hvs := (verySmallSideE p).nonnegativeOK_sound env_mem hvery
  simp only [verySmallSideE_meaning] at hvs
  have hvs' : (3 / 2 : ℝ) ≤ Checks.rowSmallRate p * Checks.rowMc p := by linarith
  have hd : ∀ cell ∈ spikeCells, Checks.rowUsesCell p cell →
      Checks.rowLb p < Checks.rowEll0 p / (cell.hi : ℝ) := by
    intro cell hcell hused
    have hu := (usesCell_iff p cell).mpr hused
    have hp := List.all_eq_true.mp hdecay cell hcell
    simp only [hu, Bool.not_true, Bool.false_or] at hp
    have hprice := (decayE p cell).positiveOK_sound env_mem hp
    simp only [decayE_meaning] at hprice
    linarith
  have hm := (marginE p).positiveOK_sound env_mem hpass.2
  rw [marginE_meaning hsmall'] at hm
  exact ⟨hmean, hb0, hb1, hell, hv, hs, hvs', hd, hm⟩

/-- The eventual finite certificate is consumed by the exact fifty-five-row
statement, with every side condition and its actual margin retained. -/
theorem check_sound (hcheck : check = true) : Checks.lemma_7_21 := by
  intro p hp
  have hrow : rowPass p = true := List.all_eq_true.mp hcheck p (List.mem_range.mpr hp)
  exact rowPass_sound hrow

end

end Erdos993Lean.Analytic.V22.RowsSound
