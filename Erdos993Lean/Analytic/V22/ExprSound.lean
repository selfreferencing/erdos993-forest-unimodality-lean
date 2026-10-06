import Erdos993Lean.Analytic.V22.Compute.Expr
import Erdos993Lean.Analytic.V22.RootBracketSound
import Erdos993Lean.Analytic.Reserve.Cert.CellSound
import Erdos993Lean.Analytic.TailCert.ExpLog

/-!
# Soundness of the version 2.2 expression evaluator

All computations use the existing checked fixed-point arithmetic. The root
node is consumed only through a proved real bracket theorem. This is generic
evaluation soundness; it does not assert any formula-specific finite check.
-/

namespace Erdos993Lean.Analytic.V22.Compute

open Real Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute

noncomputable def Expr.evalR (env : Nat → ℝ) : Expr → ℝ
  | .rat q => q
  | .var i => env i
  | .add a b => a.evalR env + b.evalR env
  | .sub a b => a.evalR env - b.evalR env
  | .neg a => -a.evalR env
  | .mul a b => a.evalR env * b.evalR env
  | .div a b => a.evalR env / b.evalR env
  | .minimum a b => min (a.evalR env) (b.evalR env)
  | .maximum a b => max (a.evalR env) (b.evalR env)
  | .sq a => a.evalR env ^ 2
  | .powNat a n => a.evalR env ^ n
  | .exp a => Real.exp (a.evalR env)
  | .log a => Real.log (a.evalR env)
  | .sqrt a => Real.sqrt (a.evalR env)
  | .rpow a q => Real.rpow (a.evalR env) (q : ℝ)
  | .root _ _ a => rootMap (a.evalR env)

theorem mem_powNatI {A : Ival} {x : ℝ} (hA : A.Mem x) (n : Nat) :
    (powNatI A n).Mem (x ^ n) := by
  induction n with
  | zero => simpa [powNatI] using mem_ofRat (1 : Rat)
  | succ n ih => simpa [powNatI, pow_succ] using mem_mul ih hA

theorem mem_rootEndpointI (a : Rat) (hpos : 0 < (rootShiftI a).lo) :
    (rootEndpointI a).Mem ((a : ℝ) + Real.log (1 + (a : ℝ))) := by
  have hs : (rootShiftI a).Mem (1 + (a : ℝ)) := by
    simpa [rootShiftI] using mem_add (mem_ofRat (1 : Rat)) (mem_ofRat a)
  exact mem_add (mem_ofRat a) (mem_logI hs hpos)

theorem mem_bracketI_root {a b : Rat} {L : Ival} {l : ℝ}
    (hL : L.Mem l) (hok : rootBracketOK a b L = true) :
    (bracketI a b).Mem (rootMap l) := by
  simp only [rootBracketOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  rcases hok with ⟨⟨⟨⟨⟨ha, hab⟩, hpa⟩, hpb⟩, hleft⟩, hright⟩
  have haR : (-1 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hleftR : (a : ℝ) + Real.log (1 + (a : ℝ)) ≤ l :=
    (mem_rootEndpointI a hpa).2.trans ((toR_le_toR.mpr hleft).trans hL.1)
  have hrightR : l ≤ (b : ℝ) + Real.log (1 + (b : ℝ)) :=
    hL.2.trans ((toR_le_toR.mpr hright).trans (mem_rootEndpointI b hpb).1)
  have hr := rootMap_mem_bracket haR habR hleftR hrightR
  exact ⟨(mem_ofRat a).1.trans hr.1, hr.2.trans (mem_ofRat b).2⟩

/-- Every safe interval evaluation encloses the exact real expression. -/
theorem Expr.evalI_mem (e : Expr) {env : Nat → Ival} {realEnv : Nat → ℝ}
    (henv : ∀ i, (env i).Mem (realEnv i)) (hsafe : e.safe env = true) :
    (e.evalI env).Mem (e.evalR realEnv) := by
  induction e with
  | rat q => exact mem_ofRat q
  | var i => exact henv i
  | add a b ia ib =>
    simp only [Expr.safe, Bool.and_eq_true] at hsafe
    exact mem_add (ia hsafe.1) (ib hsafe.2)
  | sub a b ia ib =>
    simp only [Expr.safe, Bool.and_eq_true] at hsafe
    exact mem_sub (ia hsafe.1) (ib hsafe.2)
  | neg a ia => exact mem_neg (ia hsafe)
  | mul a b ia ib =>
    simp only [Expr.safe, Bool.and_eq_true] at hsafe
    exact mem_mul (ia hsafe.1) (ib hsafe.2)
  | div a b ia ib =>
    simp only [Expr.safe, Bool.and_eq_true, decide_eq_true_eq] at hsafe
    exact mem_div (ia hsafe.1.1) (ib hsafe.1.2) hsafe.2
  | minimum a b ia ib =>
    simp only [Expr.safe, Bool.and_eq_true] at hsafe
    have ha := ia hsafe.1
    have hb := ib hsafe.2
    exact ⟨by simpa [Expr.evalI, Expr.evalR, toR_min] using min_le_min ha.1 hb.1,
      by simpa [Expr.evalI, Expr.evalR, toR_min] using min_le_min ha.2 hb.2⟩
  | maximum a b ia ib =>
    simp only [Expr.safe, Bool.and_eq_true] at hsafe
    have ha := ia hsafe.1
    have hb := ib hsafe.2
    exact ⟨by simpa [Expr.evalI, Expr.evalR, toR_max] using max_le_max ha.1 hb.1,
      by simpa [Expr.evalI, Expr.evalR, toR_max] using max_le_max ha.2 hb.2⟩
  | sq a ia => exact Reserve.Cert.mem_sqI (ia hsafe)
  | powNat a n ia => exact mem_powNatI (ia hsafe) n
  | exp a ia => exact mem_expI (ia hsafe)
  | log a ia =>
    simp only [Expr.safe, Bool.and_eq_true, decide_eq_true_eq] at hsafe
    exact mem_logI (ia hsafe.1) hsafe.2
  | sqrt a ia =>
    simp only [Expr.safe, Bool.and_eq_true, decide_eq_true_eq] at hsafe
    exact mem_sqrtI (ia hsafe.1) hsafe.2
  | rpow a q ia =>
    simp only [Expr.safe, Bool.and_eq_true, decide_eq_true_eq] at hsafe
    have ha := ia hsafe.1
    have hpos : 0 < a.evalR realEnv := (toR_pos.mpr hsafe.2).trans_le ha.1
    have h := mem_expI (mem_mul (mem_ofRat q) (mem_logI ha hsafe.2))
    simpa [Expr.evalI, Expr.evalR, Real.rpow_def_of_pos hpos, mul_comm] using h
  | root lo hi a ia =>
    simp only [Expr.safe, Bool.and_eq_true] at hsafe
    exact mem_bracketI_root (ia hsafe.1) hsafe.2

theorem Expr.positiveOK_sound (e : Expr) {env : Nat → Ival} {realEnv : Nat → ℝ}
    (henv : ∀ i, (env i).Mem (realEnv i)) (hok : e.positiveOK env = true) :
    0 < e.evalR realEnv := by
  simp only [Expr.positiveOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  exact (toR_pos.mpr hok.2).trans_le (e.evalI_mem henv hok.1).1

theorem Expr.nonnegativeOK_sound (e : Expr) {env : Nat → Ival} {realEnv : Nat → ℝ}
    (henv : ∀ i, (env i).Mem (realEnv i)) (hok : e.nonnegativeOK env = true) :
    0 ≤ e.evalR realEnv := by
  simp only [Expr.nonnegativeOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  exact (toR_nonneg.mpr hok.2).trans (e.evalI_mem henv hok.1).1

theorem Expr.upperOK_sound (e : Expr) {env : Nat → Ival} {realEnv : Nat → ℝ} (q : Rat)
    (henv : ∀ i, (env i).Mem (realEnv i)) (hok : e.upperOK env q = true) :
    e.evalR realEnv ≤ (q : ℝ) := by
  simp only [Expr.upperOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  exact (e.evalI_mem henv hok.1).2.trans ((toR_le_toR.mpr hok.2).trans (mem_ofRat q).1)

theorem Expr.strictUpperOK_sound (e : Expr) {env : Nat → Ival} {realEnv : Nat → ℝ} (q : Rat)
    (henv : ∀ i, (env i).Mem (realEnv i)) (hok : e.strictUpperOK env q = true) :
    e.evalR realEnv < (q : ℝ) := by
  simp only [Expr.strictUpperOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  exact (e.evalI_mem henv hok.1).2.trans_lt ((toR_lt_toR.mpr hok.2).trans_le (mem_ofRat q).1)

end Erdos993Lean.Analytic.V22.Compute
