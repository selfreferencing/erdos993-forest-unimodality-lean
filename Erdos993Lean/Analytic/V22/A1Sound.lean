import Erdos993Lean.Analytic.V22.Compute.A1
import Erdos993Lean.Analytic.V22.Checks.EarlyStatements
import Erdos993Lean.Analytic.TailCert.IvalSound

/-!
# A1 interval-recipe soundness and exact six-cell coverage

The computable recipe encloses a real lower corner. Positive-coefficient
polynomial monotonicity and the decreasing positive factor 1-a prove that
this corner is a lower bound for the repaired Q on its whole cell.
This module proves implications from the check; it contains no native_decide
evaluation or assumed finite-check certificate.
-/

namespace Erdos993Lean.Analytic.V22.A1Sound

open Erdos993Lean.Analytic.TailCert
open Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.V22.Compute.A1

noncomputable section

/-- Real lower corner prescribed by the source's termwise monotone recipe. -/
def cornerBound (lo hi : ℝ) : ℝ :=
  (18 / 25) * polynomialLambdaQuotient lo ^ 2 *
    (1 + Lambda lo ^ 2 / 75) * (1 - hi) - 2

theorem Lambda_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Lambda x := by
  unfold Lambda
  positivity

theorem quotient_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ polynomialLambdaQuotient x := by
  unfold polynomialLambdaQuotient
  positivity

theorem Lambda_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    Lambda x ≤ Lambda y := by
  have h1 := mul_le_mul_of_nonneg_left hxy (by norm_num : (0 : ℝ) ≤ 2)
  have h2 := div_le_div_of_nonneg_right (pow_le_pow_left₀ hx hxy 2)
    (by norm_num : (0 : ℝ) ≤ 2)
  have h3 := div_le_div_of_nonneg_right (pow_le_pow_left₀ hx hxy 3)
    (by norm_num : (0 : ℝ) ≤ 3)
  have h4 := div_le_div_of_nonneg_right (pow_le_pow_left₀ hx hxy 4)
    (by norm_num : (0 : ℝ) ≤ 4)
  have h5 := div_le_div_of_nonneg_right (pow_le_pow_left₀ hx hxy 5)
    (by norm_num : (0 : ℝ) ≤ 5)
  have h6 := div_le_div_of_nonneg_right (pow_le_pow_left₀ hx hxy 6)
    (by norm_num : (0 : ℝ) ≤ 6)
  unfold Lambda
  linarith

theorem quotient_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    polynomialLambdaQuotient x ≤ polynomialLambdaQuotient y := by
  have h1 := div_le_div_of_nonneg_right hxy (by norm_num : (0 : ℝ) ≤ 2)
  have h2 := div_le_div_of_nonneg_right (pow_le_pow_left₀ hx hxy 2)
    (by norm_num : (0 : ℝ) ≤ 3)
  have h3 := div_le_div_of_nonneg_right (pow_le_pow_left₀ hx hxy 3)
    (by norm_num : (0 : ℝ) ≤ 4)
  have h4 := div_le_div_of_nonneg_right (pow_le_pow_left₀ hx hxy 4)
    (by norm_num : (0 : ℝ) ≤ 5)
  have h5 := div_le_div_of_nonneg_right (pow_le_pow_left₀ hx hxy 5)
    (by norm_num : (0 : ℝ) ≤ 6)
  unfold polynomialLambdaQuotient
  linarith

theorem cornerBound_le_Q {lo hi a : ℝ} (hlo : 0 ≤ lo) (hla : lo ≤ a)
    (hah : a ≤ hi) (hhi : hi ≤ 66 / 125) : cornerBound lo hi ≤ Q a := by
  have ha : 0 ≤ a := hlo.trans hla
  have hq := pow_le_pow_left₀ (quotient_nonneg hlo) (quotient_mono hlo hla) 2
  have hl := pow_le_pow_left₀ (Lambda_nonneg hlo) (Lambda_mono hlo hla) 2
  have hfirst : (18 / 25 : ℝ) * polynomialLambdaQuotient lo ^ 2 ≤
      (18 / 25 : ℝ) * polynomialLambdaQuotient a ^ 2 :=
    mul_le_mul_of_nonneg_left hq (by norm_num)
  have hfactor : 1 + Lambda lo ^ 2 / 75 ≤ 1 + Lambda a ^ 2 / 75 := by
    simpa only [add_comm] using
      add_le_add_left (div_le_div_of_nonneg_right hl (by norm_num : (0 : ℝ) ≤ 75)) 1
  have hprod : (18 / 25 : ℝ) * polynomialLambdaQuotient lo ^ 2 *
      (1 + Lambda lo ^ 2 / 75) ≤
      (18 / 25 : ℝ) * polynomialLambdaQuotient a ^ 2 *
      (1 + Lambda a ^ 2 / 75) :=
    mul_le_mul hfirst hfactor (by positivity) (by positivity)
  have hlast : 1 - hi ≤ 1 - a := sub_le_sub_left hah 1
  have hlastpos : 0 < 1 - hi := by linarith
  have htotal := mul_le_mul hprod hlast hlastpos.le
    (by positivity : (0 : ℝ) ≤ (18 / 25) * polynomialLambdaQuotient a ^ 2 *
      (1 + Lambda a ^ 2 / 75))
  exact sub_le_sub_right htotal 2

theorem powI_mem {A : Ival} {x : ℝ} (hx : A.Mem x) (n : Nat) :
    (powI A n).Mem (x ^ n) := by
  induction n with
  | zero => simpa [powI, toR_one] using mem_pt one
  | succ n ih => simpa [powI, pow_succ] using mem_mul ih hx

theorem lamI_mem {A : Ival} {x : ℝ} (hx : A.Mem x) :
    (lamI A).Mem (Lambda x) := by
  have htwo : (ofRat 2).Mem (2 : ℝ) := by simpa using mem_ofRat (2 : Rat)
  simpa only [lamI, Lambda, Nat.cast_ofNat] using
    mem_add (mem_add (mem_add (mem_add (mem_add (mem_mul htwo hx)
      (mem_divNat (k := 2) (powI_mem hx 2) (by decide)))
      (mem_divNat (k := 3) (powI_mem hx 3) (by decide)))
      (mem_divNat (k := 4) (powI_mem hx 4) (by decide)))
      (mem_divNat (k := 5) (powI_mem hx 5) (by decide)))
      (mem_divNat (k := 6) (powI_mem hx 6) (by decide))

theorem lamAI_mem {A : Ival} {x : ℝ} (hx : A.Mem x) :
    (lamAI A).Mem (polynomialLambdaQuotient x) := by
  have htwo : (ofRat 2).Mem (2 : ℝ) := by simpa using mem_ofRat (2 : Rat)
  simpa only [lamAI, polynomialLambdaQuotient, Nat.cast_ofNat] using
    mem_add (mem_add (mem_add (mem_add (mem_add htwo
      (mem_divNat (k := 2) hx (by decide)))
      (mem_divNat (k := 3) (powI_mem hx 2) (by decide)))
      (mem_divNat (k := 4) (powI_mem hx 3) (by decide)))
      (mem_divNat (k := 5) (powI_mem hx 4) (by decide)))
      (mem_divNat (k := 6) (powI_mem hx 5) (by decide))

theorem cornerI_mem (c : Cell) :
    (cornerI c).Mem (cornerBound (c.1 : ℝ) (c.2 : ℝ)) := by
  have hlo := mem_ofRat c.1
  have hhi := mem_ofRat c.2
  have hone : (ofRat 1).Mem (1 : ℝ) := by simpa using mem_ofRat (1 : Rat)
  have htwo : (ofRat 2).Mem (2 : ℝ) := by simpa using mem_ofRat (2 : Rat)
  have hcoef : (ofRat (18 / 25)).Mem (18 / 25 : ℝ) := by
    simpa using mem_ofRat (18 / 25 : Rat)
  simpa only [cornerI, cornerBound, Nat.cast_ofNat] using
    mem_sub (mem_mul (mem_mul (mem_mul hcoef (powI_mem (lamAI_mem hlo) 2))
      (mem_add hone (mem_divNat (k := 75) (powI_mem (lamI_mem hlo) 2) (by decide))))
      (mem_sub hone hhi)) htwo

/-- Any passing cell gives the actual Q bound on its whole closed real cell. -/
theorem passes_sound {c : Cell} (hpass : passes c = true) {a : ℝ}
    (ha : Checks.inCell c.1 c.2 a) : (53 / 10000 : ℝ) ≤ Q a := by
  simp only [passes, domainGuard, Bool.and_eq_true, decide_eq_true_eq] at hpass
  have hlo : (0 : ℝ) ≤ (c.1 : ℝ) := by exact_mod_cast hpass.1.1
  have hhi : (c.2 : ℝ) ≤ (66 / 125 : ℝ) := by
    have ht : (c.2 : ℝ) ≤ ((66 / 125 : Rat) : ℝ) := by exact_mod_cast hpass.1.2.2
    norm_num at ht
    exact ht
  have ht : (53 / 10000 : ℝ) ≤ toR (ofRat threshold).hi := by
    simpa [threshold] using (mem_ofRat threshold).2
  have hlow : toR (ofRat threshold).hi ≤ toR (cornerI c).lo :=
    toR_le_toR.mpr hpass.2
  exact (ht.trans hlow).trans
    ((cornerI_mem c).1.trans (cornerBound_le_Q hlo ha.1 ha.2 hhi))

/-- The six adjacent nominal cells cover every point of the source interval. -/
theorem cells_cover {a : ℝ} (ha : Checks.inCell 0 (66 / 125) a) :
    ∃ c ∈ cells, Checks.inCell c.1 c.2 a := by
  by_cases h1 : a ≤ 303 / 1000
  · refine ⟨(0, 303 / 1000), by simp [cells], ?_⟩
    norm_num [Checks.inCell]
    exact ⟨ha.1, h1⟩
  by_cases h2 : a ≤ 423 / 1000
  · refine ⟨(303 / 1000, 423 / 1000), by simp [cells], ?_⟩
    norm_num [Checks.inCell]
    exact ⟨(lt_of_not_ge h1).le, h2⟩
  by_cases h3 : a ≤ 479 / 1000
  · refine ⟨(423 / 1000, 479 / 1000), by simp [cells], ?_⟩
    norm_num [Checks.inCell]
    exact ⟨(lt_of_not_ge h2).le, h3⟩
  by_cases h4 : a ≤ 507 / 1000
  · refine ⟨(479 / 1000, 507 / 1000), by simp [cells], ?_⟩
    norm_num [Checks.inCell]
    exact ⟨(lt_of_not_ge h3).le, h4⟩
  by_cases h5 : a ≤ 261 / 500
  · refine ⟨(507 / 1000, 522 / 1000), by simp [cells], ?_⟩
    norm_num [Checks.inCell]
    exact ⟨(lt_of_not_ge h4).le, h5⟩
  · refine ⟨(522 / 1000, 66 / 125), by simp [cells], ?_⟩
    norm_num [Checks.inCell]
    exact ⟨(lt_of_not_ge h5).le, ha.2⟩

/-- The D4 finite certificate is consumed by this D2 soundness theorem. -/
theorem check_sound (hcheck : check = true) : Checks.lemma_7_2 := by
  intro a ha
  obtain ⟨c, hc, hcell⟩ := cells_cover ha
  have hpasses : passes c = true := List.all_eq_true.mp hcheck c hc
  exact passes_sound hpasses hcell

end
end Erdos993Lean.Analytic.V22.A1Sound
