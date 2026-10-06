import Erdos993Lean.Analytic.V22.WindowShapeMonotone
import Erdos993Lean.Analytic.V22.Checks.EarlyStatements

/-!
# Exact coefficient transport for the lower spike check

Source: repaired note Lemma 4.10(a) and check 7.13 (B2). The actual
activity and real size are retained. No numerical cell positivity is
asserted; the final two monotonicity clauses are analytic consequences.
-/

namespace Erdos993Lean.Analytic.V22

noncomputable section
open Checks

theorem spike_activity_den_pos {rm : ℝ} (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) :
    0 < 1-rm^2 := by
  nlinarith [mul_nonneg hrm (sub_nonneg.mpr hrmhi)]

theorem nonneg_quotient_antitone {a b c d : ℝ}
    (hab : a ≤ b) (hb : 0 ≤ b) (hc : 0 < c) (hcd : c ≤ d) : a/d ≤ b/c := by
  calc
    a/d ≤ b/d := div_le_div_of_nonneg_right hab (hc.le.trans hcd)
    _ ≤ b/c := div_le_div_of_nonneg_left hb hc hcd

theorem Z0_nonneg {N : ℝ} (hN : 10 ≤ N) : 0 ≤ Z0 N :=
  div_nonneg (Real.sqrt_nonneg N) (by linarith)

theorem Z0_le_third {N : ℝ} (hN : 10 ≤ N) : Z0 N ≤ 1/3 := by
  have hn : 0 ≤ N := by linarith
  have hden : 0 < N+1 := by linarith
  have hprod := mul_nonneg hn (show 0 ≤ N-10 by linarith)
  have hsquare : (3*Real.sqrt N)^2 ≤ (N+1)^2 := by
    rw [mul_pow, Real.sq_sqrt hn]
    nlinarith
  have hcross := (sq_le_sq₀ (by positivity : 0 ≤ 3*Real.sqrt N) hden.le).mp hsquare
  apply (div_le_iff₀ hden).mpr
  linarith

theorem phiM_bounds {N rm : ℝ} (hN : 10 ≤ N) (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) :
    0 ≤ phiM N rm ∧ phiM N rm ≤ 4/3 := by
  have hn : 0 ≤ N := by linarith
  have hs3 : 3 ≤ Real.sqrt N := Real.le_sqrt_of_sq_le (by nlinarith)
  have hspos : 0 < Real.sqrt N := by linarith
  have hquot : 2*rm/Real.sqrt N ≤ 1/3 := by
    apply (div_le_iff₀ hspos).mpr
    linarith
  have hquotnonneg : 0 ≤ 2*rm/Real.sqrt N := div_nonneg (by positivity) hspos.le
  dsimp [phiM]
  constructor <;> linarith

theorem phiM_antitone_parameter {N N0 rm : ℝ}
    (hN0 : 10 ≤ N0) (hN : N0 ≤ N) (hrm : 0 ≤ rm) : phiM N rm ≤ phiM N0 rm := by
  have hs0 : 0 < Real.sqrt N0 := Real.sqrt_pos.mpr (by linarith)
  have hquot := div_le_div_of_nonneg_left (show 0 ≤ 2*rm by positivity) hs0
    (Real.sqrt_le_sqrt hN)
  dsimp [phiM]
  linarith

theorem KL_den_pos {N rm : ℝ}
    (hN : 10 ≤ N) (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) :
    0 < 1-(Z0 N)^2*(phiM N rm)^2 := by
  have hz := Z0_nonneg hN
  have hzhi := Z0_le_third hN
  have hp := phiM_bounds hN hrm hrmhi
  have hproduct : Z0 N*phiM N rm ≤ (1/3:ℝ)*(4/3) :=
    mul_le_mul hzhi hp.2 hp.1 (by norm_num)
  have hnonneg := mul_nonneg hz hp.1
  have hsquare := (sq_le_sq₀ hnonneg (by norm_num : 0 ≤ (1/3:ℝ)*(4/3))).mpr hproduct
  rw [mul_pow] at hsquare
  nlinarith

theorem KR_den_pos {N rm : ℝ}
    (hN : 10 ≤ N) (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) :
    0 < 1-(rm+Z0 N)^2 := by
  have hz := Z0_nonneg hN
  have hzhi := Z0_le_third hN
  have hlo : 0 ≤ rm+Z0 N := add_nonneg hrm hz
  have hhi : rm+Z0 N ≤ 5/6 := by linarith
  have hsquare := (sq_le_sq₀ hlo (by norm_num : (0:ℝ) ≤ 5/6)).mpr hhi
  nlinarith

theorem KL_nonneg {N rm : ℝ}
    (hN : 10 ≤ N) (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) : 0 ≤ KL N rm := by
  have hd := KL_den_pos hN hrm hrmhi
  dsimp [KL]
  positivity

theorem KR_nonneg {N rm : ℝ}
    (hN : 10 ≤ N) (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) : 0 ≤ KR N rm :=
  div_nonneg (by norm_num) (KR_den_pos hN hrm hrmhi).le

theorem KL_antitone_parameter {N N0 rm : ℝ}
    (hN0 : 10 ≤ N0) (hN : N0 ≤ N) (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) :
    KL N rm ≤ KL N0 rm := by
  have hN10 := hN0.trans hN
  have hz := sqrt_div_add_one_antitone (show 1 ≤ N0 by linarith) hN
  have hz0 := Z0_nonneg hN0
  have hzN := Z0_nonneg hN10
  have hphi := phiM_antitone_parameter hN0 hN hrm
  have hp0 := (phiM_bounds hN0 hrm hrmhi).1
  have hpN := (phiM_bounds hN10 hrm hrmhi).1
  have hzsq : (Z0 N)^2 ≤ (Z0 N0)^2 := (sq_le_sq₀ hzN hz0).mpr hz
  have hpsq : (phiM N rm)^2 ≤ (phiM N0 rm)^2 := (sq_le_sq₀ hpN hp0).mpr hphi
  have hproduct := mul_le_mul hzsq hpsq (sq_nonneg _) (sq_nonneg _)
  have hdenorder : 1-(Z0 N0)^2*(phiM N0 rm)^2 ≤
      1-(Z0 N)^2*(phiM N rm)^2 := by linarith
  have hquot := nonneg_quotient_antitone hpsq (sq_nonneg _)
    (KL_den_pos hN0 hrm hrmhi) hdenorder
  dsimp [KL]
  linarith

theorem KR_antitone_parameter {N N0 rm : ℝ}
    (hN0 : 10 ≤ N0) (hN : N0 ≤ N) (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) :
    KR N rm ≤ KR N0 rm := by
  have hN10 := hN0.trans hN
  have hz := sqrt_div_add_one_antitone (show 1 ≤ N0 by linarith) hN
  have hloN : 0 ≤ rm+Z0 N := add_nonneg hrm (Z0_nonneg hN10)
  have hlo0 : 0 ≤ rm+Z0 N0 := add_nonneg hrm (Z0_nonneg hN0)
  have hsquare := (sq_le_sq₀ hloN hlo0).mpr (add_le_add (le_refl rm) hz)
  exact div_le_div_of_nonneg_left (by norm_num) (KR_den_pos hN0 hrm hrmhi)
    (by linarith)

/-- All four linearised coefficient entries retain nonnegative numerators
and positive denominators on the stated size/activity range. -/
theorem linearCoefficient_nonneg {N rm : ℝ}
    (hN : 10 ≤ N) (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) :
    0 ≤ cL1 N rm ∧ 0 ≤ cL2 N rm ∧ 0 ≤ cR1 N rm ∧ 0 ≤ cR2 N rm := by
  have hd := spike_activity_den_pos hrm hrmhi
  have hn : 0 < N := by linarith
  have hn1 : 0 < N+1 := by linarith
  have hkl := KL_nonneg hN hrm hrmhi
  have hkr := KR_nonneg hN hrm hrmhi
  dsimp [cL1, cL2, cR1, cR2]
  constructor
  · positivity
  constructor
  · positivity
  constructor <;> positivity

theorem linearCoefficient_antitone_parameter {N N0 rm : ℝ}
    (hN0 : 10 ≤ N0) (hN : N0 ≤ N) (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) :
    cL1 N rm ≤ cL1 N0 rm ∧ cL2 N rm ≤ cL2 N0 rm ∧
      cR1 N rm ≤ cR1 N0 rm ∧ cR2 N rm ≤ cR2 N0 rm := by
  have hd := spike_activity_den_pos hrm hrmhi
  have hn0 : 0 < N0 := by linarith
  have hn : 0 < N := hn0.trans_le hN
  have hn01 : 0 < N0+1 := by linarith
  have hkl := KL_antitone_parameter hN0 hN hrm hrmhi
  have hkr := KR_antitone_parameter hN0 hN hrm hrmhi
  have hkl0 := KL_nonneg hN0 hrm hrmhi
  have hkr0 := KR_nonneg hN0 hrm hrmhi
  have hden : N0*(1-rm^2) ≤ N*(1-rm^2) := mul_le_mul_of_nonneg_right hN hd.le
  have hden1 : (N0+1)*(1-rm^2) ≤ (N+1)*(1-rm^2) :=
    mul_le_mul_of_nonneg_right (add_le_add hN (le_refl 1)) hd.le
  have hNsq : N0^2 ≤ N^2 := (sq_le_sq₀ hn0.le hn.le).mpr hN
  have hleftquad : 4*KL N rm/N^2 ≤ 4*KL N0 rm/N0^2 :=
    nonneg_quotient_antitone (mul_le_mul_of_nonneg_left hkl (by norm_num))
      (by positivity) (sq_pos_of_pos hn0) hNsq
  have hrecip : (1:ℝ)/N ≤ 1/N0 := div_le_div_of_nonneg_left (by norm_num) hn0 hN
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact nonneg_quotient_antitone (mul_le_mul_of_nonneg_left hkl (by norm_num))
      (by positivity) (mul_pos hn0 hd) hden
  · exact div_le_div_of_nonneg_right (add_le_add hleftquad hrecip) hd.le
  · exact nonneg_quotient_antitone (mul_le_mul_of_nonneg_left hkr (by norm_num))
      (by positivity) (mul_pos hn01 hd) hden1
  · exact nonneg_quotient_antitone (add_le_add hkr (le_refl 1))
      (by positivity) (mul_pos hn0 hd) hden

theorem alpha1_nonneg {N rm : ℝ}
    (hN : 10 ≤ N) (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) : 0 ≤ alpha1 N rm := by
  have hd := spike_activity_den_pos hrm hrmhi
  have hcoeff := linearCoefficient_nonneg hN hrm hrmhi
  have hmax : 0 ≤ max (cL1 N rm) (cR1 N rm) := hcoeff.1.trans (le_max_left _ _)
  dsimp [alpha1]
  positivity

theorem alpha2_nonneg {N rm : ℝ}
    (hN : 10 ≤ N) (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) : 0 ≤ alpha2 N rm := by
  have hd := spike_activity_den_pos hrm hrmhi
  have hn : 0 < N := by linarith
  have hcoeff := linearCoefficient_nonneg hN hrm hrmhi
  have hmax : 0 ≤ max (cL2 N rm) (cR2 N rm) := hcoeff.2.1.trans (le_max_left _ _)
  dsimp [alpha2]
  positivity

theorem alpha1_antitone_parameter {N N0 rm : ℝ}
    (hN0 : 10 ≤ N0) (hN : N0 ≤ N) (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) :
    alpha1 N rm ≤ alpha1 N0 rm := by
  have hcoeff := linearCoefficient_antitone_parameter hN0 hN hrm hrmhi
  have hmax := max_le_max hcoeff.1 hcoeff.2.2.1
  exact add_le_add (le_refl _) (div_le_div_of_nonneg_right hmax (by norm_num))

theorem alpha2_antitone_parameter {N N0 rm : ℝ}
    (hN0 : 10 ≤ N0) (hN : N0 ≤ N) (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) :
    alpha2 N rm ≤ alpha2 N0 rm := by
  have hd := spike_activity_den_pos hrm hrmhi
  have hn0 : 0 < N0 := by linarith
  have hfirst : 2/(N*(1-rm^2)) ≤ 2/(N0*(1-rm^2)) :=
    div_le_div_of_nonneg_left (by norm_num) (mul_pos hn0 hd)
      (mul_le_mul_of_nonneg_right hN hd.le)
  have hcoeff := linearCoefficient_antitone_parameter hN0 hN hrm hrmhi
  have hmax := max_le_max hcoeff.2.1 hcoeff.2.2.2
  exact add_le_add hfirst (div_le_div_of_nonneg_right hmax (by norm_num))

theorem sqrt_div_sub_two_antitone {N N0 : ℝ} (hN0 : 10 ≤ N0) (hN : N0 ≤ N) :
    Real.sqrt N/(N-2) ≤ Real.sqrt N0/(N0-2) := by
  have hn0 : 0 ≤ N0 := by linarith
  have hn : 0 ≤ N := by linarith
  have hd0 : 0 < N0-2 := by linarith
  have hd : 0 < N-2 := by linarith
  have hprod : (4:ℝ) ≤ N0*N := by
    have hp := mul_le_mul (show (2:ℝ) ≤ N0 by linarith) (show (2:ℝ) ≤ N by linarith)
      (by norm_num : (0:ℝ) ≤ 2) hn0
    norm_num at hp
    exact hp
  have hgap : 0 ≤ (N-N0)*(N0*N-4) :=
    mul_nonneg (sub_nonneg.mpr hN) (sub_nonneg.mpr hprod)
  have hsquare : (Real.sqrt N*(N0-2))^2 ≤ (Real.sqrt N0*(N-2))^2 := by
    calc
      _ = N*(N0-2)^2 := by rw [mul_pow, Real.sq_sqrt hn]
      _ ≤ N0*(N-2)^2 := by nlinarith
      _ = _ := by rw [mul_pow, Real.sq_sqrt hn0]
  have hcross := (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg N) hd0.le)
    (mul_nonneg (Real.sqrt_nonneg N0) hd.le)).mp hsquare
  exact (div_le_div_iff₀ hd hd0).mpr hcross

theorem div_sub_two_antitone {N N0 : ℝ} (hN0 : 10 ≤ N0) (hN : N0 ≤ N) :
    N/(N-2) ≤ N0/(N0-2) := by
  apply (div_le_div_iff₀ (by linarith : 0 < N-2) (by linarith : 0 < N0-2)).mpr
  nlinarith

/-- The actual term subtracted by the lower spike recipe, before making
the square-root square cancellation valid on `N≥10`. -/
def spikeSubtractedTerm (rm t N : ℝ) : ℝ :=
  2*t*(alpha1 N rm*rm*Real.sqrt N+alpha2 N rm*(rm*Real.sqrt N)^2)/(N-2)

theorem spikeSubtractedTerm_eq_gap (rm t N : ℝ) :
    spikeSubtractedTerm rm t N=(9/2)*(1-t)^2-spikeLowerSlack rm t N := by
  dsimp [spikeSubtractedTerm, spikeLowerSlack]
  ring

theorem spikeSubtractedTerm_factor {rm t N : ℝ} (hN : 10 ≤ N) :
    spikeSubtractedTerm rm t N =
      2*t*(rm*(alpha1 N rm*(Real.sqrt N/(N-2)))+rm^2*(alpha2 N rm*(N/(N-2)))) := by
  dsimp [spikeSubtractedTerm]
  rw [mul_pow, Real.sq_sqrt (show 0 ≤ N by linarith)]
  ring

theorem spikeSubtractedTerm_monotone_t {rm N : ℝ}
    (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) (hN : 10 ≤ N) :
    MonotoneOn (fun t => spikeSubtractedTerm rm t N) (Set.Ici 0) := by
  have ha1 := alpha1_nonneg hN hrm hrmhi
  have ha2 := alpha2_nonneg hN hrm hrmhi
  have hinner : 0 ≤ alpha1 N rm*rm*Real.sqrt N+alpha2 N rm*(rm*Real.sqrt N)^2 := by
    positivity
  have hden : 0 ≤ N-2 := by linarith
  intro x _ y _ hxy
  dsimp [spikeSubtractedTerm]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxy (by norm_num)) hinner) hden

theorem spikeSubtractedTerm_antitone_N {rm t : ℝ}
    (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) (ht : 0 ≤ t) :
    AntitoneOn (fun N => spikeSubtractedTerm rm t N) (Set.Ici 10) := by
  intro N0 hN0 N hN hNorder
  have hN0lo : 10 ≤ N0 := hN0
  have hNlo : 10 ≤ N := hN
  have ha1 := alpha1_antitone_parameter hN0lo hNorder hrm hrmhi
  have ha2 := alpha2_antitone_parameter hN0lo hNorder hrm hrmhi
  have ha10 := alpha1_nonneg hN0lo hrm hrmhi
  have ha20 := alpha2_nonneg hN0lo hrm hrmhi
  have hrat1 := sqrt_div_sub_two_antitone hN0lo hNorder
  have hrat2 := div_sub_two_antitone hN0lo hNorder
  have hrat1nonneg : 0 ≤ Real.sqrt N/(N-2) := div_nonneg (Real.sqrt_nonneg N) (by linarith)
  have hrat2nonneg : 0 ≤ N/(N-2) := div_nonneg (by linarith) (by linarith)
  have hp1 := mul_le_mul ha1 hrat1 hrat1nonneg ha10
  have hp2 := mul_le_mul ha2 hrat2 hrat2nonneg ha20
  have hsum := add_le_add (mul_le_mul_of_nonneg_left hp1 hrm)
    (mul_le_mul_of_nonneg_left hp2 (sq_nonneg rm))
  change spikeSubtractedTerm rm t N ≤ spikeSubtractedTerm rm t N0
  rw [spikeSubtractedTerm_factor hNlo, spikeSubtractedTerm_factor hN0lo]
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

/-- Exact analytic clause of B2: monotonicity in the actual `t`. -/
theorem spikeLowerSlack_subtracted_monotone_t {rm N : ℝ}
    (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) (hN : 10 ≤ N) :
    MonotoneOn (fun t => (9/2)*(1-t)^2-spikeLowerSlack rm t N) (Set.Ici 0) := by
  simpa only [← spikeSubtractedTerm_eq_gap] using spikeSubtractedTerm_monotone_t hrm hrmhi hN

/-- Exact analytic clause of B2: antitonicity in the actual real `N`. -/
theorem spikeLowerSlack_subtracted_antitone_N {rm t : ℝ}
    (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) (ht : 0 ≤ t) :
    AntitoneOn (fun N => (9/2)*(1-t)^2-spikeLowerSlack rm t N) (Set.Ici 10) := by
  simpa only [← spikeSubtractedTerm_eq_gap] using spikeSubtractedTerm_antitone_N hrm hrmhi ht

end

end Erdos993Lean.Analytic.V22
