import Erdos993Lean.Analytic.V22.Checks.LateStatements
import Erdos993Lean.Analytic.V21.PieceBounds
import Erdos993Lean.Analytic.N44.Profile
import Erdos993Lean.Analytic.MGF.Rows
import Mathlib.Tactic

/-!
# The exact inherited parameter domain for the v2.2 no-valley consumer

Source: the 55 inherited subintervals, Tables 1 and 2, and the proof of
`thm:intro-novalley`. The native activity, piece identity, theta cap, hand
variance bound, and all five MGF rows are preserved. The hand cap is bounded
by the stored row cap; equality is not asserted at common activity edges.

The finite proofs below evaluate only rational table identities and domains.
They do not discharge any of the Section 7 analytical finite certificates.
The drafting worker does not run Lean; the lane E root owns verification.
-/

namespace Erdos993Lean.Analytic.V22

deriving instance DecidableEq for V22Class
deriving instance DecidableEq for V22WingClass

namespace Analysis

open Erdos993Lean.Analytic N44

noncomputable section

def E6CentralPiece (p : Nat) : Prop := 6 ≤ p ∧ p ≤ 30
def E6WingPiece (p : Nat) : Prop := 31 ≤ p ∧ p ≤ 39
def E6OuterPiece (p : Nat) : Prop := p ≤ 5 ∨ 40 ≤ p

/-- Rational activity endpoints after the exact activity-to-q map. -/
def e6QaQ (p : Nat) : ℚ := (pieceV22 p).lamLo / (1 + (pieceV22 p).lamLo)
def e6QbQ (p : Nat) : ℚ := (pieceV22 p).lamHi / (1 + (pieceV22 p).lamHi)

/-- Every property here is a rational table property, with the chosen outer
class retained rather than reconstructed from a scalar activity bound. -/
def e6OuterTableQ (p : Nat) : Prop :=
  match classForPiece p with
  | none => False
  | some c =>
      c ∈ classes ∧ p ∈ c.iotas ∧
      (e6QbQ p ≤ 1 / 2 ∨ 1 / 2 ≤ e6QaQ p) ∧
      c.ra ≤ min |2 * e6QaQ p - 1| |2 * e6QbQ p - 1| ∧
      max |2 * e6QaQ p - 1| |2 * e6QbQ p - 1| ≤ c.rb ∧
      c.muD ≤ mu0Data.getD p 0 ∧
      0 ≤ c.ra ∧ c.ra ≤ c.rb ∧ c.rb ≤ 1 / 2 ∧
      0 ≤ c.b ∧ c.b ≤ 1 ∧ 0 ≤ c.beta ∧
      0 < c.tau ∧ c.tau < 1 ∧ 1 < c.thi

def e6WingTableQ (p : Nat) : Prop :=
  match wingForPiece p with
  | none => False
  | some c =>
      c ∈ wingClasses ∧ p ∈ c.iotas ∧ classForPiece p = none ∧
      c.ra ≤ 2 * e6QaQ p - 1 ∧ 2 * e6QbQ p - 1 ≤ c.rb ∧
      c.muW ≤ mu0Data.getD p 0 ∧
      0 < c.ra ∧ c.ra ≤ c.rb ∧ c.rb ≤ 1 / 4 ∧
      0 < c.tau ∧ c.tau ≤ 3 / 5

/-- Computable metadata decisions retain the exact lookup result. Kernel
reduction evaluates the lookup and the rational comparisons in its branch. -/
private instance e6OuterTableQ_decidable (p : Nat) : Decidable (e6OuterTableQ p) := by
  unfold e6OuterTableQ
  cases classForPiece p <;> infer_instance

private instance e6WingTableQ_decidable (p : Nat) : Decidable (e6WingTableQ p) := by
  unfold e6WingTableQ
  cases wingForPiece p <;> infer_instance

theorem e6_piece_partition {p : Nat} (hp : p < 55) :
    E6CentralPiece p ∨ E6WingPiece p ∨ E6OuterPiece p := by
  unfold E6CentralPiece E6WingPiece E6OuterPiece
  omega

theorem e6_table_boundsQ : ∀ p < 55,
    0 < (pieceV22 p).lamLo ∧ (pieceV22 p).lamLo ≤ (pieceV22 p).lamHi ∧
    1 / 4 ≤ e6QaQ p ∧ e6QaQ p ≤ e6QbQ p ∧ e6QbQ p ≤ 7 / 10 ∧
    0 ≤ (pieceV22 p).theta ∧ (pieceV22 p).theta ≤ 1 ∧
    0 < (pieceV22 p).D ∧
    0 < ((pieceV22 p).tilts.getD 0 (0, 0)).2 ∧
    19 ≤ mu0Data.getD p 0 ∧ mu0Data.getD p 0 ≤ 50 ∧
    0 < V21.m25.getD p 0 ∧ V21.m25.getD p 0 ≤ 136 / 9 ∧
    V21.m25.getD p 0 ≤ mu0Data.getD p 0 := by
  decide +kernel

theorem e6_central_tableQ : ∀ p < 55, E6CentralPiece p →
    classForPiece p = none ∧ wingForPiece p = none ∧
    3 / 8 ≤ e6QaQ p ∧ e6QbQ p ≤ 5 / 8 ∧
    (pieceV22 p).theta ≤ 7 / 10 ∧ (pieceV22 p).D = 6 / 5 := by
  intro p hp hc
  unfold E6CentralPiece at hc
  obtain ⟨hp0, hp1⟩ := hc
  interval_cases p <;> decide +kernel

theorem e6_outer_tableQ : ∀ p < 55, E6OuterPiece p → e6OuterTableQ p := by
  intro p hp ho
  unfold E6OuterPiece at ho
  rcases ho with ho | ho
  · interval_cases p <;> decide +kernel
  · interval_cases p <;> decide +kernel

theorem e6_wing_tableQ : ∀ p < 55, E6WingPiece p → e6WingTableQ p := by
  intro p hp hw
  unfold E6WingPiece at hw
  obtain ⟨hp0, hp1⟩ := hw
  interval_cases p <;> decide +kernel

theorem e6_rowQa_cast (p : Nat) : Checks.rowQa p = (e6QaQ p : ℝ) := by
  simp [Checks.rowQa, e6QaQ]

theorem e6_rowQb_cast (p : Nat) : Checks.rowQb p = (e6QbQ p : ℝ) := by
  simp [Checks.rowQb, e6QbQ]

theorem e6_theta_eq (t : ℝ) :
    P44.θb t = ((pieceV22 (pieceOf t)).theta : ℝ) := rfl

theorem e6_tilts_eq (t : ℝ) :
    MGF.tilts44R t = castTilts (pieceV22 (pieceOf t)).tilts := rfl

theorem e6_m25_eq (p : Nat) :
    ((V21.m25.getD p 0 : ℚ) : ℝ) =
      ((MGF.N25.Data.mmin25.getD p 0 : ℚ) : ℝ) := by
  rw [V21.m25_eq_window25]

theorem e6_rowEll0_eq (p : Nat) :
    Checks.rowEll0 p =
      (((N44.Data.rates44.getD p []).getD 0 0 : ℚ) : ℝ) := rfl

/-- Exact bounds needed by every source no-valley class, independently of
the numerical margin certificates. -/
theorem e6_row_bounds {p : Nat} (hp : p < 55) :
    1 / 4 ≤ Checks.rowQa p ∧ Checks.rowQa p ≤ Checks.rowQb p ∧
    Checks.rowQb p ≤ 7 / 10 ∧
    0 ≤ ((pieceV22 p).theta : ℝ) ∧ ((pieceV22 p).theta : ℝ) ≤ 1 ∧
    0 < ((pieceV22 p).D : ℝ) ∧ 0 < Checks.rowEll0 p ∧
    19 ≤ startingMean p ∧ startingMean p ≤ 50 ∧
    0 < ((V21.m25.getD p 0 : ℚ) : ℝ) ∧
    ((V21.m25.getD p 0 : ℚ) : ℝ) ≤ 136 / 9 ∧
    ((V21.m25.getD p 0 : ℚ) : ℝ) ≤ startingMean p := by
  obtain ⟨_, _, hqa, hab, hqb, hth0, hth1, hD, hell, hm0, hm1,
    hf0, hf1, hfm⟩ := e6_table_boundsQ p hp
  rw [e6_rowQa_cast, e6_rowQb_cast]
  unfold Checks.rowEll0 startingMean
  exact ⟨by have hh := (Rat.cast_le (K := ℝ)).2 hqa; norm_num at hh; exact hh, by exact_mod_cast hab, by have hh := (Rat.cast_le (K := ℝ)).2 hqb; norm_num at hh; exact hh,
    by exact_mod_cast hth0, by exact_mod_cast hth1, by exact_mod_cast hD,
    by exact_mod_cast hell, by exact_mod_cast hm0, by exact_mod_cast hm1,
    by exact_mod_cast hf0, by have hh := (Rat.cast_le (K := ℝ)).2 hf1; norm_num at hh; exact hh, by exact_mod_cast hfm⟩

theorem e6_startingMean_bounds {p : Nat} (hp : p < 55) :
    19 ≤ startingMean p ∧ startingMean p ≤ 50 := by
  obtain ⟨_, _, _, _, _, _, _, h0, h1, _⟩ := e6_row_bounds hp
  exact ⟨h0, h1⟩

/-- The actual q lies inside the exact endpoint q interval of its retained
piece; `pieceOf` keeps its original left-piece convention at shared edges. -/
theorem e6_q_bounds {t : ℝ} (ht : InRange t) :
    Checks.rowQa (pieceOf t) ≤ actQ t ∧ actQ t ≤ Checks.rowQb (pieceOf t) := by
  obtain ⟨hp, _, hlo, hhi⟩ := pieceOf_spec ht
  have hpos : 0 < loR (pieceOf t) := by
    have h := (e6_table_boundsQ (pieceOf t) hp).1
    change 0 < ((pieceV22 (pieceOf t)).lamLo : ℝ)
    exact_mod_cast h
  have htpos : 0 < t := lt_of_lt_of_le hpos hlo
  constructor
  · exact Atlas.actQ_le_actQ hpos.le hlo
  · exact Atlas.actQ_le_actQ htpos.le hhi

theorem e6_q_domain {t : ℝ} (ht : InRange t) :
    1 / 4 ≤ actQ t ∧ actQ t ≤ 7 / 10 ∧ 0 < actQ t ∧ actQ t < 1 := by
  have hp := (pieceOf_spec ht).1
  obtain ⟨hqa, _, hqb, _⟩ := e6_row_bounds hp
  obtain ⟨hlo, hhi⟩ := e6_q_bounds ht
  have h0 := hqa.trans hlo
  have h1 := hhi.trans hqb
  exact ⟨h0, h1, by linarith, by linarith⟩

theorem e6_handCap_le {t : ℝ} (ht : InRange t) :
    HandVariance.handCap t ≤ ((pieceV22 (pieceOf t)).D : ℝ) := by
  obtain ⟨hp, _, hlo, hhi⟩ := pieceOf_spec ht
  exact V21.handCap_le_dCaps hp hlo hhi

theorem e6_abs_skew_le_rowRhi {t : ℝ} (ht : InRange t) :
    |2 * actQ t - 1| ≤ Checks.rowRhi (pieceOf t) := by
  obtain ⟨hlo, hhi⟩ := e6_q_bounds ht
  have ha := neg_abs_le (2 * Checks.rowQa (pieceOf t) - 1)
  have hb := le_abs_self (2 * Checks.rowQb (pieceOf t) - 1)
  have hma := le_max_left |2 * Checks.rowQa (pieceOf t) - 1|
    |2 * Checks.rowQb (pieceOf t) - 1|
  have hmb := le_max_right |2 * Checks.rowQa (pieceOf t) - 1|
    |2 * Checks.rowQb (pieceOf t) - 1|
  unfold Checks.rowRhi
  apply abs_le.mpr
  constructor <;> linarith

theorem e6_rowRhi_bounds {p : Nat} (hp : p < 55) :
    0 ≤ Checks.rowRhi p ∧ Checks.rowRhi p ≤ 1 / 2 := by
  obtain ⟨ha, hab, hb, _⟩ := e6_row_bounds hp
  have ha' : |2 * Checks.rowQa p - 1| ≤ 1 / 2 := by
    apply abs_le.mpr
    constructor <;> linarith
  have hb' : |2 * Checks.rowQb p - 1| ≤ 1 / 2 := by
    apply abs_le.mpr
    constructor <;> linarith
  unfold Checks.rowRhi
  exact ⟨(abs_nonneg _).trans (le_max_left _ _), max_le ha' hb'⟩

theorem e6_rowVmin_pos {p : Nat} (hp : p < 55) : 0 < Checks.rowVmin p := by
  obtain ⟨ha, hab, hb, _⟩ := e6_row_bounds hp
  unfold Checks.rowVmin
  apply lt_min
  · exact mul_pos (by linarith) (by linarith)
  · exact mul_pos (by linarith) (by linarith)

theorem e6_rowVmin_le_actual {t : ℝ} (ht : InRange t) :
    Checks.rowVmin (pieceOf t) ≤ actQ t * (1 - actQ t) := by
  obtain ⟨hlo, hhi⟩ := e6_q_bounds ht
  unfold Checks.rowVmin
  by_cases hq : actQ t ≤ 1 / 2
  · have hp : 0 ≤ (actQ t - Checks.rowQa (pieceOf t)) *
        (1 - actQ t - Checks.rowQa (pieceOf t)) :=
      mul_nonneg (by linarith) (by linarith)
    exact (min_le_left _ _).trans (by nlinarith :
      Checks.rowQa (pieceOf t) * (1 - Checks.rowQa (pieceOf t)) ≤
        actQ t * (1 - actQ t))
  · have hp : 0 ≤ (Checks.rowQb (pieceOf t) - actQ t) *
        (Checks.rowQb (pieceOf t) + actQ t - 1) :=
      mul_nonneg (by linarith) (by linarith)
    exact (min_le_right _ _).trans (by nlinarith :
      Checks.rowQb (pieceOf t) * (1 - Checks.rowQb (pieceOf t)) ≤
        actQ t * (1 - actQ t))

/-- The inherited zero tilt is exactly the row used by Section 5.3. -/
theorem e6_zero_tilt_mem (p : Nat) :
    ((0 : ℝ), Checks.rowEll0 p) ∈ castTilts (pieceV22 p).tilts := by
  unfold castTilts
  apply List.mem_map.mpr
  refine ⟨(0, ((N44.Data.rates44.getD p []).getD 0 0)), ?_, ?_⟩
  · change (0, ((N44.Data.rates44.getD p []).getD 0 0)) ∈ MGF.tiltsQ44 p
    unfold MGF.tiltsQ44
    apply List.mem_map.mpr
    refine ⟨0, by simp, ?_⟩
    simp [Atlas.tvals]
  · simp [e6_rowEll0_eq]

theorem e6_zero_mgf_mem (t mu : ℝ) :
    (1 - actQ t, Real.exp (-Checks.rowEll0 (pieceOf t) * mu)) ∈
      mgfRows (MGF.tilts44R t) (actQ t) mu := by
  rw [e6_tilts_eq]
  unfold mgfRows
  apply List.mem_map.mpr
  refine ⟨(0, Checks.rowEll0 (pieceOf t)), e6_zero_tilt_mem _, ?_⟩
  simp [neg_mul]

theorem e6_zero_mgf_bound {ι : Type} (X : Mixture ι) (t mu : ℝ)
    (hrows : ∀ r ∈ mgfRows (MGF.tilts44R t) (actQ t) mu,
      X.expect (fun M _ => r.1 ^ M) ≤ r.2) :
    X.expect (fun M _ => (1 - actQ t) ^ M) ≤
      Real.exp (-Checks.rowEll0 (pieceOf t) * mu) :=
  hrows _ (e6_zero_mgf_mem t mu)

theorem e6_central_domain {t : ℝ} (ht : InRange t)
    (hc : E6CentralPiece (pieceOf t)) :
    classForPiece (pieceOf t) = none ∧ wingForPiece (pieceOf t) = none ∧
    excess (pieceOf t) = 0 ∧ spikeCutoff (pieceOf t) = 3 / 5 ∧
    |2 * actQ t - 1| ≤ 1 / 4 ∧
    ((pieceV22 (pieceOf t)).theta : ℝ) ≤ 7 / 10 ∧
    ((pieceV22 (pieceOf t)).D : ℝ) = 6 / 5 ∧
    19 ≤ startingMean (pieceOf t) := by
  have hp := (pieceOf_spec ht).1
  obtain ⟨hn, hw, ha, hb, hth, hD⟩ := e6_central_tableQ _ hp hc
  have ha' : 3 / 8 ≤ Checks.rowQa (pieceOf t) := by
    rw [e6_rowQa_cast]
    have hh := (Rat.cast_le (K := ℝ)).2 ha
    norm_num at hh
    exact hh
  have hb' : Checks.rowQb (pieceOf t) ≤ 5 / 8 := by
    rw [e6_rowQb_cast]
    have hh := (Rat.cast_le (K := ℝ)).2 hb
    norm_num at hh
    exact hh
  obtain ⟨hqlo, hqhi⟩ := e6_q_bounds ht
  refine ⟨hn, hw, by simp [excess, hn], by simp [spikeCutoff, hn, hw],
    ?_, by have hh := (Rat.cast_le (K := ℝ)).2 hth; norm_num at hh; exact hh,
    by
      have hh : ((pieceV22 (pieceOf t)).D : ℝ) = ((6 / 5 : ℚ) : ℝ) := Rat.cast_inj.mpr hD
      norm_num at hh
      exact hh,
    (e6_startingMean_bounds hp).1⟩
  apply abs_le.mpr
  constructor <;> linarith

/-- The exact wing class of the actual piece, with actual skew and mean.
This keeps its table identity and its original spike cutoff. -/
theorem e6_wing_domain {t : ℝ} (ht : InRange t)
    (hw : E6WingPiece (pieceOf t)) :
    ∃ c ∈ wingClasses, wingForPiece (pieceOf t) = some c ∧
      pieceOf t ∈ c.iotas ∧ classForPiece (pieceOf t) = none ∧
      (c.ra : ℝ) ≤ |2 * actQ t - 1| ∧ |2 * actQ t - 1| ≤ (c.rb : ℝ) ∧
      (c.muW : ℝ) ≤ startingMean (pieceOf t) ∧
      excess (pieceOf t) = 0 ∧ spikeCutoff (pieceOf t) = (c.tau : ℝ) ∧
      0 < (c.ra : ℝ) ∧ (c.rb : ℝ) ≤ 1 / 4 ∧
      0 < (c.tau : ℝ) ∧ (c.tau : ℝ) ≤ 3 / 5 := by
  have hp := (pieceOf_spec ht).1
  have h := e6_wing_tableQ _ hp hw
  unfold e6WingTableQ at h
  cases he : wingForPiece (pieceOf t) with
  | none => simp [he] at h
  | some c =>
    simp only [he] at h
    obtain ⟨hc, hpi, hn, ha, hb, hm, hra, _, hrb, hta, htb⟩ := h
    have ha' : (c.ra : ℝ) ≤ 2 * Checks.rowQa (pieceOf t) - 1 := by
      rw [e6_rowQa_cast]; exact_mod_cast ha
    have hb' : 2 * Checks.rowQb (pieceOf t) - 1 ≤ (c.rb : ℝ) := by
      rw [e6_rowQb_cast]; exact_mod_cast hb
    have hra' : 0 < (c.ra : ℝ) := by exact_mod_cast hra
    have hm' : (c.muW : ℝ) ≤ startingMean (pieceOf t) := by
      change (c.muW : ℝ) ≤ ((mu0Data.getD (pieceOf t) 0 : ℚ) : ℝ)
      exact_mod_cast hm
    obtain ⟨hqlo, hqhi⟩ := e6_q_bounds ht
    have hs : 0 ≤ 2 * actQ t - 1 := by linarith
    rw [abs_of_nonneg hs]
    exact ⟨c, hc, rfl, hpi, hn, by linarith, by linarith,
      hm', by simp [excess, hn],
      by simp [spikeCutoff, hn, he], hra', by have hh := (Rat.cast_le (K := ℝ)).2 hrb; norm_num at hh; exact hh,
      by exact_mod_cast hta, by have hh := (Rat.cast_le (K := ℝ)).2 htb; norm_num at hh; exact hh⟩

/-- The outer table class encloses the absolute skew at every point of its
closed inherited activity interval. No endpoint rounding enters this bridge. -/
theorem e6_outer_domain {t : ℝ} (ht : InRange t)
    (ho : E6OuterPiece (pieceOf t)) :
    ∃ c ∈ classes, classForPiece (pieceOf t) = some c ∧ pieceOf t ∈ c.iotas ∧
      (c.ra : ℝ) ≤ |2 * actQ t - 1| ∧ |2 * actQ t - 1| ≤ (c.rb : ℝ) ∧
      (c.muD : ℝ) ≤ startingMean (pieceOf t) ∧
      excess (pieceOf t) = (c.b : ℝ) ∧ spikeCutoff (pieceOf t) = (c.tau : ℝ) ∧
      0 ≤ (c.ra : ℝ) ∧ (c.rb : ℝ) ≤ 1 / 2 ∧
      0 ≤ (c.b : ℝ) ∧ (c.b : ℝ) ≤ 1 ∧ 0 ≤ (c.beta : ℝ) ∧
      0 < (c.tau : ℝ) ∧ (c.tau : ℝ) < 1 ∧ 1 < (c.thi : ℝ) := by
  have hp := (pieceOf_spec ht).1
  have h := e6_outer_tableQ _ hp ho
  unfold e6OuterTableQ at h
  cases he : classForPiece (pieceOf t) with
  | none => simp [he] at h
  | some c =>
    simp only [he] at h
    obtain ⟨hc, hpi, hsign, ha, hb, hm, hra, _, hrb, hb0, hb1, hbeta,
      hta, htb, hthi⟩ := h
    have ha' : (c.ra : ℝ) ≤ min |2 * Checks.rowQa (pieceOf t) - 1|
        |2 * Checks.rowQb (pieceOf t) - 1| := by
      rw [e6_rowQa_cast, e6_rowQb_cast]; exact_mod_cast ha
    have hb' : Checks.rowRhi (pieceOf t) ≤ (c.rb : ℝ) := by
      unfold Checks.rowRhi
      rw [e6_rowQa_cast, e6_rowQb_cast]; exact_mod_cast hb
    have hm' : (c.muD : ℝ) ≤ startingMean (pieceOf t) := by
      change (c.muD : ℝ) ≤ ((mu0Data.getD (pieceOf t) 0 : ℚ) : ℝ)
      exact_mod_cast hm
    obtain ⟨hqlo, hqhi⟩ := e6_q_bounds ht
    have halower : (c.ra : ℝ) ≤ |2 * actQ t - 1| := by
      rcases hsign with hneg | hpos
      · have hneg' : Checks.rowQb (pieceOf t) ≤ 1 / 2 := by
          rw [e6_rowQb_cast]
          have hh := (Rat.cast_le (K := ℝ)).2 hneg
          norm_num at hh
          exact hh
        have hab := ha'.trans (min_le_right _ _)
        rw [abs_of_nonpos (by linarith : 2 * Checks.rowQb (pieceOf t) - 1 ≤ 0)] at hab
        rw [abs_of_nonpos (by linarith : 2 * actQ t - 1 ≤ 0)]
        linarith
      · have hpos' : 1 / 2 ≤ Checks.rowQa (pieceOf t) := by
          rw [e6_rowQa_cast]
          have hh := (Rat.cast_le (K := ℝ)).2 hpos
          norm_num at hh
          exact hh
        have hab := ha'.trans (min_le_left _ _)
        rw [abs_of_nonneg (by linarith : 0 ≤ 2 * Checks.rowQa (pieceOf t) - 1)] at hab
        rw [abs_of_nonneg (by linarith : 0 ≤ 2 * actQ t - 1)]
        linarith
    exact ⟨c, hc, rfl, hpi, halower, (e6_abs_skew_le_rowRhi ht).trans hb',
      hm', by simp [excess, he], by simp [spikeCutoff, he],
      by exact_mod_cast hra, by have hh := (Rat.cast_le (K := ℝ)).2 hrb; norm_num at hh; exact hh, by exact_mod_cast hb0,
      by exact_mod_cast hb1, by exact_mod_cast hbeta, by exact_mod_cast hta,
      by exact_mod_cast htb, by exact_mod_cast hthi⟩

/-- Native O2/O1/MGF inputs imply the identical inherited row inputs used
by the three Section 5 consumers. No probability or history is discarded. -/
theorem e6_profile_inputs {ι : Type} (X : Mixture ι) {t mu : ℝ} {k : ℤ}
    (ht : InRange t) (hmu : startingMean (pieceOf t) ≤ mu)
    (hO2 : X.expect (fun M Y => delta (actQ t) k M Y ^ 2) ≤
      P44.θb t * (actQ t * (1 - actQ t)) * mu)
    (hO1 : X.varM ≤ HandVariance.handCap t * mu)
    (hrows : ∀ r ∈ mgfRows (MGF.tilts44R t) (actQ t) mu,
      X.expect (fun M _ => r.1 ^ M) ≤ r.2) :
    X.expect (fun M Y => delta (actQ t) k M Y ^ 2) ≤
      ((pieceV22 (pieceOf t)).theta : ℝ) * (actQ t * (1 - actQ t)) * mu ∧
    X.varM ≤ ((pieceV22 (pieceOf t)).D : ℝ) * mu ∧
    X.expect (fun M _ => (1 - actQ t) ^ M) ≤
      Real.exp (-Checks.rowEll0 (pieceOf t) * mu) := by
  have hp := (pieceOf_spec ht).1
  have hm0 : 0 ≤ mu := by
    have hstart := (e6_startingMean_bounds hp).1
    linarith
  exact ⟨by simpa only [e6_theta_eq] using hO2,
    hO1.trans (mul_le_mul_of_nonneg_right (e6_handCap_le ht) hm0),
    e6_zero_mgf_bound X t mu hrows⟩

end

end Analysis
end Erdos993Lean.Analytic.V22
