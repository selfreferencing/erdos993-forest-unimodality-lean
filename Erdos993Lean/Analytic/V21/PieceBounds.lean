import Erdos993Lean.Analytic.V21.Pieces
import Erdos993Lean.Analytic.HandVariance.Defs
import Erdos993Lean.Analytic.N44.Pieces
import Erdos993Lean.Analytic.MGF.N25.Data

/-!
# Paper v2.1 Theorem 5.8(a): the checked rectangle caps contain the hand cap

Source: supplement/twin_v2.1_data.txt, Part 1, and the hand cap in
s4_part_a.tex, equation p2:eq:Dhat.
The actual activity and its containing subinterval are retained. At shared
activity edges, the lesser hand cap applies, whereas the subinterval's stored
cap is an upper bound on its entire closed rectangle. No scalar selects or
reconstructs a forest object.
-/

namespace Erdos993Lean.Analytic.V21

open Erdos993Lean.Analytic.N44

/-- Paper v2.1 Theorem 4.43 and Lemma 5.4: the saved lower-edge table is exactly
the already verified window-only order-25 floor table. Kernel evaluation. -/
theorem m25_eq_window25 : m25 = MGF.N25.Data.mmin25 := by
  decide +kernel

/-- Paper v2.1 Lemma 5.4: all requested lower mean edges are positive. -/
theorem m25_pos : ∀ p < 55, 0 < m25.getD p 0 := by
  decide +kernel

/-- Source: s4_part_a.tex, p2:eq:Dhat, with the same closed-endpoint convention
as a rational function for the finite edge comparison. -/
def handCapQ (lam : ℚ) : ℚ :=
  if lam ≤ 263/200 then 6/5
  else if lam ≤ 3/2 then 7/5
  else if lam ≤ 7/4 then 8/5
  else if lam ≤ 2 then 9/5
  else 21/10

/-- Source: p2:eq:Dhat; exact cast of the rational hand cap. -/
theorem handCapQ_cast (lam : ℚ) :
    HandVariance.handCap (lam : ℝ) = ((handCapQ lam : ℚ) : ℝ) := by
  have h1 : ((lam : ℝ) ≤ 263/200) ↔ lam ≤ (263/200 : ℚ) := by
    convert (Rat.cast_le (K := ℝ) (p := lam) (q := 263/200)) using 1 <;> norm_num
  have h2 : ((lam : ℝ) ≤ 3/2) ↔ lam ≤ (3/2 : ℚ) := by
    convert (Rat.cast_le (K := ℝ) (p := lam) (q := 3/2)) using 1 <;> norm_num
  have h3 : ((lam : ℝ) ≤ 7/4) ↔ lam ≤ (7/4 : ℚ) := by
    convert (Rat.cast_le (K := ℝ) (p := lam) (q := 7/4)) using 1 <;> norm_num
  have h4 : ((lam : ℝ) ≤ 2) ↔ lam ≤ (2 : ℚ) := by norm_cast
  simp only [HandVariance.handCap, handCapQ, h1, h2, h3, h4]
  split_ifs <;> norm_num

/-- Source: p2:eq:Dhat; the hand cap is monotone on the retained activity. -/
theorem handCap_mono {t u : ℝ} (htu : t ≤ u) :
    HandVariance.handCap t ≤ HandVariance.handCap u := by
  unfold HandVariance.handCap
  split_ifs <;> norm_num <;> linarith

/-- Paper v2.1 Lemma 5.4: the cap at every closed upper activity edge is at
most the corresponding checked cap. Exact kernel evaluation on 55 rows. -/
theorem handCapQ_hi_le : ∀ p < 55,
    handCapQ (N44.Data.pieceHi.getD p 0) ≤ dCaps.getD p 0 := by
  decide +kernel

/-- Paper v2.1 Theorem 5.8(a): on each closed subinterval the hand cap is no
greater than the cap at which its boxes are checked. -/
theorem handCap_le_dCaps {p : ℕ} (hp : p < 55) {t : ℝ}
    (hlo : loR p ≤ t) (hhi : t ≤ hiR p) :
    HandVariance.handCap t ≤ ((dCaps.getD p 0 : ℚ) : ℝ) := by
  have hmono := handCap_mono hhi
  unfold hiR at hmono
  rw [handCapQ_cast] at hmono
  exact hmono.trans (by exact_mod_cast handCapQ_hi_le p hp)

end Erdos993Lean.Analytic.V21
