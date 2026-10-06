import Erdos993Lean.Analytic.V22.Analysis.WindowClassTransfer
import Erdos993Lean.Analytic.V22.Analysis.LargeTFiber
import Erdos993Lean.Analytic.V22.Analysis.Symmetry
import Erdos993Lean.Analytic.V22.Analysis.FiberInfimum
import Erdos993Lean.Analytic.V22.Analysis.E6ProfileDomains

/-! Source: frozen note Theorem 5.14. The finite premises are exactly
Lemma 7.11 and Lemmas 7.16--7.20. The class, all real means above its
starting mean, the original activity cutoff, and every integer atom survive.
The actual fiber infimum is attained over the full integer domain.
Parent owns Lean verification. -/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

deriving instance DecidableEq for V22.V22Cell

-- Exact literal views keep the generated private q wrapper out of
-- real-coercion normalization. These identities change no finite data.
private def windowClassesLiteral : List V22.V22Class := [
  ⟨1, "C1", (3793 / 10000 : ℚ), (1 / 2 : ℚ), (2 / 5 : ℚ), (0 / 1 : ℚ), (3 / 5 : ℚ), (17 / 10 : ℚ), (45 / 1 : ℚ), [0, 1, 2]⟩,
  ⟨2, "C2", (1 / 4 : ℚ), (1897 / 5000 : ℚ), (2 / 5 : ℚ), (0 / 1 : ℚ), (69 / 100 : ℚ), (17 / 10 : ℚ), (50 / 1 : ℚ), [3, 4, 5]⟩,
  ⟨3, "C3", (833 / 5000 : ℚ), (2309 / 10000 : ℚ), (0 / 1 : ℚ), (1 / 2 : ℚ), (11 / 25 : ℚ), (7 / 4 : ℚ), (50 / 1 : ℚ), [40, 41, 42, 43]⟩,
  ⟨4, "C4", (2307 / 10000 : ℚ), (341 / 1250 : ℚ), (3 / 20 : ℚ), (3 / 10 : ℚ), (21 / 50 : ℚ), (9 / 5 : ℚ), (40 / 1 : ℚ), [44, 45, 46]⟩,
  ⟨5, "C5", (2727 / 10000 : ℚ), (194 / 625 : ℚ), (3 / 10 : ℚ), (0 / 1 : ℚ), (2 / 5 : ℚ), (17 / 10 : ℚ), (50 / 1 : ℚ), [47, 48, 49]⟩,
  ⟨6, "C6", (3103 / 10000 : ℚ), (861 / 2500 : ℚ), (3 / 10 : ℚ), (0 / 1 : ℚ), (9 / 25 : ℚ), (17 / 10 : ℚ), (50 / 1 : ℚ), [50, 51, 52]⟩,
  ⟨7, "C7", (1721 / 5000 : ℚ), (3847 / 10000 : ℚ), (3 / 10 : ℚ), (1 / 1 : ℚ), (33 / 100 : ℚ), (19 / 10 : ℚ), (50 / 1 : ℚ), [53]⟩,
  ⟨8, "C8", (1923 / 5000 : ℚ), (2 / 5 : ℚ), (3 / 10 : ℚ), (1 / 1 : ℚ), (3 / 10 : ℚ), (19 / 10 : ℚ), (50 / 1 : ℚ), [54]⟩
]

private theorem windowClasses_literal_eq : V22.classes = windowClassesLiteral := by decide +kernel

private def windowCellsLiteral : List V22.V22Cell := [
  ⟨1, (3 / 5 : ℚ), (749 / 1000 : ℚ)⟩,
  ⟨1, (749 / 1000 : ℚ), (167 / 200 : ℚ)⟩,
  ⟨1, (167 / 200 : ℚ), (201 / 200 : ℚ)⟩,
  ⟨1, (201 / 200 : ℚ), (1263 / 1000 : ℚ)⟩,
  ⟨1, (1263 / 1000 : ℚ), (1597 / 1000 : ℚ)⟩,
  ⟨1, (1597 / 1000 : ℚ), (17 / 10 : ℚ)⟩,
  ⟨2, (69 / 100 : ℚ), (797 / 1000 : ℚ)⟩,
  ⟨2, (797 / 1000 : ℚ), (881 / 1000 : ℚ)⟩,
  ⟨2, (881 / 1000 : ℚ), (263 / 250 : ℚ)⟩,
  ⟨2, (263 / 250 : ℚ), (627 / 500 : ℚ)⟩,
  ⟨2, (627 / 500 : ℚ), (757 / 500 : ℚ)⟩,
  ⟨2, (757 / 500 : ℚ), (17 / 10 : ℚ)⟩,
  ⟨3, (11 / 25 : ℚ), (97 / 200 : ℚ)⟩,
  ⟨3, (97 / 200 : ℚ), (591 / 1000 : ℚ)⟩,
  ⟨3, (591 / 1000 : ℚ), (209 / 250 : ℚ)⟩,
  ⟨3, (209 / 250 : ℚ), (1069 / 1000 : ℚ)⟩,
  ⟨3, (1069 / 1000 : ℚ), (159 / 125 : ℚ)⟩,
  ⟨3, (159 / 125 : ℚ), (37 / 25 : ℚ)⟩,
  ⟨3, (37 / 25 : ℚ), (7 / 4 : ℚ)⟩,
  ⟨4, (21 / 50 : ℚ), (9 / 20 : ℚ)⟩,
  ⟨4, (9 / 20 : ℚ), (53 / 100 : ℚ)⟩,
  ⟨4, (53 / 100 : ℚ), (94 / 125 : ℚ)⟩,
  ⟨4, (94 / 125 : ℚ), (89 / 100 : ℚ)⟩,
  ⟨4, (89 / 100 : ℚ), (567 / 500 : ℚ)⟩,
  ⟨4, (567 / 500 : ℚ), (169 / 125 : ℚ)⟩,
  ⟨4, (169 / 125 : ℚ), (13 / 8 : ℚ)⟩,
  ⟨4, (13 / 8 : ℚ), (9 / 5 : ℚ)⟩,
  ⟨5, (2 / 5 : ℚ), (59 / 125 : ℚ)⟩,
  ⟨5, (59 / 125 : ℚ), (91 / 125 : ℚ)⟩,
  ⟨5, (91 / 125 : ℚ), (847 / 1000 : ℚ)⟩,
  ⟨5, (847 / 1000 : ℚ), (287 / 250 : ℚ)⟩,
  ⟨5, (287 / 250 : ℚ), (184 / 125 : ℚ)⟩,
  ⟨5, (184 / 125 : ℚ), (17 / 10 : ℚ)⟩,
  ⟨6, (9 / 25 : ℚ), (391 / 1000 : ℚ)⟩,
  ⟨6, (391 / 1000 : ℚ), (519 / 1000 : ℚ)⟩,
  ⟨6, (519 / 1000 : ℚ), (153 / 200 : ℚ)⟩,
  ⟨6, (153 / 200 : ℚ), (959 / 1000 : ℚ)⟩,
  ⟨6, (959 / 1000 : ℚ), (1307 / 1000 : ℚ)⟩,
  ⟨6, (1307 / 1000 : ℚ), (17 / 10 : ℚ)⟩,
  ⟨7, (33 / 100 : ℚ), (181 / 500 : ℚ)⟩,
  ⟨7, (181 / 500 : ℚ), (247 / 500 : ℚ)⟩,
  ⟨7, (247 / 500 : ℚ), (787 / 1000 : ℚ)⟩,
  ⟨7, (787 / 1000 : ℚ), (1027 / 1000 : ℚ)⟩,
  ⟨7, (1027 / 1000 : ℚ), (1279 / 1000 : ℚ)⟩,
  ⟨7, (1279 / 1000 : ℚ), (1533 / 1000 : ℚ)⟩,
  ⟨7, (1533 / 1000 : ℚ), (1881 / 1000 : ℚ)⟩,
  ⟨7, (1881 / 1000 : ℚ), (19 / 10 : ℚ)⟩,
  ⟨8, (3 / 10 : ℚ), (161 / 500 : ℚ)⟩,
  ⟨8, (161 / 500 : ℚ), (83 / 200 : ℚ)⟩,
  ⟨8, (83 / 200 : ℚ), (763 / 1000 : ℚ)⟩,
  ⟨8, (763 / 1000 : ℚ), (201 / 200 : ℚ)⟩,
  ⟨8, (201 / 200 : ℚ), (257 / 200 : ℚ)⟩,
  ⟨8, (257 / 200 : ℚ), (313 / 200 : ℚ)⟩,
  ⟨8, (313 / 200 : ℚ), (19 / 10 : ℚ)⟩
]

private theorem windowCells_literal_eq : V22.windowCells = windowCellsLiteral := by decide +kernel

theorem window_class_domains {c : V22.V22Class} (hc : c ∈ V22.classes) :
    0 < (c.ra : ℝ) ∧ (c.rb : ℝ) ≤ 1 / 2 ∧ 0 ≤ (c.b : ℝ) ∧ (c.b : ℝ) ≤ 1 ∧
    0 ≤ (c.beta : ℝ) ∧ (c.beta : ℝ) ≤ 1 ∧ 0 < (c.tau : ℝ) ∧ (c.tau : ℝ) < 1 ∧
    (8 / 5 : ℝ) ≤ c.thi ∧ (c.tau : ℝ) ≤ c.thi ∧ 40 ≤ (c.muD : ℝ) ∧
    17 ≤ (c.muD : ℝ) * (c.tau : ℝ) + 2 ∧ 10 + (c.beta : ℝ) ≤ 9 * (c.thi : ℝ) := by
  rw [windowClasses_literal_eq] at hc
  simp only [windowClassesLiteral, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem window_class_target_antitone {c : V22.V22Class} (hc : c ∈ V22.classes)
    {t : ℝ} (ht : (c.thi : ℝ) ≤ t) : V22.Checks.classTarget c t ≤ V22.Checks.classTarget c c.thi := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hbeta⟩ := window_class_domains hc
  have hprod := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht)
    (show 10 + (c.beta : ℝ) - (9 / 2) * (t + (c.thi : ℝ)) ≤ 0 from by linarith)
  unfold V22.Checks.classTarget V22.psi
  nlinarith

theorem window_size_scaling {M : ℕ} {mu Na : ℝ} (hmu : 0 < mu)
    (ha : 10 ≤ Na) (haN : Na ≤ (M : ℝ) + 2) :
    (M : ℝ) / mu ≤ ((M : ℝ) + 2) / mu ∧
    ((M : ℝ) + 2) / mu ≤ ((M : ℝ) / mu) * Na / (Na - 2) := by
  constructor
  · exact div_le_div_of_nonneg_right (by linarith) hmu.le
  · apply (le_div_iff₀ (show 0 < Na - 2 from by linarith)).2
    have hidL : (((M : ℝ) + 2) / mu) * (Na - 2) = (((M : ℝ) + 2) * (Na - 2)) / mu := by ring
    have hidR : ((M : ℝ) / mu) * Na = ((M : ℝ) * Na) / mu := by ring
    rw [hidL, hidR]
    exact div_le_div_of_nonneg_right (by nlinarith) hmu.le

theorem window_target_scaled {target t B Na X : ℝ} (ht : 0 < t) (ha : 2 < Na)
    (hB : 0 < B) (htB : t ≤ B) (hBmax : B ≤ t * Na / (Na - 2))
    (hpos : 0 < target → target / t ≤ X)
    (hneg : target ≤ 0 → target * (Na - 2) / (t * Na) ≤ X) : target ≤ B * X := by
  by_cases hp : 0 < target
  · have hx := hpos hp
    have hx0 : 0 ≤ X := (div_pos hp ht).le.trans hx
    have htarget := (div_le_iff₀ ht).1 hx
    have hmul := mul_le_mul_of_nonneg_right htB hx0
    nlinarith
  · have hn : target ≤ 0 := by linarith
    have hx := hneg hn
    have hreq0 : target * (Na - 2) / (t * Na) ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hn (by linarith)) (by positivity)
    have hmul := mul_le_mul_of_nonpos_right hBmax hreq0
    have hid : (t * Na / (Na - 2)) * (target * (Na - 2) / (t * Na)) = target := by
      field_simp [ht.ne', (show 0 < Na from by linarith).ne', (show 0 < Na - 2 from by linarith).ne']
    rw [hid] at hmul
    exact hmul.trans (mul_le_mul_of_nonneg_left hx hB.le)

-- Exact class-cell cover is inserted below from the verbatim rational data.

set_option maxHeartbeats 1000000 in
/-- Every exact Table 1 class interval is covered, including all endpoints.
This is a rational list-cover theorem, not an additional finite premise. -/
theorem window_cells_cover {c : V22.V22Class} (hc : c ∈ V22.classes)
    {t : ℝ} (ht0 : (c.tau : ℝ) ≤ t) (ht1 : t ≤ (c.thi : ℝ)) :
    ∃ cell ∈ V22.windowCells, cell.classId = c.classId ∧
      (c.tau : ℝ) ≤ cell.lo ∧ (cell.lo : ℝ) ≤ t ∧ t ≤ cell.hi := by
  rw [windowClasses_literal_eq] at hc
  simp only [windowClassesLiteral, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num at ht0 ht1
    by_cases h0 : t ≤ (749 / 1000 : ℝ)
    · refine ⟨⟨1, (3 / 5 : ℚ), (749 / 1000 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨ht0, h0⟩
    by_cases h1 : t ≤ (167 / 200 : ℝ)
    · refine ⟨⟨1, (749 / 1000 : ℚ), (167 / 200 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h0).le, h1⟩
    by_cases h2 : t ≤ (201 / 200 : ℝ)
    · refine ⟨⟨1, (167 / 200 : ℚ), (201 / 200 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h1).le, h2⟩
    by_cases h3 : t ≤ (1263 / 1000 : ℝ)
    · refine ⟨⟨1, (201 / 200 : ℚ), (1263 / 1000 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h2).le, h3⟩
    by_cases h4 : t ≤ (1597 / 1000 : ℝ)
    · refine ⟨⟨1, (1263 / 1000 : ℚ), (1597 / 1000 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h3).le, h4⟩
    refine ⟨⟨1, (1597 / 1000 : ℚ), (17 / 10 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
    norm_num
    exact ⟨(lt_of_not_ge h4).le, ht1⟩
  · norm_num at ht0 ht1
    by_cases h0 : t ≤ (797 / 1000 : ℝ)
    · refine ⟨⟨2, (69 / 100 : ℚ), (797 / 1000 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨ht0, h0⟩
    by_cases h1 : t ≤ (881 / 1000 : ℝ)
    · refine ⟨⟨2, (797 / 1000 : ℚ), (881 / 1000 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h0).le, h1⟩
    by_cases h2 : t ≤ (263 / 250 : ℝ)
    · refine ⟨⟨2, (881 / 1000 : ℚ), (263 / 250 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h1).le, h2⟩
    by_cases h3 : t ≤ (627 / 500 : ℝ)
    · refine ⟨⟨2, (263 / 250 : ℚ), (627 / 500 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h2).le, h3⟩
    by_cases h4 : t ≤ (757 / 500 : ℝ)
    · refine ⟨⟨2, (627 / 500 : ℚ), (757 / 500 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h3).le, h4⟩
    refine ⟨⟨2, (757 / 500 : ℚ), (17 / 10 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
    norm_num
    exact ⟨(lt_of_not_ge h4).le, ht1⟩
  · norm_num at ht0 ht1
    by_cases h0 : t ≤ (97 / 200 : ℝ)
    · refine ⟨⟨3, (11 / 25 : ℚ), (97 / 200 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨ht0, h0⟩
    by_cases h1 : t ≤ (591 / 1000 : ℝ)
    · refine ⟨⟨3, (97 / 200 : ℚ), (591 / 1000 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h0).le, h1⟩
    by_cases h2 : t ≤ (209 / 250 : ℝ)
    · refine ⟨⟨3, (591 / 1000 : ℚ), (209 / 250 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h1).le, h2⟩
    by_cases h3 : t ≤ (1069 / 1000 : ℝ)
    · refine ⟨⟨3, (209 / 250 : ℚ), (1069 / 1000 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h2).le, h3⟩
    by_cases h4 : t ≤ (159 / 125 : ℝ)
    · refine ⟨⟨3, (1069 / 1000 : ℚ), (159 / 125 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h3).le, h4⟩
    by_cases h5 : t ≤ (37 / 25 : ℝ)
    · refine ⟨⟨3, (159 / 125 : ℚ), (37 / 25 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h4).le, h5⟩
    refine ⟨⟨3, (37 / 25 : ℚ), (7 / 4 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
    norm_num
    exact ⟨(lt_of_not_ge h5).le, ht1⟩


  · norm_num at ht0 ht1
    by_cases h0 : t ≤ (9 / 20 : ℝ)
    · refine ⟨⟨4, (21 / 50 : ℚ), (9 / 20 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨ht0, h0⟩
    by_cases h1 : t ≤ (53 / 100 : ℝ)
    · refine ⟨⟨4, (9 / 20 : ℚ), (53 / 100 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h0).le, h1⟩
    by_cases h2 : t ≤ (94 / 125 : ℝ)
    · refine ⟨⟨4, (53 / 100 : ℚ), (94 / 125 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h1).le, h2⟩
    by_cases h3 : t ≤ (89 / 100 : ℝ)
    · refine ⟨⟨4, (94 / 125 : ℚ), (89 / 100 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h2).le, h3⟩
    by_cases h4 : t ≤ (567 / 500 : ℝ)
    · refine ⟨⟨4, (89 / 100 : ℚ), (567 / 500 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h3).le, h4⟩
    by_cases h5 : t ≤ (169 / 125 : ℝ)
    · refine ⟨⟨4, (567 / 500 : ℚ), (169 / 125 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h4).le, h5⟩
    by_cases h6 : t ≤ (13 / 8 : ℝ)
    · refine ⟨⟨4, (169 / 125 : ℚ), (13 / 8 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h5).le, h6⟩
    refine ⟨⟨4, (13 / 8 : ℚ), (9 / 5 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
    norm_num
    exact ⟨(lt_of_not_ge h6).le, ht1⟩
  · norm_num at ht0 ht1
    by_cases h0 : t ≤ (59 / 125 : ℝ)
    · refine ⟨⟨5, (2 / 5 : ℚ), (59 / 125 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨ht0, h0⟩
    by_cases h1 : t ≤ (91 / 125 : ℝ)
    · refine ⟨⟨5, (59 / 125 : ℚ), (91 / 125 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h0).le, h1⟩
    by_cases h2 : t ≤ (847 / 1000 : ℝ)
    · refine ⟨⟨5, (91 / 125 : ℚ), (847 / 1000 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h1).le, h2⟩
    by_cases h3 : t ≤ (287 / 250 : ℝ)
    · refine ⟨⟨5, (847 / 1000 : ℚ), (287 / 250 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h2).le, h3⟩
    by_cases h4 : t ≤ (184 / 125 : ℝ)
    · refine ⟨⟨5, (287 / 250 : ℚ), (184 / 125 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h3).le, h4⟩
    refine ⟨⟨5, (184 / 125 : ℚ), (17 / 10 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
    norm_num
    exact ⟨(lt_of_not_ge h4).le, ht1⟩
  · norm_num at ht0 ht1
    by_cases h0 : t ≤ (391 / 1000 : ℝ)
    · refine ⟨⟨6, (9 / 25 : ℚ), (391 / 1000 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨ht0, h0⟩
    by_cases h1 : t ≤ (519 / 1000 : ℝ)
    · refine ⟨⟨6, (391 / 1000 : ℚ), (519 / 1000 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h0).le, h1⟩
    by_cases h2 : t ≤ (153 / 200 : ℝ)
    · refine ⟨⟨6, (519 / 1000 : ℚ), (153 / 200 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h1).le, h2⟩
    by_cases h3 : t ≤ (959 / 1000 : ℝ)
    · refine ⟨⟨6, (153 / 200 : ℚ), (959 / 1000 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h2).le, h3⟩
    by_cases h4 : t ≤ (1307 / 1000 : ℝ)
    · refine ⟨⟨6, (959 / 1000 : ℚ), (1307 / 1000 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h3).le, h4⟩
    refine ⟨⟨6, (1307 / 1000 : ℚ), (17 / 10 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
    norm_num
    exact ⟨(lt_of_not_ge h4).le, ht1⟩
  · norm_num at ht0 ht1
    by_cases h0 : t ≤ (181 / 500 : ℝ)
    · refine ⟨⟨7, (33 / 100 : ℚ), (181 / 500 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨ht0, h0⟩
    by_cases h1 : t ≤ (247 / 500 : ℝ)
    · refine ⟨⟨7, (181 / 500 : ℚ), (247 / 500 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h0).le, h1⟩
    by_cases h2 : t ≤ (787 / 1000 : ℝ)
    · refine ⟨⟨7, (247 / 500 : ℚ), (787 / 1000 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h1).le, h2⟩
    by_cases h3 : t ≤ (1027 / 1000 : ℝ)
    · refine ⟨⟨7, (787 / 1000 : ℚ), (1027 / 1000 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h2).le, h3⟩
    by_cases h4 : t ≤ (1279 / 1000 : ℝ)
    · refine ⟨⟨7, (1027 / 1000 : ℚ), (1279 / 1000 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h3).le, h4⟩
    by_cases h5 : t ≤ (1533 / 1000 : ℝ)
    · refine ⟨⟨7, (1279 / 1000 : ℚ), (1533 / 1000 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h4).le, h5⟩
    by_cases h6 : t ≤ (1881 / 1000 : ℝ)
    · refine ⟨⟨7, (1533 / 1000 : ℚ), (1881 / 1000 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h5).le, h6⟩
    refine ⟨⟨7, (1881 / 1000 : ℚ), (19 / 10 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
    norm_num
    exact ⟨(lt_of_not_ge h6).le, ht1⟩
  · norm_num at ht0 ht1
    by_cases h0 : t ≤ (161 / 500 : ℝ)
    · refine ⟨⟨8, (3 / 10 : ℚ), (161 / 500 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨ht0, h0⟩
    by_cases h1 : t ≤ (83 / 200 : ℝ)
    · refine ⟨⟨8, (161 / 500 : ℚ), (83 / 200 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h0).le, h1⟩
    by_cases h2 : t ≤ (763 / 1000 : ℝ)
    · refine ⟨⟨8, (83 / 200 : ℚ), (763 / 1000 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h1).le, h2⟩
    by_cases h3 : t ≤ (201 / 200 : ℝ)
    · refine ⟨⟨8, (763 / 1000 : ℚ), (201 / 200 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h2).le, h3⟩
    by_cases h4 : t ≤ (257 / 200 : ℝ)
    · refine ⟨⟨8, (201 / 200 : ℚ), (257 / 200 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h3).le, h4⟩
    by_cases h5 : t ≤ (313 / 200 : ℝ)
    · refine ⟨⟨8, (257 / 200 : ℚ), (313 / 200 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
      norm_num
      exact ⟨(lt_of_not_ge h4).le, h5⟩
    refine ⟨⟨8, (313 / 200 : ℚ), (19 / 10 : ℚ)⟩, by rw [windowCells_literal_eq]; norm_num [windowCellsLiteral], ?_⟩
    norm_num
    exact ⟨(lt_of_not_ge h5).le, ht1⟩

/-- Theorem 5.14 on the reflected half of the activity domain. All finite
premises used by the note remain explicit, including the full D3 sign cases. -/
theorem window_theorem_positive (hD4 : V22.Checks.lemma_7_11)
    (hD0 : V22.Checks.lemma_7_16) (hD1 : V22.Checks.lemma_7_17)
    (hD1p : V22.Checks.lemma_7_18) (hD2 : V22.Checks.lemma_7_19)
    (hD3 : V22.Checks.lemma_7_20) {c : V22.V22Class} (hc : c ∈ V22.classes)
    {r mu : ℝ} {M : ℕ} (har : (c.ra : ℝ) ≤ r) (hrrb : r ≤ (c.rb : ℝ))
    (hmuD : (c.muD : ℝ) ≤ mu) (ht : (c.tau : ℝ) ≤ (M : ℝ) / mu) (j : ℤ) :
    V22.Checks.classTarget c ((M : ℝ) / mu) ≤ V22.fiberFunction ((1 + r) / 2) mu M j := by
  obtain ⟨hra, hrb, hb0, hb1, hbta0, hbta1, htau, htau1, hthi, htauthi, hmu40, hNs17, hder⟩ :=
    window_class_domains hc
  have hmu : 0 < mu := by linarith
  have ht0 : 0 < (M : ℝ) / mu := htau.trans_le ht
  have hr0 : 0 ≤ r := (hra.trans_le har).le
  have hrh : r ≤ 1 / 2 := hrrb.trans hrb
  by_cases hhi : (c.thi : ℝ) ≤ (M : ℝ) / mu
  · have htarget := (window_class_target_antitone hc hhi).trans_lt (hD0 c hc)
    have htlarge : (8 / 5 : ℝ) ≤ (M : ℝ) / mu := hthi.trans hhi
    have hM64 : (64 : ℝ) ≤ M := by
      have hM := (le_div_iff₀ hmu).1 htlarge
      nlinarith
    have hlarge := largeT_fiber_source hD4 (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
      (by norm_num : (10 : ℝ) ≤ 66) (by linarith : (66 : ℝ) ≤ (M : ℝ) + 2)
      hr0 hrh hmu htlarge j
    exact htarget.le.trans hlarge.1
  · have hthiT : (M : ℝ) / mu ≤ c.thi := by linarith
    obtain ⟨cell, hcell, hid, hclo, hlo, hhi⟩ := window_cells_cover hc ht hthiT
    let Ns : ℝ := (c.muD : ℝ) * (c.tau : ℝ) + 2
    let Na : ℝ := (c.muD : ℝ) * (cell.lo : ℝ) + 2
    have hNs : 10 ≤ Ns := by dsimp [Ns]; linarith
    have hsa : Ns ≤ Na := by
      have hprod := mul_le_mul_of_nonneg_left hclo (show 0 ≤ (c.muD : ℝ) from by linarith)
      dsimp [Ns, Na]
      linarith
    have hlo0 : 0 < (cell.lo : ℝ) := htau.trans_le hclo
    have haN : Na ≤ (M : ℝ) + 2 := by
      have hM := (le_div_iff₀ hmu).1 hlo
      have hprod := mul_le_mul_of_nonneg_right hmuD hlo0.le
      dsimp [Na]
      nlinarith
    have hcshape := hD1 c hc r har hrrb
    have hcp : V22.persistentWindowConditions r Ns :=
      ⟨hcshape.1, hcshape.2.1, hD1p.1 c hc r har hrrb⟩
    have hguard := hD2 c hc r har hrrb
    have hF := window_class_cell_fiber hra har hrrb hrb hNs hsa haN hmu hcp hguard j
    have hreq := hD3 c hc cell hcell hid ((M : ℝ) / mu) r hlo hhi har hrrb
    have hscale := window_size_scaling hmu (hNs.trans hsa) haN
    have htarget := window_target_scaled ht0 (by linarith : 2 < Na)
      (show 0 < ((M : ℝ) + 2) / mu from by positivity) hscale.1 hscale.2 hreq.1 hreq.2.1
    exact htarget.trans hF

/-- Paper v2.2 Theorem 5.14, all Table 1 classes, both activity halves,
every real mean at least mu_D, every original natural M, and every integer j. -/
theorem window_theorem_source (hD4 : V22.Checks.lemma_7_11)
    (hD0 : V22.Checks.lemma_7_16) (hD1 : V22.Checks.lemma_7_17)
    (hD1p : V22.Checks.lemma_7_18) (hD2 : V22.Checks.lemma_7_19)
    (hD3 : V22.Checks.lemma_7_20) {c : V22.V22Class} (hc : c ∈ V22.classes)
    {q mu : ℝ} {M : ℕ} (hr : (c.ra : ℝ) ≤ |2 * q - 1| ∧ |2 * q - 1| ≤ (c.rb : ℝ))
    (hmuD : (c.muD : ℝ) ≤ mu) (ht : (c.tau : ℝ) ≤ (M : ℝ) / mu) (j : ℤ) :
    V22.psi ((M : ℝ) / mu) + (c.b : ℝ) + (c.beta : ℝ) * ((M : ℝ) / mu - 1) ≤
      V22.fiberFunction q mu M j := by
  obtain ⟨hra, hrb, _⟩ := window_class_domains hc
  have hq : 0 < q ∧ q < 1 := by
    have habs := abs_le.mp (hr.2.trans hrb)
    constructor <;> linarith
  by_cases hhalf : 1 / 2 ≤ q
  · have hr0 : 0 ≤ 2 * q - 1 := by linarith
    rw [abs_of_nonneg hr0] at hr
    have h := window_theorem_positive hD4 hD0 hD1 hD1p hD2 hD3 hc hr.1 hr.2 hmuD ht j
    have he : (1 + (2 * q - 1)) / 2 = q := by ring
    simpa only [he, V22.Checks.classTarget] using h
  · have hr0 : 0 ≤ 1 - 2 * q := by linarith
    have hrneg : 2 * q - 1 ≤ 0 := by linarith
    rw [abs_of_nonpos hrneg] at hr
    have hlo : (c.ra : ℝ) ≤ 1 - 2 * q := by linarith [hr.1]
    have hhi : 1 - 2 * q ≤ (c.rb : ℝ) := by linarith [hr.2]
    have h := window_theorem_positive hD4 hD0 hD1 hD1p hD2 hD3 hc hlo hhi hmuD ht ((M : ℤ) - j)
    have he : (1 + (1 - 2 * q)) / 2 = 1 - q := by ring
    rw [he, shared_fiberFunction_eq, fiber_reflection hq.1 hq.2, ← shared_fiberFunction_eq] at h
    simpa only [V22.Checks.classTarget] using h

/-- The window theorem's actual all-integer infimum consumer. -/
theorem window_deficitG_zero (hD4 : V22.Checks.lemma_7_11)
    (hD0 : V22.Checks.lemma_7_16) (hD1 : V22.Checks.lemma_7_17)
    (hD1p : V22.Checks.lemma_7_18) (hD2 : V22.Checks.lemma_7_19)
    (hD3 : V22.Checks.lemma_7_20) {c : V22.V22Class} (hc : c ∈ V22.classes)
    {q mu : ℝ} {M : ℕ} (hr : (c.ra : ℝ) ≤ |2 * q - 1| ∧ |2 * q - 1| ≤ (c.rb : ℝ))
    (hmuD : (c.muD : ℝ) ≤ mu) (ht : (c.tau : ℝ) ≤ (M : ℝ) / mu) :
    V22.deficitG q mu c.b c.beta M = 0 := by
  have hq : 0 ≤ q ∧ q ≤ 1 := by
    obtain ⟨_, hrb, _⟩ := window_class_domains hc
    have h := abs_le.mp (hr.2.trans hrb)
    constructor <;> linarith
  obtain ⟨j, hj, _⟩ := shared_fiberInfimum_attained (mu := mu) hq.1 hq.2 M
  have hf := window_theorem_source hD4 hD0 hD1 hD1p hD2 hD3 hc hr hmuD ht j
  unfold V22.deficitG V22.targetLine V22.positivePart
  rw [hj, max_eq_right (by linarith)]

end Erdos993Lean.Analytic.V22.Analysis
