import Erdos993Lean.Analytic.V22.Analysis.WindowPhiBlocks
import Erdos993Lean.Analytic.V22.Analysis.OuterCells
import Erdos993Lean.Analytic.V22.Analysis.LambdaBonus

/-! Source: Corollary 5.15, the native lambda_U >= lambda_t comparison.
The six A4p pairs, all thirty grid blocks and three tail blocks of A4d,
the A4m sign, and D2 past N=29 are preserved exactly. Parent owns compilation. -/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

private def outerLogClassesLiteral : List V22.V22Class := [
  ⟨1, "C1", (3793 / 10000 : ℚ), (1 / 2 : ℚ), (2 / 5 : ℚ), (0 / 1 : ℚ), (3 / 5 : ℚ), (17 / 10 : ℚ), (45 / 1 : ℚ), [0, 1, 2]⟩,
  ⟨2, "C2", (1 / 4 : ℚ), (1897 / 5000 : ℚ), (2 / 5 : ℚ), (0 / 1 : ℚ), (69 / 100 : ℚ), (17 / 10 : ℚ), (50 / 1 : ℚ), [3, 4, 5]⟩,
  ⟨3, "C3", (833 / 5000 : ℚ), (2309 / 10000 : ℚ), (0 / 1 : ℚ), (1 / 2 : ℚ), (11 / 25 : ℚ), (7 / 4 : ℚ), (50 / 1 : ℚ), [40, 41, 42, 43]⟩,
  ⟨4, "C4", (2307 / 10000 : ℚ), (341 / 1250 : ℚ), (3 / 20 : ℚ), (3 / 10 : ℚ), (21 / 50 : ℚ), (9 / 5 : ℚ), (40 / 1 : ℚ), [44, 45, 46]⟩,
  ⟨5, "C5", (2727 / 10000 : ℚ), (194 / 625 : ℚ), (3 / 10 : ℚ), (0 / 1 : ℚ), (2 / 5 : ℚ), (17 / 10 : ℚ), (50 / 1 : ℚ), [47, 48, 49]⟩,
  ⟨6, "C6", (3103 / 10000 : ℚ), (861 / 2500 : ℚ), (3 / 10 : ℚ), (0 / 1 : ℚ), (9 / 25 : ℚ), (17 / 10 : ℚ), (50 / 1 : ℚ), [50, 51, 52]⟩,
  ⟨7, "C7", (1721 / 5000 : ℚ), (3847 / 10000 : ℚ), (3 / 10 : ℚ), (1 / 1 : ℚ), (33 / 100 : ℚ), (19 / 10 : ℚ), (50 / 1 : ℚ), [53]⟩,
  ⟨8, "C8", (1923 / 5000 : ℚ), (2 / 5 : ℚ), (3 / 10 : ℚ), (1 / 1 : ℚ), (3 / 10 : ℚ), (19 / 10 : ℚ), (50 / 1 : ℚ), [54]⟩
]

private theorem outerLogClassesLiteral_eq : V22.classes = outerLogClassesLiteral := by decide +kernel

set_option maxRecDepth 4000

/-- Exact r-grid coverage for A4d, including every shared endpoint. -/
theorem outer_phi_r_grid_cover {r : ℝ}
    (hlo : (3793/10000 : ℝ) ≤ r) (hhi : r ≤ (1/2 : ℝ)) :
    ∃ p ∈ ([3793/10000,2/5,21/50,11/25,23/50,12/25] : List ℚ).zip [2/5,21/50,11/25,23/50,12/25,1/2], (p.1 : ℝ) ≤ r ∧ r ≤ p.2 := by
  by_cases h0 : r ≤ (2/5 : ℝ)
  · refine ⟨((3793/10000:ℚ),(2/5:ℚ)), by norm_num, ?_⟩
    norm_num
    exact ⟨hlo, h0⟩
  by_cases h1 : r ≤ (21/50 : ℝ)
  · refine ⟨((2/5:ℚ),(21/50:ℚ)), by norm_num, ?_⟩
    norm_num
    exact ⟨(lt_of_not_ge h0).le, h1⟩
  by_cases h2 : r ≤ (11/25 : ℝ)
  · refine ⟨((21/50:ℚ),(11/25:ℚ)), by norm_num, ?_⟩
    norm_num
    exact ⟨(lt_of_not_ge h1).le, h2⟩
  by_cases h3 : r ≤ (23/50 : ℝ)
  · refine ⟨((11/25:ℚ),(23/50:ℚ)), by norm_num, ?_⟩
    norm_num
    exact ⟨(lt_of_not_ge h2).le, h3⟩
  by_cases h4 : r ≤ (12/25 : ℝ)
  · refine ⟨((23/50:ℚ),(12/25:ℚ)), by norm_num, ?_⟩
    norm_num
    exact ⟨(lt_of_not_ge h3).le, h4⟩
  refine ⟨((12/25:ℚ),(1/2:ℚ)), by norm_num, ?_⟩
  norm_num
  exact ⟨(lt_of_not_ge h4).le, hhi⟩

/-- Exact N-grid coverage for A4d, including every shared endpoint. -/
theorem outer_phi_N_grid_cover {N : ℝ}
    (hlo : (229/20 : ℝ) ≤ N) (hhi : N ≤ (20 : ℝ)) :
    ∃ p ∈ ([229/20,25/2,14,16,18] : List ℚ).zip [25/2,14,16,18,20], (p.1 : ℝ) ≤ N ∧ N ≤ p.2 := by
  by_cases h0 : N ≤ (25/2 : ℝ)
  · refine ⟨((229/20:ℚ),(25/2:ℚ)), by norm_num, ?_⟩
    norm_num
    exact ⟨hlo, h0⟩
  by_cases h1 : N ≤ (14 : ℝ)
  · refine ⟨((25/2:ℚ),(14:ℚ)), by norm_num, ?_⟩
    norm_num
    exact ⟨(lt_of_not_ge h0).le, h1⟩
  by_cases h2 : N ≤ (16 : ℝ)
  · refine ⟨((14:ℚ),(16:ℚ)), by norm_num, ?_⟩
    norm_num
    exact ⟨(lt_of_not_ge h1).le, h2⟩
  by_cases h3 : N ≤ (18 : ℝ)
  · refine ⟨((16:ℚ),(18:ℚ)), by norm_num, ?_⟩
    norm_num
    exact ⟨(lt_of_not_ge h2).le, h3⟩
  refine ⟨((18:ℚ),(20:ℚ)), by norm_num, ?_⟩
  norm_num
  exact ⟨(lt_of_not_ge h3).le, hhi⟩

theorem outer_phi_block_domains {c : ℚ × ℚ × ℚ × ℚ}
    (hc : c ∈ V22.Checks.phiRBlocks ++ V22.Checks.phiRTailBlocks) :
    (3793/10000 : ℝ) ≤ c.1 ∧ (c.2.1 : ℝ) ≤ 1/2 ∧ (229/20 : ℝ) ≤ c.2.2.1 := by
  change c ∈ [(3793/10000,2/5,229/20,25/2),(3793/10000,2/5,25/2,14),(3793/10000,2/5,14,16),(3793/10000,2/5,16,18),(3793/10000,2/5,18,20),(2/5,21/50,229/20,25/2),(2/5,21/50,25/2,14),(2/5,21/50,14,16),(2/5,21/50,16,18),(2/5,21/50,18,20),(21/50,11/25,229/20,25/2),(21/50,11/25,25/2,14),(21/50,11/25,14,16),(21/50,11/25,16,18),(21/50,11/25,18,20),(11/25,23/50,229/20,25/2),(11/25,23/50,25/2,14),(11/25,23/50,14,16),(11/25,23/50,16,18),(11/25,23/50,18,20),(23/50,12/25,229/20,25/2),(23/50,12/25,25/2,14),(23/50,12/25,14,16),(23/50,12/25,16,18),(23/50,12/25,18,20),(12/25,1/2,229/20,25/2),(12/25,1/2,25/2,14),(12/25,1/2,14,16),(12/25,1/2,16,18),(12/25,1/2,18,20),(3793/10000,1/2,20,23),(3793/10000,1/2,23,26),(3793/10000,1/2,26,291/10)] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
/-- The exact A4d blocks cover the entire source rectangle. -/
theorem outer_phi_blocks_cover {r N : ℝ} (hrlo : (3793/10000 : ℝ) ≤ r)
    (hrhi : r ≤ 1/2) (hNlo : (229/20 : ℝ) ≤ N) (hNhi : N ≤ 291/10) :
    ∃ c ∈ V22.Checks.phiRBlocks ++ V22.Checks.phiRTailBlocks,
      (c.1 : ℝ) ≤ r ∧ r ≤ c.2.1 ∧ (c.2.2.1 : ℝ) ≤ N ∧ N ≤ c.2.2.2 := by
  by_cases h20 : N ≤ 20
  · obtain ⟨rp, hrp, hra, hrb⟩ := outer_phi_r_grid_cover hrlo hrhi
    obtain ⟨np, hnp, hna, hnb⟩ := outer_phi_N_grid_cover hNlo h20
    -- The grid helpers retain a real second endpoint; recover its original
    -- rational endpoint through the exact native grid's cast map.
    have hrpMap : rp ∈
        (([3793/10000,2/5,21/50,11/25,23/50,12/25] : List ℚ).zip
          ([2/5,21/50,11/25,23/50,12/25,1/2] : List ℚ)).map
          (fun p : ℚ × ℚ => (p.1, (p.2 : ℝ))) := by
      convert hrp using 1 <;> norm_num
    rcases List.mem_map.mp hrpMap with ⟨rpQ, hrpQ, rfl⟩
    have hnpMap : np ∈
        (([229/20,25/2,14,16,18] : List ℚ).zip
          ([25/2,14,16,18,20] : List ℚ)).map
          (fun p : ℚ × ℚ => (p.1, (p.2 : ℝ))) := by
      convert hnp using 1 <;> norm_num
    rcases List.mem_map.mp hnpMap with ⟨npQ, hnpQ, rfl⟩
    refine ⟨((rpQ.1, rpQ.2, npQ.1, npQ.2) : ℚ × ℚ × ℚ × ℚ), ?_, hra, hrb, hna, hnb⟩
    apply List.mem_append.mpr
    left
    unfold V22.Checks.phiRBlocks
    apply List.mem_flatMap.mpr
    refine ⟨rpQ, hrpQ, ?_⟩
    exact List.mem_map.mpr ⟨npQ, hnpQ, rfl⟩
  · by_cases h23 : N ≤ 23
    · refine ⟨(3793/10000,1/2,20,23), ?_,
        (by convert hrlo using 1 <;> norm_num),
        (by convert hrhi using 1 <;> norm_num),
        (by norm_num; linarith), (by convert h23 using 1 <;> norm_num)⟩
      exact List.mem_append.mpr (Or.inr (by norm_num [V22.Checks.phiRTailBlocks]))
    by_cases h26 : N ≤ 26
    · refine ⟨(3793/10000,1/2,23,26), ?_,
        (by convert hrlo using 1 <;> norm_num),
        (by convert hrhi using 1 <;> norm_num),
        (by norm_num; linarith), (by convert h26 using 1 <;> norm_num)⟩
      exact List.mem_append.mpr (Or.inr (by norm_num [V22.Checks.phiRTailBlocks]))
    · refine ⟨(3793/10000,1/2,26,291/10), ?_,
        (by convert hrlo using 1 <;> norm_num),
        (by convert hrhi using 1 <;> norm_num),
        (by norm_num; linarith), (by convert hNhi using 1 <;> norm_num)⟩
      exact List.mem_append.mpr (Or.inr (by norm_num [V22.Checks.phiRTailBlocks]))

/-- A4d and A4m certify the actual Phi_R, not merely its boxed evaluator. -/
theorem outer_phiR_small_nonneg (hA4d : V22.Checks.lemma_7_8) (hA4m : V22.Checks.lemma_7_9)
    {r N : ℝ} (hrlo : (3793/10000 : ℝ) ≤ r) (hrhi : r ≤ 1/2)
    (hNlo : (229/20 : ℝ) ≤ N) (hNhi : N ≤ 291/10) : 0 ≤ V22.phiR r N := by
  obtain ⟨c, hc, hra, hrb, hna, hnb⟩ := outer_phi_blocks_cover hrlo hrhi hNlo hNhi
  obtain ⟨hclo, hchi, hcnlo⟩ := outer_phi_block_domains hc
  exact (hA4d c hc).trans (window_phiR_rectangular_lower hA4m hclo hra hrb hchi hcnlo hna hnb)

noncomputable def outerFirstClass : V22.V22Class :=
  ⟨1, "C1", 3793/10000, 1/2, 2/5, 0, 3/5, 17/10, 45, [0,1,2]⟩

theorem outerFirstClass_mem : outerFirstClass ∈ V22.classes := by
  norm_num [outerFirstClass, outerLogClassesLiteral_eq, outerLogClassesLiteral]

/-- The original D2 start for C1 is exactly N=29. -/
theorem outer_phiR_nonneg (hA4d : V22.Checks.lemma_7_8) (hA4m : V22.Checks.lemma_7_9)
    (hD2 : V22.Checks.lemma_7_19) {r N : ℝ} (hrlo : (3793/10000 : ℝ) ≤ r)
    (hrhi : r ≤ 1/2) (hNlo : (229/20 : ℝ) ≤ N) : 0 ≤ V22.phiR r N := by
  by_cases h29 : N ≤ 29
  · exact outer_phiR_small_nonneg hA4d hA4m hrlo hrhi hNlo (by linarith)
  · have hguard := hD2 outerFirstClass outerFirstClass_mem r
      (by convert hrlo using 1 <;> norm_num [outerFirstClass])
      (by convert hrhi using 1 <;> norm_num [outerFirstClass])
    norm_num [outerFirstClass] at hguard
    have hmono := (window_phiR_strictMonoOn (by linarith : 0 < r) hrhi
      (by norm_num : (10 : ℝ) ≤ 29) hguard).monotoneOn
      (show (29 : ℝ) ∈ Ici 29 from by exact (show (29 : ℝ) ≤ 29 from le_rfl)) (show N ∈ Ici 29 from by simp only [mem_Ici]; linarith)
      (show (29 : ℝ) ≤ N from by linarith)
    exact (outer_phiR_small_nonneg hA4d hA4m hrlo hrhi (by norm_num : (229/20 : ℝ) ≤ 29)
      (by norm_num : (29 : ℝ) ≤ 291/10)).trans hmono

/-- The source A4p pair that covers each outer class other than C1. -/
theorem outer_bonus_pair {k : V22.V22Class} (hk : k ∈ V22.classes) (hnot : k.classId ≠ 1) :
    ∃ p ∈ V22.Checks.bonusPairs, (k.rb : ℝ) ≤ p.1 ∧ 0 < (p.1 : ℝ) ∧
      (p.1 : ℝ) ≤ 1/2 ∧ 10 ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ (k.muD : ℝ) * (21/100) + 2 := by
  rw [outerLogClassesLiteral_eq] at hk
  simp only [outerLogClassesLiteral, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num at hnot
  · refine ⟨(3847/10000,12), by norm_num [V22.Checks.bonusPairs], ?_⟩
    norm_num
  · refine ⟨(1/4,10), by norm_num [V22.Checks.bonusPairs], ?_⟩
    norm_num
  · refine ⟨(7/25,10), by norm_num [V22.Checks.bonusPairs], ?_⟩
    norm_num
  · refine ⟨(194/625,10), by norm_num [V22.Checks.bonusPairs], ?_⟩
    norm_num
  · refine ⟨(861/2500,10), by norm_num [V22.Checks.bonusPairs], ?_⟩
    norm_num
  · refine ⟨(3847/10000,12), by norm_num [V22.Checks.bonusPairs], ?_⟩
    norm_num
  · refine ⟨(2/5,12), by norm_num [V22.Checks.bonusPairs], ?_⟩
    norm_num

/-- Corollary 5.15's native upper log-ratio comparison on every spike fiber.
C1 uses all exact A4d/A4m blocks and D2; other classes use their A4p pair. -/
theorem outer_lambdaU_lower (hA4p : V22.Checks.lemma_7_7)
    (hA4d : V22.Checks.lemma_7_8) (hA4m : V22.Checks.lemma_7_9)
    (hD2 : V22.Checks.lemma_7_19) {k : V22.V22Class} (hk : k ∈ V22.classes)
    {M : ℕ} {r mu : ℝ} (har : (k.ra : ℝ) ≤ r) (hrrb : r ≤ (k.rb : ℝ))
    (hmuD : (k.muD : ℝ) ≤ mu) (ht : (21/100 : ℝ) ≤ (M : ℝ) / mu) :
    V22.lambdaT ((M : ℝ) / mu) ≤ threeRangeLambdaU r mu M := by
  obtain ⟨hra, hrb, _, _, _, _, _, _, _, _, hmu40, _, _⟩ := window_class_domains hk
  have hmu : 0 < mu := by linarith
  have hr0 := (hra.trans_le har).le
  have hrh := hrrb.trans hrb
  have hM := (le_div_iff₀ hmu).1 ht
  have hN : (10 : ℝ) ≤ (M : ℝ) + 2 := by nlinarith
  have hNN : 10 ≤ M + 2 := by exact_mod_cast hN
  by_cases hfirst : k.classId = 1
  · have hkfirst : k = outerFirstClass := by
      rw [outerLogClassesLiteral_eq] at hk
      simp only [outerLogClassesLiteral, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · decide +kernel
      all_goals norm_num at hfirst
    rw [hkfirst] at har hrrb hmuD
    have hrlo : (3793/10000 : ℝ) ≤ r := by
      convert har using 1 <;> norm_num [outerFirstClass]
    have hrhi : r ≤ 1/2 := by
      convert hrrb using 1 <;> norm_num [outerFirstClass]
    have hmean45 : (45 : ℝ) ≤ mu := by
      convert hmuD using 1 <;> norm_num [outerFirstClass]
    have hNlo : (229/20 : ℝ) ≤ (M : ℝ) + 2 := by nlinarith
    have hphi := outer_phiR_nonneg hA4d hA4m hD2 hrlo hrhi hNlo
    have hlam := window_lambdaU_lower hNN hr0 hrh hmu
    change V22.lambdaT ((M : ℝ) / mu) + V22.phiR r ((M : ℝ) + 2) ≤ _ at hlam
    linarith
  · obtain ⟨p, hp, hrp, hp0, hph, hpn, hpm⟩ := outer_bonus_pair hk hfirst
    have hNlo : (p.2 : ℝ) ≤ (M : ℝ) + 2 := by nlinarith
    exact lambdaBonus_source (hA4p p hp) hp0 hph hpn hNlo hr0 (hrrb.trans hrp) hmu

end Erdos993Lean.Analytic.V22.Analysis
