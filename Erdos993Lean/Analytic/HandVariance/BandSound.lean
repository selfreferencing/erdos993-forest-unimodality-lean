import Erdos993Lean.Analytic.HandVariance.CoverageSound
import Erdos993Lean.Analytic.HandVariance.NumericSound
import Erdos993Lean.Analytic.HandVariance.ChildNumericSound
import Erdos993Lean.Analytic.HandVariance.FlankSound

/-!
# Retained Appendix N.4 recipes imply the actual band's step comparisons

Source: TWIN v1.8 Appendix N.4, `tgt:thm`, `mc:thm:step`,
`tgt:prop:red`, `tgt:lem:hand`, `tgt:lem:feas` and `mc:lem:base`.
This module consumes individual numerical rows on their exact source lists.
The activity row, source polygon, per-spatial cut, actual child coordinates
and the named band's activity endpoints all survive into `CompOK`.
-/

namespace Erdos993Lean.Analytic.HandVariance

open Real Set Reserve Compute

/-- The analytic meanings of the actual retained numerical recipes. This is
filled by NumericSound, ChildNumericSound and FlankSound, not by a global
comparison hypothesis. -/
structure ActivityAnalyticRows (s : Segment) (a : Activity) (p : Polygon) : Prop where
  vertices : ∀ v ∈ a.vertexChecks, ∀ lam ∈ Icc (a.activity.lo : ℝ) a.activity.hi,
    ∀ Y ∈ Icc (v.spatial.lo : ℝ) v.spatial.hi,
      0 ≤ if v.useGamma then vertexAgamma s.band lam Y v.r v.J
        else vertexA s.band lam Y v.r v.J
  ca : ∀ v ∈ a.caChecks, ∀ lam ∈ Icc (a.activity.lo : ℝ) a.activity.hi,
    ∀ Y ∈ Icc (v.spatial.lo : ℝ) v.spatial.hi,
      0 ≤ lBar s.band lam Y ∨ 0 ≤ cLower s.band lam Y a.Jcap
  polygon : ∀ c ∈ p.checks, ∀ T ∈ Icc (c.spatial.lo : ℝ) c.spatial.hi,
    coefJ c.activity T - (c.slope : ℝ) * childR c.activity T ≤ c.intercept
  chain : ∀ c ∈ p.chain, chainMeaning c
  flanks : FlankChecks s.band a.activity.lo a.activity.hi a.leftEnd a.Jcap

/-- Source: `tgt:lem:hand` (i). The global denominator enclosure holds for every physical polygon
coordinate, including the cap used by the CA and vertex soundness consumers. -/
theorem segment_zBar_pos_on_cap (s : Segment) {lo lam hi Y J Jcap : ℝ}
    (hlo : 0 < lo) (hl : lo ≤ lam) (hh : lam ≤ hi) (hY : 0 ≤ Y)
    (hJ : J ∈ Icc 0 Jcap) (hcheck : 0 < flankGlobalZ s.band lo hi Jcap) :
    0 < zBar s.band lam Y J := by
  have hc := segment_bandSide s
  have hlam : 0 < lam := hlo.trans_le hl
  have hhi : 0 < hi := hlam.trans_le hh
  have hc1 : 0 < flankC1 s.band hi := by
    unfold flankC1
    linarith [hc.gamma_pos hhi]
  have hc2 : 0 < flankC2 s.band lo hi := div_pos (hc.gamma_pos hlo) hhi
  have henv := flank_lBar_exp_lower hc hlo hl hh hY
  have hmax := flank_exp_peak (Y := Y) hc1 hc2
  have hL : -(flankC1 s.band hi * (log (flankC1 s.band hi / flankC2 s.band lo hi)-1)) ≤
      lBar s.band lam Y := by
    unfold flankC1 flankC2 at hmax
    rw [div_mul_eq_mul_div] at hmax
    dsimp [flankC1,flankC2]
    linarith
  have hpeak := flank_peak_nonneg hc hlo (hl.trans hh) (segment_gDen_ge_nine s)
  have hz := flank_zBar_lower (flank_gamma_mono hc hlo hl) hL hJ.1 hJ.2
  rw [min_eq_right (neg_nonpos.mpr hpeak)] at hz
  have hbound : flankGlobalZ s.band lo hi Jcap ≤ zBar s.band lam Y J := by
    unfold flankGlobalZ
    nlinarith
  exact hcheck.trans_le hbound

private theorem vertexRow_false (s : Segment) {a : Activity} {p : Polygon}
    (rows : ActivityAnalyticRows s a p) {v : VertexCheck} (hv : v ∈ a.vertexChecks)
    {lam Y : ℝ} (hlam : lam ∈ Icc (a.activity.lo : ℝ) a.activity.hi)
    (hY : Y ∈ Icc (v.spatial.lo : ℝ) v.spatial.hi) (htag : v.useGamma = false) :
    0 ≤ vertexA s.band lam Y v.r v.J := by
  simpa only [htag, Bool.false_eq_true, if_false] using rows.vertices v hv lam hlam Y hY

private theorem vertexRow_true (s : Segment) {a : Activity} {p : Polygon}
    (rows : ActivityAnalyticRows s a p) {v : VertexCheck} (hv : v ∈ a.vertexChecks)
    {lam Y : ℝ} (hlam : lam ∈ Icc (a.activity.lo : ℝ) a.activity.hi)
    (hY : Y ∈ Icc (v.spatial.lo : ℝ) v.spatial.hi) (htag : v.useGamma = true) :
    0 ≤ vertexAgamma s.band lam Y v.r v.J := by
  simpa only [htag, if_true] using rows.vertices v hv lam hlam Y hY

/-- Source: `tgt:lem:feas`, `tgt:lem:hand`, `tgt:thm` and `mc:thm:step`.
The CA rows and the two L-positive flanks certify the actual QC
comparison for every feasible child, with its exact child cap. -/
theorem activity_QC_of_rows (s : Segment) {a : Activity} {p : Polygon}
    (hcoverage : activityCoverageCheck a p = true) (rows : ActivityAnalyticRows s a p)
    {lam T Y : ℝ} (hlam : lam ∈ Icc (a.activity.lo : ℝ) a.activity.hi)
    (hT : 0 ≤ T) (hTY : lmass lam T ≤ Y) (hJ : coefJ lam T ≤ (a.Jcap : ℝ)) :
    0 ≤ coefL s.band lam Y ∨ 0 ≤ compC s.band lam T Y := by
  have facts := activityCoverageCheck_facts hcoverage
  have hlo : 0 < (a.activity.lo : ℝ) := by exact_mod_cast facts.lo_pos
  have ha : 0 < lam := hlo.trans_le hlam.1
  have hy := feasible_parent_pos ha hTY
  have hcap0 : 0 ≤ (a.Jcap : ℝ) := (polygonGeometryCheck_geometry facts.geometry).cap_nonneg
  have hz : ∀ j ∈ Icc (0 : ℝ) a.Jcap, 0 < zBar s.band lam Y j :=
    fun j hj => segment_zBar_pos_on_cap s hlo hlam.1 hlam.2 hy.le hj rows.flanks.globalZ_pos
  have hqc : 0 ≤ lBar s.band lam Y ∨ 0 ≤ cLower s.band lam Y a.Jcap := by
    by_cases hsmall : Y ≤ 1/500
    · exact Or.inl (flank_lBar_tiny_pos (segment_bandSide s) hlo hlam.1 hlam.2
        hy.le hsmall rows.flanks.tinyL_pos).le
    · by_cases hlarge : 3 ≤ Y
      · exact Or.inl (flank_lBar_large_pos (segment_bandSide s) hlo hlam.1 hlam.2
          hlarge rows.flanks.large_threshold rows.flanks.largeL_pos).le
      · obtain ⟨v, hv, hYv⟩ := activityCoverageCheck_ca hcoverage
          ⟨le_of_not_ge hsmall, le_of_not_ge hlarge⟩
        exact rows.ca v hv lam hlam Y hYv
  rcases hqc with hL | hC
  · left
    rw [coefL_eq_msg_lBar s.band ha Y]
    exact mul_nonneg (Reserve.Cert.msg_pos (X := Y) ha).le hL
  · by_cases hL : 0 ≤ lBar s.band lam Y
    · left
      rw [coefL_eq_msg_lBar s.band ha Y]
      exact mul_nonneg (Reserve.Cert.msg_pos (X := Y) ha).le hL
    · right
      have hzcap : 0 < gamma s.band lam - (a.Jcap : ℝ) * (-lBar s.band lam Y) := by
        simpa only [zBar, mul_neg, sub_neg_eq_add] using hz a.Jcap ⟨hcap0,le_rfl⟩
      have hquot := hC.trans (segment_compC_div_msg_ge_cLower s ha hT hTY
        (lt_of_not_ge hL) hJ hzcap)
      have hmul := (le_div_iff₀ (Reserve.Cert.msg_pos (X := Y) ha)).mp hquot
      simpa only [zero_mul] using hmul

private theorem checked_point_bounds (s : Segment) {a : Activity} {p : Polygon}
    (rows : ActivityAnalyticRows s a p) {lam Y : ℝ} {v : Rat × Rat}
    (hlam : lam ∈ Icc (a.activity.lo : ℝ) a.activity.hi)
    (hpoint : ∀ tag : Bool, ∃ c ∈ a.vertexChecks,
      c.r = v.1 ∧ c.J = v.2 ∧ c.useGamma = tag ∧
        Y ∈ Icc (c.spatial.lo : ℝ) c.spatial.hi) :
    0 ≤ vertexA s.band lam Y v.1 v.2 ∧ 0 ≤ vertexAgamma s.band lam Y v.1 v.2 := by
  constructor
  · obtain ⟨c, hc, hr, hJ, htag, hY⟩ := hpoint false
    simpa only [hr,hJ] using vertexRow_false s rows hc hlam hY htag
  · obtain ⟨c, hc, hr, hJ, htag, hY⟩ := hpoint true
    simpa only [hr,hJ] using vertexRow_true s rows hc hlam hY htag

/-- Source: `tgt:prop:red` and `tgt:lem:cut`. The core AC comparison uses the exact surviving vertices and actual
per-spatial cut, consuming only individually checked vertex rows. -/
theorem activity_AC_core_of_rows (s : Segment) {a : Activity} {p : Polygon}
    (hcoverage : activityCoverageCheck a p = true) (rows : ActivityAnalyticRows s a p)
    {lam T Y : ℝ} (hlam : lam ∈ Icc (a.activity.lo : ℝ) a.activity.hi)
    (hT : 0 ≤ T) (hTY : lmass lam T ≤ Y)
    (hY : Y ∈ Icc (a.leftEnd : ℝ) 3)
    (hJU : coefJ lam T ≤ polygonU (p.lines.map castPair) a.Jcap (childR lam T)) :
    0 ≤ vertexA s.band lam Y (childR lam T) (coefJ lam T) := by
  have facts := activityCoverageCheck_facts hcoverage
  have g := polygonGeometryCheck_geometry facts.geometry
  have hlo : 0 < (a.activity.lo : ℝ) := by exact_mod_cast facts.lo_pos
  have ha : 0 < lam := hlo.trans_le hlam.1
  have hYpos := feasible_parent_pos ha hTY
  have hb := (polygonGeometryCheck_lines facts.geometry).1
  have hγ := (segment_bandSide s).gamma_pos ha
  have hα := (segment_bandSide s).alpha_pos ha
  have hZ : ∀ j ∈ Icc (0 : ℝ) a.Jcap, 0 < zBar s.band lam Y j :=
    fun j hj => segment_zBar_pos_on_cap s hlo hlam.1 hlam.2 hYpos.le hj rows.flanks.globalZ_pos
  have hJ0 := Tails.coefJ_nonneg ha hT
  have hr0 : 0 ≤ childR lam T := div_nonneg hT (Reserve.Cert.lmass_pos (X := T) ha).le
  cases huse : a.useCut
  · have hv : ∀ v ∈ a.vertices.map castPair, (0 : ℝ) ≤ v.1 →
        0 ≤ vertexA s.band lam Y v.1 v.2 ∧ 0 ≤ vertexAgamma s.band lam Y v.1 v.2 := by
      intro v hv _
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hv
      exact checked_point_bounds s rows hlam
        (fun tag => activityCoverageCheck_uncut_vertices hcoverage huse hY hq tag)
    have hnode := hv (g.node 0) (g.node_mem (by omega)) (by simpa only [g.initial] using (le_refl (0 : ℝ)))
    have hheight : (g.node 0).2 = polygonU (p.lines.map castPair) a.Jcap 0 := by
      simpa only [g.initial] using g.upper ⟨0,by omega⟩
    have hcut : 0 ≤ vertexA s.band lam Y 0 (polygonU (p.lines.map castPair) a.Jcap 0) ∧
        0 ≤ vertexAgamma s.band lam Y 0 (polygonU (p.lines.map castPair) a.Jcap 0) := by
      simpa only [g.initial,hheight] using hnode
    exact vertexA_lower_of_polygon_geometry g hb hα.le hγ hZ (le_refl 0)
      hv hcut hr0 hJ0 hJU
  · obtain ⟨sp,hsp,hYsp,hgroup⟩ := activityCoverageCheck_cut_groups hcoverage huse hY
    obtain ⟨rmin,hrmin,hsafe,hpoints⟩ := cutGroupCheck_witness hgroup
    have hmin : (rmin : ℝ) ≤ childR lam T :=
      cutSafe_childR hsafe hlo hlam.1 hT hTY hYsp.2
    have point_bounds : ∀ q : Rat × Rat,
        (q = (rmin,polygonURat p.lines a.Jcap rmin) ∨
          (q ∈ a.vertices ∧ rmin ≤ q.1)) →
        0 ≤ vertexA s.band lam Y q.1 q.2 ∧ 0 ≤ vertexAgamma s.band lam Y q.1 q.2 := by
      intro q hq
      apply checked_point_bounds s rows hlam
      intro tag
      obtain ⟨c,hc,hspan,hr,hJ,htag⟩ := hpoints q hq tag
      refine ⟨c,hc,hr,hJ,htag,?_⟩
      have helo : c.spatial.lo = sp.1 := congrArg Prod.fst hspan
      have hehi : c.spatial.hi = sp.2 := congrArg Prod.snd hspan
      simpa only [helo,hehi] using hYsp
    have hv : ∀ v ∈ a.vertices.map castPair, (rmin : ℝ) ≤ v.1 →
        0 ≤ vertexA s.band lam Y v.1 v.2 ∧ 0 ≤ vertexAgamma s.band lam Y v.1 v.2 := by
      intro v hv hr
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hv
      have hqr : rmin ≤ q.1 := by
        dsimp only [castPair] at hr
        exact_mod_cast hr
      exact point_bounds q (Or.inr ⟨hq,hqr⟩)
    have hcut := point_bounds (rmin,polygonURat p.lines a.Jcap rmin) (Or.inl rfl)
    have hcutR : 0 ≤ vertexA s.band lam Y rmin (polygonU (p.lines.map castPair) a.Jcap rmin) ∧
        0 ≤ vertexAgamma s.band lam Y rmin (polygonU (p.lines.map castPair) a.Jcap rmin) := by
      simpa only [polygonURat_cast] using hcut
    have hmin0 : 0 ≤ (rmin : ℝ) := by exact_mod_cast hrmin
    exact vertexA_lower_of_polygon_geometry g hb hα.le hγ hZ hmin0 hv hcutR hmin hJ0 hJU

/-- Source: `tgt:thm` and `mc:thm:step`. The actual retained recipes cover every feasible parent-child pair on
one activity row, with the named band and all actual reserve coordinates. -/
theorem activity_compOK_of_rows (s : Segment) {a : Activity} {p : Polygon}
    (hcoverage : activityCoverageCheck a p = true) (hpolygon : polygonCoverageCheck p = true)
    (rows : ActivityAnalyticRows s a p) {lam T Y : ℝ}
    (hlam : lam ∈ Icc (a.activity.lo : ℝ) a.activity.hi)
    (hT : 0 ≤ T) (hTY : lmass lam T ≤ Y) : CompOK s.band lam T Y := by
  have facts := activityCoverageCheck_facts hcoverage
  have hlo : 0 < (a.activity.lo : ℝ) := by exact_mod_cast facts.lo_pos
  have ha : 0 < lam := hlo.trans_le hlam.1
  have hy := feasible_parent_pos ha hTY
  have hhigh : lam ≤ (p.activity : ℝ) := by
    have hh : (a.activity.hi : ℝ) ≤ a.polygonActivity := by exact_mod_cast facts.hi_polygon
    rw [facts.polygon_activity]
    exact hlam.2.trans hh
  have hJU := child_le_polygonU_of_coverage hpolygon ha hhigh
    (polygonGeometryCheck_lines facts.geometry).2 rows.polygon rows.chain hT
  have hJ : coefJ lam T ≤ (a.Jcap : ℝ) := hJU.trans (polygonU_le_cap _ _ _)
  have hJ0 := Tails.coefJ_nonneg ha hT
  have hz : 0 < zBar s.band lam Y (coefJ lam T) :=
    segment_zBar_pos_on_cap s hlo hlam.1 hlam.2 hy.le ⟨hJ0,hJ⟩ rows.flanks.globalZ_pos
  refine ⟨?_,activity_QC_of_rows s hcoverage rows hlam hT hTY hJ,?_⟩
  · rw [coefZ_eq_msg_zBar s.band ha T Y]
    exact mul_pos (Reserve.Cert.msg_pos (X := Y) ha) hz
  · by_cases hsmall : Y ≤ (a.leftEnd : ℝ)
    · exact (flank_compB_small_pos (segment_bandSide s) hlo hlam.1 hlam.2
        hT hTY hsmall hJ rows.flanks).le
    · by_cases hlarge : 3 ≤ Y
      · exact (flank_compB_large_pos (segment_bandSide s) hlo hlam.1 hlam.2
          hlarge hT hJ rows.flanks).le
      · have hA := activity_AC_core_of_rows s hcoverage rows hlam hT hTY
          ⟨le_of_not_ge hsmall,le_of_not_ge hlarge⟩ hJU
        have hquot : 0 ≤ compB s.band lam T Y / msg lam Y := by
          rw [compB_div_msg s.band ha T hy hz.ne']
          exact hA
        have hmul := (le_div_iff₀ (Reserve.Cert.msg_pos (X := Y) ha)).mp hquot
        simpa only [zero_mul] using hmul

/-- Source: `tgt:thm`, `mc:thm:step` and the finite-check families `chk:tgt`,
`chk:mc`. Individual positive numerical checks fill the exact retained row
meanings. All denominator premises come from the independently checked
flank data and explicit finite metadata guards. -/
theorem activityAnalyticRows_of_checks (s : Segment) {a : Activity} {p : Polygon}
    (hsegment : a.segment = s.index) (hcoverage : activityCoverageCheck a p = true)
    (hpolygon : polygonCoverageCheck p = true) (hactivity : activityOK a = true)
    (hpolyNumeric : polygonOK p = true)
    (hflanks : FlankChecks s.band a.activity.lo a.activity.hi a.leftEnd a.Jcap) :
    ActivityAnalyticRows s a p := by
  have facts := activityCoverageCheck_facts hcoverage
  have hlo : 0 < (a.activity.lo : ℝ) := by exact_mod_cast facts.lo_pos
  have hc : (a.center : ℝ) ∈ Icc (a.activity.lo : ℝ) a.activity.hi := by
    constructor
    · exact_mod_cast facts.center_lo
    · exact_mod_cast facts.center_hi
  have hcap0 := (polygonGeometryCheck_geometry facts.geometry).cap_nonneg
  have hg : ∀ lam ∈ Icc (a.activity.lo : ℝ) a.activity.hi,
      gamma (parameters a.segment).asBand lam ≠ 0 := by
    intro lam hlam
    rw [hsegment,parameters_segment_gamma]
    exact ((segment_bandSide s).gamma_pos (hlo.trans_le hlam.1)).ne'
  have ha := hactivity
  simp only [activityOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ha
  have hp := hpolyNumeric
  simp only [polygonOK, Bool.and_eq_true, List.all_eq_true] at hp
  have hpc := hpolygon
  simp only [polygonCoverageCheck, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hpc
  refine ⟨?_,?_,?_,?_,hflanks⟩
  · intro v hv lam hlam Y hY
    have hvr := facts.vertex_rows v hv
    have hYpos : 0 < (v.spatial.lo : ℝ) := by
      exact_mod_cast facts.left_pos.trans_le hvr.1
    have hZ : ∀ l ∈ Icc (a.activity.lo : ℝ) a.activity.hi,
        ∀ y ∈ Icc (v.spatial.lo : ℝ) v.spatial.hi,
        zBar (parameters a.segment).asBand l y v.J ≠ 0 := by
      intro l hl y hy
      rw [hsegment,parameters_segment_zBar]
      have hy0 : 0 ≤ y := hYpos.le.trans hy.1
      have hj : (v.J : ℝ) ∈ Icc (0 : ℝ) (a.Jcap : ℝ) := by
        constructor
        · exact_mod_cast hvr.2.2.2.2.1
        · exact_mod_cast hvr.2.2.2.2.2
      exact (segment_zBar_pos_on_cap s hlo hl.1 hl.2 hy0 hj hflanks.globalZ_pos).ne'
    have hvp := vertexLower_positive a v (ha.1.1.2 v hv) hlo hc hYpos hZ hg hlam hY
    simpa only [taggedVertex,hsegment,parameters_segment_vertexA,
      parameters_segment_vertexAgamma] using hvp
  · intro v hv lam hlam Y hY
    have hvr := facts.ca_rows v hv
    have hYpos : 0 < (v.spatial.lo : ℝ) := by
      have hh : ((1/500 : Rat) : ℝ) ≤ (v.spatial.lo : ℝ) := by exact_mod_cast hvr.1
      norm_num at hh
      linarith
    have hZ : ∀ l ∈ Icc (a.activity.lo : ℝ) a.activity.hi,
        ∀ y ∈ Icc (v.spatial.lo : ℝ) v.spatial.hi,
        zBar (parameters a.segment).asBand l y a.Jcap ≠ 0 := by
      intro l hl y hy
      rw [hsegment,parameters_segment_zBar]
      exact (segment_zBar_pos_on_cap s hlo hl.1 hl.2 (hYpos.le.trans hy.1)
        ⟨hcap0,le_rfl⟩ hflanks.globalZ_pos).ne'
    have hcp := caLower_positive a v (ha.1.2 v hv) hlo hc hYpos hZ hlam hY
    simpa only [hsegment,parameters_segment_lBar,parameters_segment_cLower] using hcp
  · intro c hc T hT
    have hac : c.activity = p.activity := (hpc.1.1.2 c hc).1
    have hpos : 0 < (c.activity : ℝ) := by
      rw [hac]
      exact_mod_cast hpc.1.1.1.1.1
    cases he : polygonLower c with
    | none =>
      have hh := hp.1 c hc
      simp only [he,optionPositive,Bool.false_eq_true] at hh
    | some beta =>
      have hb : (0 : Rat) < beta := by
        simpa only [he,optionPositive,decide_eq_true_eq] using hp.1 c hc
      have hn := polygonLower_sound c he hpos hT
      have hb0 : (0 : ℝ) ≤ beta := by exact_mod_cast hb.le
      linarith
  · intro c hc
    cases he : chainLower c with
    | none =>
      have hh := hp.2 c hc
      simp only [he,optionPositive,Bool.false_eq_true] at hh
    | some beta =>
      have hb : (0 : Rat) < beta := by
        simpa only [he,optionPositive,decide_eq_true_eq] using hp.2 c hc
      have hn := (chainLower_endpoint_sound c he).2.2
      have hb0 : (0 : ℝ) < beta := by exact_mod_cast hb
      unfold chainMeaning
      cases hr : c.right <;> simp only [hr,one_div] at hn ⊢ <;> norm_num at hn <;> linarith

/-- Source: `tgt:lem:hand` (i)--(iv). Successful retained flank calculations supply the actual named band's
flank record, using all additional proved quotient and sign guards. -/
theorem activityFlankChecks_of_checks (s : Segment) {a : Activity} {p : Polygon}
    (hsegment : a.segment = s.index) (hcoverage : activityCoverageCheck a p = true)
    (hactivity : activityOK a = true) :
    FlankChecks s.band a.activity.lo a.activity.hi a.leftEnd a.Jcap := by
  have facts := activityCoverageCheck_facts hcoverage
  have hlast := (bool_and_true hactivity).2
  cases he : flankBounds a with
  | none => simp only [he,Bool.false_eq_true] at hlast
  | some xs =>
    have hpos : allPositive xs = true := by simpa only [he] using hlast
    have hn := flankBounds_sound he hpos facts.zero_k_pos facts.three_k_pos facts.large_n_upper_neg
    rw [hsegment] at hn
    exact parameters_segment_flankChecks s hn

/-- Source: `tgt:thm` and `mc:thm:step`. All actual checked recipe data imply
CompOK for this activity row. -/
theorem activity_compOK_of_checks (s : Segment) {a : Activity} {p : Polygon}
    (hsegment : a.segment = s.index) (hcoverage : activityCoverageCheck a p = true)
    (hpolygon : polygonCoverageCheck p = true) (hactivity : activityOK a = true)
    (hpolyNumeric : polygonOK p = true) {lam T Y : ℝ}
    (hlam : lam ∈ Icc (a.activity.lo : ℝ) a.activity.hi)
    (hT : 0 ≤ T) (hTY : lmass lam T ≤ Y) : CompOK s.band lam T Y := by
  have hf := activityFlankChecks_of_checks s hsegment hcoverage hactivity
  exact activity_compOK_of_rows s hcoverage hpolygon
    (activityAnalyticRows_of_checks s hsegment hcoverage hpolygon hactivity hpolyNumeric hf)
    hlam hT hTY

/-- Source: `tgt:thm`, `mc:thm:step` and Table `mc:tab:curve`.
Every named band is covered by actual retained activity/polygon recipes;
its exact activity endpoints remain in the global step comparison. -/
theorem band_compOK_of_checks (s : Segment) {activities : List Activity}
    {polygons : List Polygon}
    (hcoverage : segmentActivityCoverageCheck s.index activities polygons = true)
    (hactivities : activities.all activityOK = true)
    (hpolygonCover : polygons.all polygonCoverageCheck = true)
    (hpolygons : polygons.all polygonOK = true) :
    ∀ lam T Y : ℝ, (s.band.lo : ℝ) ≤ lam → lam ≤ s.band.hi → 0 ≤ T →
      lmass lam T ≤ Y → CompOK s.band lam T Y := by
  intro lam T Y hl hh hT hTY
  obtain ⟨a,ha,hs,hla,p,hp,hap⟩ := segmentActivityCoverageCheck_band_covers hcoverage ⟨hl,hh⟩
  exact activity_compOK_of_checks s hs hap
    (List.all_eq_true.mp hpolygonCover p hp) (List.all_eq_true.mp hactivities a ha)
    (List.all_eq_true.mp hpolygons p hp) hla hT hTY

/-- Source: `mc:eq:base`, `mc:lem:base` and the base part of `tgt:thm`.
The selected-leaf recipes and their same-band coverage prove the
actual named band's base inequality on every activity, including endpoints. -/
theorem band_leafOK_of_checks (s : Segment) {rows : List BaseCheck}
    (hcoverage : baseCoverageCheck s.index rows = true)
    (hchecks : rows.all (fun b => optionPositive (baseLower b)) = true) : LeafOK s.band := by
  intro lam hl hh
  obtain ⟨b,hb,hs,hlam⟩ := baseCoverageCheck_band_covers hcoverage ⟨hl,hh⟩
  have hbspan := baseCoverageCheck_band_row_bounds hcoverage hb
  have hbpos : 0 < (b.activity.lo : ℝ) :=
    (segment_bandSide s).lo_pos.trans_le hbspan.1
  have hpos := List.all_eq_true.mp hchecks b hb
  cases he : baseLower b with
  | none => simp only [he,optionPositive,Bool.false_eq_true] at hpos
  | some beta =>
    have hp : (0 : Rat) < beta := by simpa only [he,optionPositive,decide_eq_true_eq] using hpos
    have hn := baseLower_sound b he hbpos hlam
    rw [hs] at hn
    have heq : baseSlack (parameters s.index).asBand lam = baseSlack s.band lam := by
      cases s <;> rfl
    rw [heq] at hn
    have hb0 : (0 : ℝ) ≤ beta := by exact_mod_cast hp.le
    have hslack := hb0.trans hn
    unfold baseSlack at hslack
    linarith

end Erdos993Lean.Analytic.HandVariance

#print axioms Erdos993Lean.Analytic.HandVariance.band_compOK_of_checks
#print axioms Erdos993Lean.Analytic.HandVariance.band_leafOK_of_checks
