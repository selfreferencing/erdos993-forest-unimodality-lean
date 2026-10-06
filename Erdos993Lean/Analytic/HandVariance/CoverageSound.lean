import Erdos993Lean.Analytic.HandVariance.Compute.Coverage
import Erdos993Lean.Analytic.HandVariance.Polygon
import Erdos993Lean.Analytic.HandVariance.ExprSound
import Erdos993Lean.Analytic.HandVariance.ContextSound
import Erdos993Lean.Analytic.HandVariance.Feasibility

/-!
# Ordinary soundness of the finite Appendix N.4 coverage guards

The checker facts below consume the actual exported lists. Taylor or transport
soundness supplies each retained row's analytic conclusion; these proofs then
cover every spatial point and the full infinite child tail. No global polygon
inequality is taken as a hypothesis.
-/

namespace Erdos993Lean.Analytic.HandVariance

/-- The exact source recipe index of each named closed hand segment. -/
def Segment.index : Segment → Nat
  | .lo => 0
  | .mid => 1
  | .u1 => 2
  | .u2 => 3
  | .u3 => 4
  | .u4 => 5

/-- All retained segment indices occur in the finite six-segment census. -/
theorem Segment.index_lt_six (s : Segment) : s.index < 6 := by
  cases s <;> decide

namespace Compute

open Real Set Reserve Erdos993Lean.Analytic.TailCert
open Erdos993Lean.Analytic.TailCert.Compute

theorem bool_and_true {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  simpa only [Bool.and_eq_true] using h

noncomputable def castPair (v : Rat × Rat) : ℝ × ℝ := (v.1, v.2)

theorem polygonLineRat_cast (line : Rat × Rat) (r : Rat) :
    (polygonLineRat line r : ℝ) = polygonLine (castPair line) r := by
  simp [polygonLineRat, polygonLine, castPair]

theorem polygonURat_cast (lines : List (Rat × Rat)) (cap r : Rat) :
    (polygonURat lines cap r : ℝ) = polygonU (lines.map castPair) cap r := by
  induction lines with
  | nil => rfl
  | cons line lines ih =>
      simp only [polygonURat, Rat.cast_min, List.map_cons, polygonU,
        polygonLineRat_cast, ih]

/-- A checked contiguous list covers its entire requested closed interval. -/
theorem partitionFrom_covers {pieces : List (Rat × Rat)} {start stop : Rat}
    (h : partitionFrom start stop pieces = true) {x : ℝ}
    (hx : x ∈ Icc (start : ℝ) stop) :
    ∃ piece ∈ pieces, x ∈ Icc (piece.1 : ℝ) piece.2 := by
  induction pieces generalizing start with
  | nil => simp [partitionFrom] at h
  | cons a rest ih =>
      cases rest with
      | nil =>
          simp only [partitionFrom, Bool.and_eq_true, decide_eq_true_eq] at h
          refine ⟨a, by simp, ?_⟩
          simpa only [h.1.1, h.2] using hx
      | cons b rest =>
          change (decide (a.1 = start ∧ a.1 ≤ a.2) && partitionFrom a.2 stop (b :: rest)) = true at h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          by_cases hxa : x ≤ (a.2 : ℝ)
          · refine ⟨a, by simp, ?_, hxa⟩
            simpa only [h.1.1] using hx.1
          · obtain ⟨piece, hp, hxp⟩ := ih h.2
              ⟨(le_of_not_ge hxa), hx.2⟩
            exact ⟨piece, List.mem_cons_of_mem a hp, hxp⟩

/-- Every retained piece also lies inside the requested finite span. This
supplies positive activity endpoints for the selected-leaf consumer. -/
theorem partitionFrom_member_bounds {pieces : List (Rat × Rat)} {start stop : Rat}
    (h : partitionFrom start stop pieces = true) {piece : Rat × Rat}
    (hp : piece ∈ pieces) : start ≤ piece.1 ∧ piece.1 ≤ piece.2 ∧ piece.2 ≤ stop := by
  induction pieces generalizing start piece with
  | nil => simp at hp
  | cons a rest ih =>
      cases rest with
      | nil =>
        simp only [partitionFrom, Bool.and_eq_true, decide_eq_true_eq] at h
        have he : piece = a := by simpa only [List.mem_singleton] using hp
        subst piece
        exact ⟨h.1.1.ge,h.1.2,h.2.le⟩
      | cons b rest =>
        change (decide (a.1 = start ∧ a.1 ≤ a.2) && partitionFrom a.2 stop (b :: rest)) = true at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        have hb := ih h.2 (List.mem_cons_self : b ∈ b :: rest)
        have hab : a.2 ≤ stop := hb.1.trans (hb.2.1.trans hb.2.2)
        rcases List.mem_cons.mp hp with he | hp
        · subst piece
          exact ⟨h.1.1.ge,h.1.2,hab⟩
        · have hh := ih h.2 hp
          refine ⟨?_,hh.2⟩
          rw [← h.1.1]
          exact h.1.2.trans hh.1

/-- A pointwise row conclusion is retained on the full checked partition. -/
theorem bound_on_checked_partition {pieces : List (Rat × Rat)} {start stop : Rat}
    {P : ℝ → Prop} (h : partitionFrom start stop pieces = true)
    (hrow : ∀ piece ∈ pieces, ∀ x ∈ Icc (piece.1 : ℝ) piece.2, P x)
    {x : ℝ} (hx : x ∈ Icc (start : ℝ) stop) : P x := by
  obtain ⟨piece, hp, hxp⟩ := partitionFrom_covers h hx
  exact hrow piece hp x hxp

private theorem getD_mem {α : Type*} (xs : List α) (d : α) {i : Nat}
    (hi : i < xs.length) : xs.getD i d ∈ xs := by
  rw [List.getD_eq_getElem xs d hi]
  exact List.getElem_mem hi

/-- The finite Boolean geometry constructs precisely the supplied real
vertex list, rather than a replacement polygon with different provenance. -/
noncomputable def polygonGeometryCheck_geometry {lines : List (Rat × Rat)} {cap : Rat}
    {vertices : List (Rat × Rat)} (h : polygonGeometryCheck lines cap vertices = true) :
    PolygonGeometry (lines.map castPair) (cap : ℝ) (vertices.map castPair) := by
  simp only [polygonGeometryCheck, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.any_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨⟨hlen, hzero⟩, hv⟩, he⟩, hlast⟩, _⟩, _⟩
  have hsize : vertices.length - 1 + 1 = vertices.length := by omega
  refine ⟨vertices.length-1, fun i => castPair (vertices.getD i (0,0)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsize]
    symm
    convert List.ofFn_getElem_eq_map vertices castPair using 1
    congr 1
    funext i
    exact congrArg castPair (List.getD_eq_getElem vertices (0,0) i.isLt)
  · dsimp only [castPair]
    exact_mod_cast hzero
  · intro i
    have hh := (he i.val (List.mem_range.mpr i.isLt)).1
    dsimp only [castPair]
    exact_mod_cast hh
  · intro i
    have hi : i.val < vertices.length := by omega
    have hh := (hv _ (getD_mem vertices (0,0) hi)).1
    dsimp only [castPair]
    exact_mod_cast hh
  · intro i
    have hi : i.val < vertices.length := by omega
    have hh := (hv _ (getD_mem vertices (0,0) hi)).2
    have hc := congrArg (fun q : Rat => (q : ℝ)) hh
    simpa only [castPair, polygonURat_cast] using hc
  · dsimp only [castPair]
    exact_mod_cast hlast
  · intro i
    obtain ⟨line, hl, h0, h1⟩ := (he i.val (List.mem_range.mpr i.isLt)).2
    refine ⟨castPair line, List.mem_map.mpr ⟨line, hl, rfl⟩, ?_, ?_⟩
    · have hc := congrArg (fun q : Rat => (q : ℝ)) h0
      simpa only [castPair, polygonLineRat_cast] using hc
    · have hc := congrArg (fun q : Rat => (q : ℝ)) h1
      simpa only [castPair, polygonLineRat_cast] using hc

/-- The cap ray slopes and actual zero-slope cap line survive the guard. -/
theorem polygonGeometryCheck_lines {lines : List (Rat × Rat)} {cap : Rat}
    {vertices : List (Rat × Rat)} (h : polygonGeometryCheck lines cap vertices = true) :
    (∀ line ∈ lines.map castPair, 0 ≤ line.2) ∧ ((cap : ℝ),0) ∈ lines.map castPair := by
  simp only [polygonGeometryCheck, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.any_eq_true] at h
  refine ⟨?_, ?_⟩
  · intro line hl
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl
    have hs := h.1.2 q hq
    dsimp only [castPair]
    exact_mod_cast hs
  · exact List.mem_map.mpr ⟨(cap,0), h.2, by simp [castPair]⟩

/-- Exact real interpretation of a retained finite or terminal tail row. -/
noncomputable def chainMeaning (c : ChainCheck) : Prop :=
  match c.right with
  | none => 1 / (c.left : ℝ) + 1 - 2 + 2 * msg c.activity c.left < 0
  | some right => 1 / (c.left : ℝ) + 1 / (1 + msg c.activity right / 2) - 2 +
      2 * msg c.activity c.left < 0

/-- The finite checked chain proves monotonicity on its whole infinite ray. -/
theorem chainCoverageCheck_antitone {activity start : Rat} {chain : List ChainCheck}
    (h : chainCoverageCheck activity start chain = true) (ha : 0 < (activity : ℝ))
    (hnumeric : ∀ c ∈ chain, chainMeaning c) :
    AntitoneOn (coefJ activity) (Ici (start : ℝ)) := by
  simp only [chainCoverageCheck, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at h
  rcases h with ⟨⟨⟨⟨hlen, hstart⟩, hrows⟩, hnext⟩, hlast⟩
  let n := chain.length-1
  let t : Nat → ℝ := fun i => (chain.getD i ⟨0,0,none⟩).left
  have ht0 : t 0 = (start : ℝ) := by
    dsimp only [t]
    exact_mod_cast hstart
  have hnode : ∀ i ≤ n,
      (chain.getD i ⟨0,0,none⟩).activity = activity ∧
        0 < (chain.getD i ⟨0,0,none⟩).left := by
    intro i hi
    apply hrows
    exact getD_mem chain ⟨0,0,none⟩ (by dsimp [n] at hi; omega)
  have ht : 0 < t 0 := by
    dsimp only [t]
    exact_mod_cast (hnode 0 (by omega)).2
  have hinc : ∀ i < n, t i < t (i+1) := by
    intro i hi
    have hh := (hnext i (List.mem_range.mpr hi)).2
    dsimp only [t]
    exact_mod_cast hh
  have hseg : ∀ i < n,
      1 / t i + 1 / (1 + msg activity (t (i+1)) / 2) - 2 +
        2 * msg activity (t i) < 0 := by
    intro i hi
    have hn := hnumeric (chain.getD i ⟨0,0,none⟩)
      (getD_mem chain ⟨0,0,none⟩ (i := i) (by dsimp [n] at hi; omega))
    have hr := (hnext i (List.mem_range.mpr hi)).1
    unfold chainMeaning at hn
    rw [hr] at hn
    rw [(hnode i (by omega)).1] at hn
    exact hn
  have hend : 1 / t n + 1 - 2 + 2 * msg activity (t n) < 0 := by
    have hn := hnumeric (chain.getD n ⟨0,0,none⟩)
      (getD_mem chain ⟨0,0,none⟩ (i := n) (by omega))
    unfold chainMeaning at hn
    rw [hlast, (hnode n (le_refl _)).1] at hn
    exact hn
  have hh := coefJ_antitoneOn_of_chain ha n t ht hinc hseg hend
  simpa only [ht0] using hh

/-- Each actual Taylor row is consumed once its analytic soundness is known;
its list coverage and the checked chain then prove every child upper line. -/
theorem polygonCoverageCheck_lines {p : Polygon}
    (h : polygonCoverageCheck p = true)
    (hfinite : ∀ c ∈ p.checks, ∀ T ∈ Icc (c.spatial.lo : ℝ) c.spatial.hi,
      coefJ c.activity T - (c.slope : ℝ) * childR c.activity T ≤ c.intercept)
    (hchain : ∀ c ∈ p.chain, chainMeaning c) :
    ∀ line ∈ p.lines, ∀ T ≥ 0,
      coefJ p.activity T ≤ polygonLine (castPair line) (childR p.activity T) := by
  simp only [polygonCoverageCheck, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at h
  rcases h with ⟨⟨⟨⟨hmeta, hslopes⟩, _⟩, hparts⟩, htail⟩
  have ha : 0 < (p.activity : ℝ) := by exact_mod_cast hmeta.1
  have ht : 0 < (p.tailStart : ℝ) := by exact_mod_cast hmeta.2.2
  have hj := chainCoverageCheck_antitone htail ha hchain
  intro line hl
  have hb : 0 ≤ (line.2 : ℝ) := by exact_mod_cast hslopes line hl
  have hrow : ∀ piece ∈ polygonPieces p line,
      ∀ T ∈ Icc (piece.1 : ℝ) piece.2,
        coefJ p.activity T - (line.2 : ℝ) * childR p.activity T ≤ line.1 := by
    intro piece hp T hT
    obtain ⟨c, hc, hp⟩ := List.mem_map.mp hp
    have hcf := List.mem_filter.mp hc
    have hid : c.activity = p.activity ∧ c.intercept = line.1 ∧ c.slope = line.2 := by
      simpa only [decide_eq_true_eq] using hcf.2
    have hf := hfinite c hcf.1 T (by simpa only [← hp, spanPair] using hT)
    simpa only [hid.1, hid.2.1, hid.2.2] using hf
  have hsmall : ∀ T ∈ Icc (0 : ℝ) p.tailStart,
      coefJ p.activity T - (line.2 : ℝ) * childR p.activity T ≤ line.1 :=
    fun T hT => bound_on_checked_partition (hparts line hl) hrow
      (by simpa only [Rat.cast_zero] using hT)
  have hslack := child_polygon_slack_antitoneOn ha ht.le hb hj
  intro T hT
  have hf : coefJ p.activity T - (line.2 : ℝ) * childR p.activity T ≤ line.1 := by
    by_cases hTs : T ≤ (p.tailStart : ℝ)
    · exact hsmall T ⟨hT,hTs⟩
    · have htmem : (p.tailStart : ℝ) ∈ Ici (p.tailStart : ℝ) := by
        simpa only [Set.mem_Ici] using (le_refl (p.tailStart : ℝ))
      have hTmem : T ∈ Ici (p.tailStart : ℝ) := by
        simpa only [Set.mem_Ici] using (le_of_not_ge hTs)
      exact (hslack htmem hTmem hTmem).trans (hsmall p.tailStart ⟨ht.le,le_rfl⟩)
  dsimp [polygonLine, castPair]
  linarith

/-- The list of upper lines transports to every smaller positive activity.
The explicitly retained cap line supplies the cap inequality as well. -/
theorem child_le_polygonU_of_coverage {p : Polygon} {cap lam T : ℝ}
    (h : polygonCoverageCheck p = true) (hlam : 0 < lam)
    (hll : lam ≤ (p.activity : ℝ)) (hcapline : (cap,0) ∈ p.lines.map castPair)
    (hfinite : ∀ c ∈ p.checks, ∀ Y ∈ Icc (c.spatial.lo : ℝ) c.spatial.hi,
      coefJ c.activity Y - (c.slope : ℝ) * childR c.activity Y ≤ c.intercept)
    (hchain : ∀ c ∈ p.chain, chainMeaning c) (hT : 0 ≤ T) :
    coefJ lam T ≤ polygonU (p.lines.map castPair) cap (childR lam T) := by
  have hlines := polygonCoverageCheck_lines h hfinite hchain
  have h' := h
  simp only [polygonCoverageCheck, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at h'
  have hmax : (p.activity : ℝ) ≤ 5/2 := by
    have hh : (p.activity : ℝ) ≤ ((5/2 : Rat) : ℝ) := Rat.cast_mono h'.1.1.1.1.2.1
    norm_num at hh
    exact hh
  have hb : ∀ line ∈ p.lines, 0 ≤ (line.2 : ℝ) := by
    intro line hl
    exact_mod_cast h'.1.1.1.2 line hl
  have htransport : ∀ line ∈ p.lines.map castPair,
      coefJ lam T ≤ polygonLine line (childR lam T) := by
    intro line hl
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl
    exact child_polygon_line_transport hlam hll hmax hT (hb q hq) (hlines q hq T hT)
  apply (le_polygonU_iff _ _ _ _).mpr
  refine ⟨?_, htransport⟩
  simpa only [polygonLine, zero_mul, add_zero] using htransport (cap,0) hcapline

/-- Named finite metadata facts for the numerical soundness consumers. -/
structure ActivityCoverageFacts (a : Activity) (p : Polygon) : Prop where
  segment_le : a.segment ≤ 5
  lo_pos : 0 < a.activity.lo
  center_lo : a.activity.lo ≤ a.center
  center_hi : a.center ≤ a.activity.hi
  center_mid : a.center = (a.activity.lo+a.activity.hi)/2
  hi_polygon : a.activity.hi ≤ a.polygonActivity
  polygon_max : a.polygonActivity ≤ 5/2
  polygon_activity : p.activity = a.polygonActivity
  left_pos : 0 < a.leftEnd
  left_three : a.leftEnd ≤ 3
  zero_k_pos : 0 < loRat (point a.activity.hi 0).k
  three_k_pos : 0 < loRat (point a.activity.hi 3).k
  large_n_upper_neg : capARat (parameters a.segment) a.activity.lo - 1 -
    gammaRat (parameters a.segment) a.activity.hi -
    alphaRat (parameters a.segment) a.activity.hi / hiRat (point a.activity.hi 3).k < 0
  geometry : polygonGeometryCheck p.lines a.Jcap a.vertices = true
  vertex_rows : ∀ c ∈ a.vertexChecks,
    a.leftEnd ≤ c.spatial.lo ∧ c.spatial.lo ≤ c.spatial.hi ∧ c.spatial.hi ≤ 3 ∧
      0 ≤ c.r ∧ 0 ≤ c.J ∧ c.J ≤ a.Jcap
  ca_rows : ∀ c ∈ a.caChecks,
    1/500 ≤ c.spatial.lo ∧ c.spatial.lo ≤ c.spatial.hi ∧ c.spatial.hi ≤ 3

theorem activityCoverageCheck_facts {a : Activity} {p : Polygon}
    (h : activityCoverageCheck a p = true) : ActivityCoverageFacts a p := by
  simp only [activityCoverageCheck, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at h
  rcases h.1.1.1.1.1 with
    ⟨hs, hlo, hcl, hch, hmid, hp, hpmax, hpa, hyl, hyl3, hpb, hp3, hN⟩
  exact ⟨hs,hlo,hcl,hch,hmid,hp,hpmax,hpa,hyl,hyl3,hpb,hp3,hN,
    h.1.1.1.1.2,h.1.1.1.2,h.1.2⟩

/-- An accepted vertex tag retains an actual source row and its identity. -/
theorem rowAt_sound {rows : List VertexCheck} {v : Rat × Rat} {tag : Bool}
    (h : rowAt rows v tag = true) :
    ∃ c ∈ rows, c.r = v.1 ∧ c.J = v.2 ∧ c.useGamma = tag := by
  obtain ⟨c, hc, hh⟩ := List.any_eq_true.mp h
  exact ⟨c, hc, by simpa only [decide_eq_true_eq] using hh⟩

/-- Each accepted cut group retains the actual cut and every surviving
source vertex with both denominator tags, on this same spatial piece. -/
theorem cutGroupCheck_witness {a : Activity} {p : Polygon} {s : Rat × Rat}
    (h : cutGroupCheck a p s = true) :
    ∃ rmin : Rat, 0 ≤ rmin ∧ cutSafe a.activity.lo s.2 rmin = true ∧
      ∀ v : Rat × Rat,
        (v = (rmin, polygonURat p.lines a.Jcap rmin) ∨
          (v ∈ a.vertices ∧ rmin ≤ v.1)) → ∀ tag : Bool,
        ∃ c ∈ a.vertexChecks, spanPair c.spatial = s ∧
          c.r = v.1 ∧ c.J = v.2 ∧ c.useGamma = tag := by
  unfold cutGroupCheck at h
  cases hc : groupCut (spatialRows a s) with
  | none => simp only [hc, Bool.false_eq_true] at h
  | some rmin =>
      simp only [hc, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true] at h
      rcases h with ⟨⟨⟨⟨⟨hr, hsafe⟩, hcut0⟩, hcut1⟩, hvertices⟩, _⟩
      refine ⟨rmin, hr, hsafe, ?_⟩
      intro v hv tag
      have htag : rowAt (spatialRows a s) v tag = true := by
        rcases hv with hcut | ⟨hvm, hvr⟩
        · subst v
          cases tag
          · exact hcut0
          · exact hcut1
        · have hh := hvertices v hvm
          simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hh
          rcases hh with hh | hh
          · exact False.elim (not_lt_of_ge hvr hh)
          · cases tag
            · exact hh.1
            · exact hh.2
      obtain ⟨c, hc, hcv⟩ := rowAt_sound htag
      have hcf := List.mem_filter.mp hc
      refine ⟨c, hcf.1, ?_, hcv⟩
      simpa only [decide_eq_true_eq] using hcf.2

/-- The cut groups themselves cover every parent coordinate in the core. -/
theorem activityCoverageCheck_cut_groups {a : Activity} {p : Polygon}
    (h : activityCoverageCheck a p = true) (huse : a.useCut = true)
    {Y : ℝ} (hY : Y ∈ Icc (a.leftEnd : ℝ) 3) :
    ∃ s ∈ spatialGroups a, Y ∈ Icc (s.1 : ℝ) s.2 ∧ cutGroupCheck a p s = true := by
  simp only [activityCoverageCheck, huse, if_true,
    Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨s, hs, hYs⟩ := partitionFrom_covers h.1.1.2.1 hY
  exact ⟨s, hs, hYs, h.1.1.2.2 s hs⟩

/-- In an uncut row, every exported vertex and both tags retain a covering
checked spatial recipe, including the shared closed endpoints. -/
theorem activityCoverageCheck_uncut_vertices {a : Activity} {p : Polygon}
    (h : activityCoverageCheck a p = true) (huse : a.useCut = false)
    {Y : ℝ} (hY : Y ∈ Icc (a.leftEnd : ℝ) 3) {v : Rat × Rat}
    (hv : v ∈ a.vertices) (tag : Bool) :
    ∃ c ∈ a.vertexChecks, c.r = v.1 ∧ c.J = v.2 ∧ c.useGamma = tag ∧
      Y ∈ Icc (c.spatial.lo : ℝ) c.spatial.hi := by
  simp only [activityCoverageCheck, huse, Bool.false_eq_true, if_false,
    Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  have hp := h.1.1.2.1 v hv
  have hpart : partitionFrom a.leftEnd 3 (vertexPieces a v tag) = true := by
    cases tag
    · exact hp.1
    · exact hp.2
  obtain ⟨piece, hm, hpiece⟩ := partitionFrom_covers hpart hY
  obtain ⟨c, hc, hcp⟩ := List.mem_map.mp hm
  have hcf := List.mem_filter.mp hc
  have hcv : c.r = v.1 ∧ c.J = v.2 ∧ c.useGamma = tag := by
    simpa only [decide_eq_true_eq] using hcf.2
  exact ⟨c, hcf.1, hcv.1, hcv.2.1, hcv.2.2,
    by simpa only [← hcp, spanPair] using hpiece⟩

/-- The CA list covers the whole source interval, preserving each row's
positive-L or Taylor method tag for its numerical soundness consumer. -/
theorem activityCoverageCheck_ca {a : Activity} {p : Polygon}
    (h : activityCoverageCheck a p = true) {Y : ℝ}
    (hY : Y ∈ Icc (1/500 : ℝ) 3) :
    ∃ c ∈ a.caChecks, Y ∈ Icc (c.spatial.lo : ℝ) c.spatial.hi := by
  have hp : partitionFrom (1/500) 3
      (a.caChecks.map (fun c => spanPair c.spatial)) = true := by
    exact (bool_and_true h).2
  obtain ⟨piece, hm, hpiece⟩ := partitionFrom_covers hp
    (show Y ∈ Icc ((1/500 : Rat) : ℝ) ((3 : Rat) : ℝ) from by norm_num at hY ⊢; exact hY)
  obtain ⟨c, hc, hcp⟩ := List.mem_map.mp hm
  exact ⟨c, hc, by simpa only [← hcp, spanPair] using hpiece⟩

/-- Segment identity and every endpoint survive the finite activity cover. -/
theorem segmentCoverageCheck_covers {segment : Nat} {rows : List Activity}
    (h : segmentCoverageCheck segment rows = true) {lam : ℝ}
    (hlam : lam ∈ Icc ((segmentSpan segment).1 : ℝ) (segmentSpan segment).2) :
    ∃ a ∈ rows, a.segment = segment ∧ lam ∈ Icc (a.activity.lo : ℝ) a.activity.hi := by
  simp only [segmentCoverageCheck, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at h
  obtain ⟨piece, hm, hpiece⟩ := partitionFrom_covers h.2 hlam
  obtain ⟨a, ha, hap⟩ := List.mem_map.mp hm
  exact ⟨a, ha, h.1.2 a ha, by simpa only [← hap, spanPair] using hpiece⟩

/-- A successful activity guard retains an actual polygon from the source
list, with the complete geometry and per-spatial data guard. -/
theorem activityCoverageIn_sound {polygons : List Polygon} {a : Activity}
    (h : activityCoverageIn polygons a = true) :
    ∃ p ∈ polygons, activityCoverageCheck a p = true :=
  List.any_eq_true.mp h

/-- Combined finite segment coverage selects an actual activity row and an
actual polygon recipe, never a free scalar tuple. -/
theorem segmentActivityCoverageCheck_covers {segment : Nat} {rows : List Activity}
    {polygons : List Polygon} (h : segmentActivityCoverageCheck segment rows polygons = true)
    {lam : ℝ} (hlam : lam ∈ Icc ((segmentSpan segment).1 : ℝ) (segmentSpan segment).2) :
    ∃ a ∈ rows, a.segment = segment ∧ lam ∈ Icc (a.activity.lo : ℝ) a.activity.hi ∧
      ∃ p ∈ polygons, activityCoverageCheck a p = true := by
  obtain ⟨a, ha, hs, hla⟩ := segmentCoverageCheck_covers (bool_and_true h).1 hlam
  obtain ⟨p, hp, hap⟩ := activityCoverageIn_sound
    (List.all_eq_true.mp (bool_and_true h).2 a ha)
  exact ⟨a,ha,hs,hla,p,hp,hap⟩

/-- Selected-leaf base list coverage retains the exact row and segment index. -/
theorem baseCoverageCheck_covers {segment : Nat} {rows : List BaseCheck}
    (h : baseCoverageCheck segment rows = true) {lam : ℝ}
    (hlam : lam ∈ Icc ((segmentSpan segment).1 : ℝ) (segmentSpan segment).2) :
    ∃ b ∈ rows, b.segment = segment ∧ lam ∈ Icc (b.activity.lo : ℝ) b.activity.hi := by
  simp only [baseCoverageCheck, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at h
  obtain ⟨piece, hm, hpiece⟩ := partitionFrom_covers h.2 hlam
  obtain ⟨b, hb, hbp⟩ := List.mem_map.mp hm
  exact ⟨b,hb,h.1.2 b hb,by simpa only [← hbp,spanPair] using hpiece⟩

/-- Computational coefficients equal the actual named band's fields.
The band's activity endpoints remain on `s.band` for the final consumer. -/
theorem parameters_segment_fields (s : Segment) :
    (parameters s.index).D = s.band.D ∧
    (parameters s.index).a = s.band.aCoef ∧
    (parameters s.index).g = s.band.gDen := by
  cases s <;> exact ⟨rfl,rfl,rfl⟩

/-- The numerical band's unused endpoint fields do not alter its retained
coefficient functions. The final consumer uses the actual `s.band` endpoints. -/
theorem parameters_segment_alpha (s : Segment) (lam : ℝ) :
    alpha (parameters s.index).asBand lam = alpha s.band lam := by cases s <;> rfl

theorem parameters_segment_gamma (s : Segment) (lam : ℝ) :
    gamma (parameters s.index).asBand lam = gamma s.band lam := by cases s <;> rfl

theorem parameters_segment_zBar (s : Segment) (lam Y J : ℝ) :
    zBar (parameters s.index).asBand lam Y J = zBar s.band lam Y J := by cases s <;> rfl

theorem parameters_segment_lBar (s : Segment) (lam Y : ℝ) :
    lBar (parameters s.index).asBand lam Y = lBar s.band lam Y := by cases s <;> rfl

theorem parameters_segment_vertexA (s : Segment) (lam Y r J : ℝ) :
    vertexA (parameters s.index).asBand lam Y r J = vertexA s.band lam Y r J := by cases s <;> rfl

theorem parameters_segment_vertexAgamma (s : Segment) (lam Y r J : ℝ) :
    vertexAgamma (parameters s.index).asBand lam Y r J = vertexAgamma s.band lam Y r J := by cases s <;> rfl

theorem parameters_segment_cLower (s : Segment) (lam Y Jcap : ℝ) :
    cLower (parameters s.index).asBand lam Y Jcap = cLower s.band lam Y Jcap := by cases s <;> rfl

/-- Coefficient normalization transports each checked flank field to the
actual named band; no activity endpoint is overwritten. -/
theorem parameters_segment_flankChecks (s : Segment) {lo hi YL Jcap : ℝ}
    (h : FlankChecks (parameters s.index).asBand lo hi YL Jcap) :
    FlankChecks s.band lo hi YL Jcap := by
  cases s <;>
    rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩ <;>
    exact ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩

/-- The computed activity span is exactly the named band's closed span. -/
theorem segmentSpan_index (s : Segment) :
    segmentSpan s.index = (s.band.lo,s.band.hi) := by
  cases s <;> rfl

/-- Each selected-leaf row lies inside its actual named band's endpoints. -/
theorem baseCoverageCheck_band_row_bounds {s : Segment} {rows : List BaseCheck}
    (h : baseCoverageCheck s.index rows = true) {b : BaseCheck} (hb : b ∈ rows) :
    (s.band.lo : ℝ) ≤ b.activity.lo ∧ (b.activity.lo : ℝ) ≤ b.activity.hi ∧
      (b.activity.hi : ℝ) ≤ s.band.hi := by
  have hp : partitionFrom (segmentSpan s.index).1 (segmentSpan s.index).2
      (rows.map (fun c => spanPair c.activity)) = true := (bool_and_true h).2
  have hm : spanPair b.activity ∈ rows.map (fun c => spanPair c.activity) :=
    List.mem_map.mpr ⟨b,hb,rfl⟩
  have hh := partitionFrom_member_bounds hp hm
  rw [segmentSpan_index] at hh
  exact_mod_cast hh

/-- Named segment coverage binds the row index to the actual retained band,
including its exact closed endpoints. -/
theorem segmentCoverageCheck_band_covers {s : Segment} {rows : List Activity}
    (h : segmentCoverageCheck s.index rows = true) {lam : ℝ}
    (hlam : lam ∈ Icc (s.band.lo : ℝ) s.band.hi) :
    ∃ a ∈ rows, a.segment = s.index ∧ lam ∈ Icc (a.activity.lo : ℝ) a.activity.hi := by
  apply segmentCoverageCheck_covers h
  simpa only [segmentSpan_index] using hlam

/-- Combined activity and polygon cover on the actual named closed band. -/
theorem segmentActivityCoverageCheck_band_covers {s : Segment} {rows : List Activity}
    {polygons : List Polygon} (h : segmentActivityCoverageCheck s.index rows polygons = true)
    {lam : ℝ} (hlam : lam ∈ Icc (s.band.lo : ℝ) s.band.hi) :
    ∃ a ∈ rows, a.segment = s.index ∧ lam ∈ Icc (a.activity.lo : ℝ) a.activity.hi ∧
      ∃ p ∈ polygons, activityCoverageCheck a p = true := by
  apply segmentActivityCoverageCheck_covers h
  simpa only [segmentSpan_index] using hlam

/-- Selected-leaf base cover on the same actual named closed band. -/
theorem baseCoverageCheck_band_covers {s : Segment} {rows : List BaseCheck}
    (h : baseCoverageCheck s.index rows = true) {lam : ℝ}
    (hlam : lam ∈ Icc (s.band.lo : ℝ) s.band.hi) :
    ∃ b ∈ rows, b.segment = s.index ∧ lam ∈ Icc (b.activity.lo : ℝ) b.activity.hi := by
  apply baseCoverageCheck_covers h
  simpa only [segmentSpan_index] using hlam

/-- Fixed-point rational endpoints use the same proved real semantics. -/
theorem loRat_cast (v : Ival) : (loRat v : ℝ) = toR v.lo := by
  simp only [loRat, Rat.cast_div, Rat.cast_intCast, toR]
  rw [one_eq]
  push_cast
  rfl

/-- The closed cut guard really bounds the source feasibility expression. -/
theorem cutSafe_sound {activityLo spatialHi rmin : Rat}
    (h : cutSafe activityLo spatialHi rmin = true) :
    (rmin : ℝ) ≤ max 0 (log (activityLo : ℝ) -
      log (exp (spatialHi : ℝ)-1)) / (spatialHi : ℝ) := by
  unfold cutSafe at h
  cases he : evalClosed (cutExpr activityLo spatialHi) with
  | none => simp only [he, Bool.false_eq_true] at h
  | some v =>
      have hr : rmin ≤ loRat v := by simpa only [he, decide_eq_true_eq] using h
      unfold evalClosed at he
      split at he
      next hs =>
        have hv : (cutExpr activityLo spatialHi).evalI (fun _ => zeroI) = v :=
          Option.some.inj he
        have hm := Expr.evalI_mem (cutExpr activityLo spatialHi)
          (realEnv := fun _ => 0) (fun _ => by simpa only [zeroI, toR_zero] using mem_pt 0) hs
        rw [hv] at hm
        have hrr : (rmin : ℝ) ≤ toR v.lo := by
          rw [← loRat_cast]
          exact_mod_cast hr
        exact hrr.trans (by simpa only [cutExpr, Expr.evalR, Rat.cast_zero, Rat.cast_one] using hm.1)
      next hs => simp at he

/-- A safely retained cut is below the actual child coordinate throughout
its spatial interval, by the source feasibility lemma. -/
theorem cutSafe_childR {activityLo spatialHi rmin : Rat} {lam T Y : ℝ}
    (h : cutSafe activityLo spatialHi rmin = true) (hlo : 0 < (activityLo : ℝ))
    (hlam : (activityLo : ℝ) ≤ lam) (hT : 0 ≤ T)
    (hTY : lmass lam T ≤ Y) (hY : Y ≤ (spatialHi : ℝ)) :
    (rmin : ℝ) ≤ childR lam T :=
  (cutSafe_sound h).trans (childR_ge_feasibility_cut hlo hlam hT hTY hY)

end Compute
end Erdos993Lean.Analytic.HandVariance
