import Erdos993Lean.Analytic.HandVariance.Child
import Erdos993Lean.Analytic.HandVariance.Taylor
import Erdos993Lean.Analytic.HandVariance.Flanks

/-!
# Finite polygon coverage and comparison with its checked vertices

Source: TWIN v1.8 `apx_hand.tex`, Proposition `tgt:prop:red` and the
finite polygon Taylor partitions following `tgt:lem:poly`.
The geometric certificate retains the supplied vertex list, every finite
edge's supporting line, the cut coordinate, and the cap ray. Its premises
are finite endpoint equalities and inequalities, rather than a pointwise
comparison on an unbounded child region.
-/

namespace Erdos993Lean.Analytic.HandVariance

open Real Reserve Set

/-- An upper line of the source child polygon. -/
noncomputable def polygonLine (line : ℝ × ℝ) (r : ℝ) : ℝ := line.1 + line.2 * r

/-- Source: `tgt:prop:red`, the upper envelope `U`, retaining its finite
line list and its cap. The cap may also occur as the final zero-slope line. -/
noncomputable def polygonU : List (ℝ × ℝ) → ℝ → ℝ → ℝ
  | [], cap, _ => cap
  | line :: lines, cap, r => min (polygonLine line r) (polygonU lines cap r)

/-- Source: the polygon inequalities in `tgt:prop:red`; a bound by `U`
retains the cap and every individual upper line. -/
theorem le_polygonU_iff (lines : List (ℝ × ℝ)) (cap r J : ℝ) :
    J ≤ polygonU lines cap r ↔ J ≤ cap ∧ ∀ line ∈ lines, J ≤ polygonLine line r := by
  induction lines with
  | nil => simp [polygonU]
  | cons line lines ih =>
      rw [polygonU, le_min_iff, ih]
      constructor
      · rintro ⟨hline, hcap, hrest⟩
        refine ⟨hcap, ?_⟩
        intro other ho
        rcases List.mem_cons.mp ho with h | h
        · subst other
          exact hline
        · exact hrest other h
      · rintro ⟨hcap, hlines⟩
        refine ⟨hlines line (by simp), hcap, ?_⟩
        intro other ho
        exact hlines other (List.mem_cons_of_mem line ho)

/-- Source: `tgt:prop:red`, the envelope is bounded by its cap. -/
theorem polygonU_le_cap (lines : List (ℝ × ℝ)) (cap r : ℝ) :
    polygonU lines cap r ≤ cap :=
  ((le_polygonU_iff lines cap r (polygonU lines cap r)).mp le_rfl).1

/-- Source: `tgt:prop:red`, the envelope is bounded by each retained line. -/
theorem polygonU_le_line {lines : List (ℝ × ℝ)} {cap r : ℝ}
    {line : ℝ × ℝ} (hl : line ∈ lines) : polygonU lines cap r ≤ polygonLine line r :=
  ((le_polygonU_iff lines cap r (polygonU lines cap r)).mp le_rfl).2 line hl

/-- Exact interpolation of a source affine upper line. -/
theorem polygonLine_mix (line : ℝ × ℝ) {w0 w1 r0 r1 : ℝ}
    (hw : w0 + w1 = 1) :
    polygonLine line (w0 * r0 + w1 * r1) =
      w0 * polygonLine line r0 + w1 * polygonLine line r1 := by
  unfold polygonLine
  calc
    line.1 + line.2 * (w0 * r0 + w1 * r1) =
        (w0 + w1) * line.1 + line.2 * (w0 * r0 + w1 * r1) := by rw [hw, one_mul]
    _ = _ := by ring

/-- Source: `tgt:prop:red`; the finite endpoint tests certify the actual
upper edge between two retained vertices. -/
theorem polygonU_mix_eq {lines : List (ℝ × ℝ)} {cap : ℝ} {line : ℝ × ℝ}
    {r0 r1 J0 J1 w0 w1 : ℝ} (hl : line ∈ lines)
    (hU0 : J0 = polygonU lines cap r0) (hU1 : J1 = polygonU lines cap r1)
    (hline0 : J0 = polygonLine line r0) (hline1 : J1 = polygonLine line r1)
    (hw0 : 0 ≤ w0) (hw1 : 0 ≤ w1) (hw : w0 + w1 = 1) :
    polygonU lines cap (w0 * r0 + w1 * r1) = w0 * J0 + w1 * J1 := by
  apply le_antisymm
  · calc
      polygonU lines cap (w0 * r0 + w1 * r1) ≤
          polygonLine line (w0 * r0 + w1 * r1) := polygonU_le_line hl
      _ = w0 * J0 + w1 * J1 := by rw [polygonLine_mix line hw, ← hline0, ← hline1]
  · apply (le_polygonU_iff lines cap _ _).mpr
    constructor
    · have hcap0 : J0 ≤ cap := by rw [hU0]; exact polygonU_le_cap lines cap r0
      have hcap1 : J1 ≤ cap := by rw [hU1]; exact polygonU_le_cap lines cap r1
      calc
        w0 * J0 + w1 * J1 ≤ w0 * cap + w1 * cap :=
          add_le_add (mul_le_mul_of_nonneg_left hcap0 hw0)
            (mul_le_mul_of_nonneg_left hcap1 hw1)
        _ = cap := by rw [← add_mul, hw, one_mul]
    · intro other ho
      have h0 : J0 ≤ polygonLine other r0 := by rw [hU0]; exact polygonU_le_line ho
      have h1 : J1 ≤ polygonLine other r1 := by rw [hU1]; exact polygonU_le_line ho
      rw [polygonLine_mix other hw]
      exact add_le_add (mul_le_mul_of_nonneg_left h0 hw0)
        (mul_le_mul_of_nonneg_left h1 hw1)

/-- Every point of a closed interval retains explicit interpolation weights.
The degenerate case is included for a cut at an existing vertex. -/
theorem exists_segment_weights {a b x : ℝ} (hx : x ∈ Icc a b) :
    ∃ w0 w1 : ℝ, 0 ≤ w0 ∧ 0 ≤ w1 ∧ w0 + w1 = 1 ∧ x = w0 * a + w1 * b := by
  rcases eq_or_lt_of_le (hx.1.trans hx.2) with hab | hab
  · have hxa : x = a := by linarith [hx.1, hx.2]
    refine ⟨1, 0, by norm_num, by norm_num, by norm_num, ?_⟩
    rw [hxa]
    ring
  · have hd : 0 < b - a := sub_pos.mpr hab
    refine ⟨(b - x) / (b - a), (x - a) / (b - a),
      div_nonneg (sub_nonneg.mpr hx.2) hd.le,
      div_nonneg (sub_nonneg.mpr hx.1) hd.le, ?_, ?_⟩
    · field_simp [hd.ne']
      ring
    · field_simp [hd.ne']
      ring

/-- Source: `tgt:prop:red`; a certified supporting line equals `U`
throughout its edge, derived from finite endpoint data. -/
theorem polygonU_eq_on_edge {lines : List (ℝ × ℝ)} {cap : ℝ} {line : ℝ × ℝ}
    {r0 r1 J0 J1 r : ℝ} (hl : line ∈ lines)
    (hU0 : J0 = polygonU lines cap r0) (hU1 : J1 = polygonU lines cap r1)
    (hline0 : J0 = polygonLine line r0) (hline1 : J1 = polygonLine line r1)
    (hr : r ∈ Icc r0 r1) : polygonU lines cap r = polygonLine line r := by
  obtain ⟨w0, w1, hw0, hw1, hw, hmix⟩ := exists_segment_weights hr
  rw [hmix, polygonU_mix_eq hl hU0 hU1 hline0 hline1 hw0 hw1 hw,
    polygonLine_mix line hw, ← hline0, ← hline1]

/-- Source: `tgt:prop:red`; nonnegative slopes extend the last capped
vertex to the entire cap ray. -/
theorem polygonU_eq_cap_of_ge {lines : List (ℝ × ℝ)} {cap r0 r : ℝ}
    (hb : ∀ line ∈ lines, 0 ≤ line.2) (hcap : polygonU lines cap r0 = cap)
    (hr : r0 ≤ r) : polygonU lines cap r = cap := by
  apply le_antisymm (polygonU_le_cap lines cap r)
  apply (le_polygonU_iff lines cap r cap).mpr
  refine ⟨le_rfl, ?_⟩
  intro line hl
  calc
    cap = polygonU lines cap r0 := hcap.symm
    _ ≤ polygonLine line r0 := polygonU_le_line hl
    _ ≤ polygonLine line r := by
      unfold polygonLine
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hr (hb line hl))

/-- Finite sorted endpoints cover every point to their right by an actual
adjacent pair or by the terminal ray. Used for both polygon edges and tails. -/
theorem exists_chain_edge_or_ray (n : ℕ) (t : ℕ → ℝ)
    (hinc : ∀ i < n, t i < t (i + 1)) {x : ℝ} (hx : t 0 ≤ x) :
    t n ≤ x ∨ ∃ i < n, x ∈ Icc (t i) (t (i + 1)) := by
  induction n generalizing t with
  | zero => exact Or.inl hx
  | succ n ih =>
      by_cases hx1 : x ≤ t 1
      · exact Or.inr ⟨0, by omega, hx, hx1⟩
      · rcases ih (fun i => t (i + 1))
          (fun i hi => hinc (i + 1) (by omega)) (le_of_not_ge hx1) with h | ⟨i, hi, hxi⟩
        · exact Or.inl h
        · exact Or.inr ⟨i + 1, by omega, hxi⟩

/-- Source: `tgt:prop:red`, the finite geometric certificate for the exact
exported vertex list. Every premise is a finite endpoint test. -/
structure PolygonGeometry (lines : List (ℝ × ℝ)) (cap : ℝ)
    (vertices : List (ℝ × ℝ)) where
  size : ℕ
  node : ℕ → ℝ × ℝ
  vertices_eq : vertices = List.ofFn (fun i : Fin (size + 1) => node i.val)
  initial : (node 0).1 = 0
  increasing : ∀ i : Fin size, (node i.val).1 < (node (i.val + 1)).1
  nonnegative : ∀ i : Fin (size + 1), 0 ≤ (node i.val).2
  upper : ∀ i : Fin (size + 1), (node i.val).2 = polygonU lines cap (node i.val).1
  last_cap : (node size).2 = cap
  edge : ∀ i : Fin size, ∃ line ∈ lines,
    (node i.val).2 = polygonLine line (node i.val).1 ∧
      (node (i.val + 1)).2 = polygonLine line (node (i.val + 1)).1

/-- The geometric certificate's nodes occur in its retained vertex list. -/
theorem PolygonGeometry.node_mem {lines : List (ℝ × ℝ)} {cap : ℝ}
    {vertices : List (ℝ × ℝ)} (g : PolygonGeometry lines cap vertices)
    {i : ℕ} (hi : i ≤ g.size) : g.node i ∈ vertices := by
  have hm : g.node i ∈ List.ofFn (fun j : Fin (g.size+1) => g.node j.val) :=
    List.mem_ofFn.mpr ⟨⟨i, by omega⟩, rfl⟩
  exact (congrArg (fun vs => g.node i ∈ vs) g.vertices_eq).mpr hm

/-- Source: `tgt:prop:red`; the finite geometry proves the cap is physical. -/
theorem PolygonGeometry.cap_nonneg {lines : List (ℝ × ℝ)} {cap : ℝ}
    {vertices : List (ℝ × ℝ)} (g : PolygonGeometry lines cap vertices) : 0 ≤ cap := by
  rw [← g.last_cap]
  exact g.nonnegative ⟨g.size, by omega⟩

/-- Source: `tgt:prop:red`; the finite geometry proves `U` is nonnegative
on the entire physical half-line. -/
theorem PolygonGeometry.upper_mem {lines : List (ℝ × ℝ)} {cap : ℝ}
    {vertices : List (ℝ × ℝ)} (g : PolygonGeometry lines cap vertices)
    (hb : ∀ line ∈ lines, 0 ≤ line.2) {r : ℝ} (hr : 0 ≤ r) :
    polygonU lines cap r ∈ Icc 0 cap := by
  refine ⟨?_, polygonU_le_cap lines cap r⟩
  have hstart : (g.node 0).1 ≤ r := by rw [g.initial]; exact hr
  rcases exists_chain_edge_or_ray g.size (fun i => (g.node i).1)
      (fun i hi => g.increasing ⟨i, hi⟩) hstart with hlast | ⟨i, hi, hri⟩
  · have hcap : polygonU lines cap (g.node g.size).1 = cap :=
      (g.upper ⟨g.size, by omega⟩).symm.trans g.last_cap
    rw [polygonU_eq_cap_of_ge hb hcap hlast]
    exact g.cap_nonneg
  · obtain ⟨line, hl, hline0, hline1⟩ := g.edge ⟨i, hi⟩
    obtain ⟨w0, w1, hw0, hw1, hw, hmix⟩ := exists_segment_weights hri
    rw [hmix, polygonU_mix_eq hl (g.upper ⟨i, by omega⟩)
      (g.upper ⟨i + 1, by omega⟩) hline0 hline1 hw0 hw1 hw]
    exact add_nonneg (mul_nonneg hw0 (g.nonnegative ⟨i, by omega⟩))
      (mul_nonneg hw1 (g.nonnegative ⟨i + 1, by omega⟩))

/-- Source: the finite Taylor partition after `tgt:lem:poly`; a contiguous
list of closed pieces retains a covering piece for every point of its range. -/
theorem exists_piece_of_list_partition {pieces : List (ℝ × ℝ)}
    (hchain : pieces.IsChain (fun a b => a.2 = b.1))
    {first last : ℝ × ℝ} (hfirst : pieces.head? = some first)
    (hlast : pieces.getLast? = some last) {x : ℝ} (hx : x ∈ Icc first.1 last.2) :
    ∃ piece ∈ pieces, x ∈ Icc piece.1 piece.2 := by
  induction pieces generalizing first last with
  | nil => simp at hfirst
  | cons a pieces ih =>
      have ha : a = first := Option.some.inj (by simpa using hfirst)
      subst first
      cases pieces with
      | nil =>
          have ha : a = last := Option.some.inj (by simpa using hlast)
          subst last
          exact ⟨a, by simp, hx⟩
      | cons b pieces =>
          obtain ⟨hab, htail⟩ := List.isChain_cons_cons.mp hchain
          have hlast' : (b :: pieces).getLast? = some last := by simpa using hlast
          by_cases hxa : x ≤ a.2
          · exact ⟨a, by simp, hx.1, hxa⟩
          · have hxb : b.1 ≤ x := by rw [← hab]; exact le_of_not_ge hxa
            obtain ⟨piece, hp, hxp⟩ := ih htail (by simp) hlast' ⟨hxb, hx.2⟩
            exact ⟨piece, List.mem_cons_of_mem a hp, hxp⟩

/-- Source: the finite Taylor partition after `tgt:lem:poly`; actual
piecewise analytic certificates cover the full checked interval. -/
theorem bound_on_list_partition {pieces : List (ℝ × ℝ)}
    (hchain : pieces.IsChain (fun a b => a.2 = b.1))
    {first last : ℝ × ℝ} (hfirst : pieces.head? = some first)
    (hlast : pieces.getLast? = some last) (P : ℝ → Prop)
    (hpiece : ∀ piece ∈ pieces, ∀ x ∈ Icc piece.1 piece.2, P x)
    {x : ℝ} (hx : x ∈ Icc first.1 last.2) : P x := by
  obtain ⟨piece, hp, hxp⟩ := exists_piece_of_list_partition hchain hfirst hlast hx
  exact hpiece piece hp x hxp

/-- Source: `tgt:prop:red`; endpoint bounds on an actual finite upper edge
certify every point below that edge. -/
theorem polygonFloor_lower_on_edge {c : Band} {lam Y cap m : ℝ}
    {lines : List (ℝ × ℝ)} {line : ℝ × ℝ} {r0 r1 J0 J1 r J : ℝ}
    (hγ : 0 < gamma c lam)
    (hZ : ∀ j ∈ Icc 0 cap, 0 < zBar c lam Y j)
    (hl : line ∈ lines)
    (hU0 : J0 = polygonU lines cap r0) (hU1 : J1 = polygonU lines cap r1)
    (hline0 : J0 = polygonLine line r0) (hline1 : J1 = polygonLine line r1)
    (hJ0 : J0 ∈ Icc 0 cap) (hJ1 : J1 ∈ Icc 0 cap)
    (hf0 : m ≤ polygonFloor c lam Y r0 J0) (hf1 : m ≤ polygonFloor c lam Y r1 J1)
    (hr : r ∈ Icc r0 r1) (hJ : 0 ≤ J) (hJU : J ≤ polygonU lines cap r) :
    m ≤ polygonFloor c lam Y r J := by
  obtain ⟨w0, w1, hw0, hw1, hw, hmix⟩ := exists_segment_weights hr
  have hu := polygonU_mix_eq hl hU0 hU1 hline0 hline1 hw0 hw1 hw
  have htop : w0 * J0 + w1 * J1 ∈ Icc 0 cap := by
    constructor
    · exact add_nonneg (mul_nonneg hw0 hJ0.1) (mul_nonneg hw1 hJ1.1)
    · calc
        w0 * J0 + w1 * J1 ≤ w0 * cap + w1 * cap :=
          add_le_add (mul_le_mul_of_nonneg_left hJ0.2 hw0)
            (mul_le_mul_of_nonneg_left hJ1.2 hw1)
        _ = cap := by rw [← add_mul, hw, one_mul]
  have hJtop : J ≤ w0 * J0 + w1 * J1 := by rw [hmix, hu] at hJU; exact hJU
  have hJcap : J ∈ Icc 0 cap := ⟨hJ, hJtop.trans htop.2⟩
  have hfloor := polygonFloor_mix_le (r0 := r0) (r1 := r1)
    hγ (hZ J0 hJ0) (hZ J1 hJ1) hw0 hw1 hw
  have hm : m ≤ w0 * polygonFloor c lam Y r0 J0 +
      w1 * polygonFloor c lam Y r1 J1 := by
    calc
      m = w0 * m + w1 * m := by rw [← add_mul, hw, one_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hf0 hw0)
        (mul_le_mul_of_nonneg_left hf1 hw1)
  calc
    m ≤ polygonFloor c lam Y (w0 * r0 + w1 * r1) (w0 * J0 + w1 * J1) := hm.trans hfloor
    _ ≤ polygonFloor c lam Y r J := by
      rw [← hmix]
      exact polygonFloor_antitone_J hγ hJtop (hZ J hJcap) (hZ _ htop)

/-- Source: Proposition `tgt:prop:red`. The supplied finite vertices to the
right of the cut and the actual cut point suffice for the full child region.
The parent, actual child coordinates, finite vertex list and every positive
denominator on `[0,cap]` remain explicit. -/
theorem vertexA_lower_of_polygon_geometry {c : Band} {lam Y cap rmin m r J : ℝ}
    {lines vertices : List (ℝ × ℝ)} (g : PolygonGeometry lines cap vertices)
    (hb : ∀ line ∈ lines, 0 ≤ line.2) (hα : 0 ≤ alpha c lam) (hγ : 0 < gamma c lam)
    (hZ : ∀ j ∈ Icc 0 cap, 0 < zBar c lam Y j) (hrmin : 0 ≤ rmin)
    (hvertices : ∀ v ∈ vertices, rmin ≤ v.1 →
      m ≤ vertexA c lam Y v.1 v.2 ∧ m ≤ vertexAgamma c lam Y v.1 v.2)
    (hcut : m ≤ vertexA c lam Y rmin (polygonU lines cap rmin) ∧
      m ≤ vertexAgamma c lam Y rmin (polygonU lines cap rmin))
    (hr : rmin ≤ r) (hJ : 0 ≤ J) (hJU : J ≤ polygonU lines cap r) :
    m ≤ vertexA c lam Y r J := by
  have hr0 : 0 ≤ r := hrmin.trans hr
  have hJUcap := g.upper_mem hb hr0
  have hJcap : J ∈ Icc 0 cap := ⟨hJ, hJU.trans hJUcap.2⟩
  have hcutfloor : m ≤ polygonFloor c lam Y rmin (polygonU lines cap rmin) :=
    le_min hcut.1 hcut.2
  have hnodefloor : ∀ i ≤ g.size, rmin ≤ (g.node i).1 →
      m ≤ polygonFloor c lam Y (g.node i).1 (g.node i).2 := by
    intro i hi hri
    exact le_min (hvertices (g.node i) (g.node_mem hi) hri).1
      (hvertices (g.node i) (g.node_mem hi) hri).2
  have hstart : (g.node 0).1 ≤ r := by rw [g.initial]; exact hr0
  have hfloor : m ≤ polygonFloor c lam Y r J := by
    rcases exists_chain_edge_or_ray g.size (fun i => (g.node i).1)
        (fun i hi => g.increasing ⟨i, hi⟩) hstart with hlast | ⟨i, hi, hri⟩
    · have hcap : polygonU lines cap (g.node g.size).1 = cap :=
        (g.upper ⟨g.size, by omega⟩).symm.trans g.last_cap
      by_cases hminlast : rmin ≤ (g.node g.size).1
      · have hlastfloor : m ≤ polygonFloor c lam Y (g.node g.size).1 cap := by
          simpa only [g.last_cap] using hnodefloor g.size le_rfl hminlast
        exact (hlastfloor.trans (polygonFloor_mono_r hα hlast)).trans
          (polygonFloor_antitone_J hγ hJcap.2 (hZ J hJcap) (hZ cap ⟨g.cap_nonneg, le_rfl⟩))
      · have hUcut : polygonU lines cap rmin = cap :=
          polygonU_eq_cap_of_ge hb hcap (le_of_not_ge hminlast)
        rw [hUcut] at hcutfloor
        exact (hcutfloor.trans (polygonFloor_mono_r hα hr)).trans
          (polygonFloor_antitone_J hγ hJcap.2 (hZ J hJcap) (hZ cap ⟨g.cap_nonneg, le_rfl⟩))
    · obtain ⟨line, hl, hline0, hline1⟩ := g.edge ⟨i, hi⟩
      have hu0 := g.upper ⟨i, by omega⟩
      have hu1 := g.upper ⟨i + 1, by omega⟩
      have hright : rmin ≤ (g.node (i + 1)).1 := hr.trans hri.2
      have hrightfloor := hnodefloor (i + 1) (by omega) hright
      have hrightheight : (g.node (i + 1)).2 ∈ Icc 0 cap := by
        rw [hu1]
        exact g.upper_mem hb (hrmin.trans hright)
      by_cases hminleft : rmin ≤ (g.node i).1
      · have hleftheight : (g.node i).2 ∈ Icc 0 cap := by
          rw [hu0]
          exact g.upper_mem hb (hrmin.trans hminleft)
        exact polygonFloor_lower_on_edge hγ hZ hl hu0 hu1 hline0 hline1
          hleftheight hrightheight (hnodefloor i (by omega) hminleft) hrightfloor hri hJ hJU
      · have hcutedge : rmin ∈ Icc (g.node i).1 (g.node (i + 1)).1 :=
          ⟨le_of_not_ge hminleft, hright⟩
        have hcutline := polygonU_eq_on_edge hl hu0 hu1 hline0 hline1 hcutedge
        exact polygonFloor_lower_on_edge hγ hZ hl rfl hu1 hcutline hline1
          (g.upper_mem hb hrmin) hrightheight hcutfloor hrightfloor ⟨hr, hri.2⟩ hJ hJU
  exact hfloor.trans (min_le_left _ _)

end Erdos993Lean.Analytic.HandVariance
