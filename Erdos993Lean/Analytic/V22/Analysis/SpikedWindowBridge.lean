import Erdos993Lean.Analytic.V22.Analysis.OuterCells
import Erdos993Lean.Analytic.V22.Analysis.OuterDeficits

/-! Source: frozen note Corollary 5.15, the marked spike-window bound.
The public native transport retains the class, real mean, integer M, cell,
block, and both activity halves. The shape/derivative licenses are precisely
the conditions checked at N0=mu_D*t_a+2. The first transport does not assume
the B3 minimum certificate that it is intended to help lane D establish.
Parent owns Lean verification. -/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

noncomputable section

def spikeWindowMinimum (k : V22.V22Class) (cell : V22.V22SpikeCell) (t r : ℝ) : ℝ :=
  V22.Checks.windowCellMinimum k ⟨cell.classId, cell.lo, cell.hi⟩ t r

def spikeWindowBound (k : V22.V22Class) (cell : V22.V22SpikeCell) (t r : ℝ) : ℝ :=
  let Na := (k.muD : ℝ) * (cell.lo : ℝ) + 2
  V22.positivePart (V22.psi t + V22.targetLine k.b k.beta t +
    (cell.hi : ℝ) * Na / (Na - 2) * V22.positivePart (-spikeWindowMinimum k cell t r))

/-- The actual all-integer fiber bound at a marked spike-cell start.
The explicit licenses are exactly the source shape and derivative clauses,
and may be supplied independently of the numerical B3 minimum. -/
theorem spike_window_cell_fiber {cell : V22.V22SpikeCell} (hc : cell ∈ V22.spikeCells)
    {k : V22.V22Class} (hk : k ∈ V22.classes) (hid : k.classId = cell.classId)
    {M : ℕ} {r mu : ℝ} (hM : 8 ≤ M)
    (har : (k.ra : ℝ) ≤ r) (hrrb : r ≤ (k.rb : ℝ))
    (hmuD : (k.muD : ℝ) ≤ mu)
    (ht : V22.Checks.inCell cell.lo cell.hi ((M : ℝ) / mu))
    (hshape : V22.persistentWindowConditions r ((k.muD : ℝ) * (cell.lo : ℝ) + 2))
    (hguard : 0 < V22.uMonoDerivative r ((k.muD : ℝ) * (cell.lo : ℝ) + 2)) (j : ℤ) :
    (((M : ℝ) + 2) / mu) * spikeWindowMinimum k cell ((M : ℝ) / mu) r ≤
      V22.fiberFunction ((1 + r) / 2) mu M j := by
  obtain ⟨hra, hrb, _, _, _, _, _, _, _, _, hmu40, _, _⟩ := window_class_domains hk
  obtain ⟨hlo, _, _, hma, hmaeq⟩ := outer_cell_metadata hc hk hid
  have hmu : 0 < mu := by linarith
  have hlo0 : 0 ≤ (cell.lo : ℝ) := by linarith
  have hNa : 10 ≤ (k.muD : ℝ) * (cell.lo : ℝ) + 2 := by linarith
  have haN : (k.muD : ℝ) * (cell.lo : ℝ) + 2 ≤ (M : ℝ) + 2 := by
    have hMlo := (le_div_iff₀ hmu).1 ht.1
    have hprod := mul_le_mul_of_nonneg_right hmuD hlo0
    nlinarith
  let ks : V22.V22Class := { k with tau := cell.lo }
  let wc : V22.V22Cell := ⟨cell.classId, cell.lo, cell.hi⟩
  have h := window_class_cell_fiber (c := ks) (cell := wc) hra har hrrb hrb
    hNa le_rfl haN hmu hshape hguard j
  change (((M : ℝ) + 2) / mu) * spikeWindowMinimum k cell ((M : ℝ) / mu) r ≤ _ at h
  exact h

/-- Source window bound (psi+g+Bmax*(-X)_+)_+ for the actual full
integer infimum, rather than an interpolation or a finite-support surrogate. -/
theorem spike_window_deficit_positive {cell : V22.V22SpikeCell} (hc : cell ∈ V22.spikeCells)
    {k : V22.V22Class} (hk : k ∈ V22.classes) (hid : k.classId = cell.classId)
    {M : ℕ} {r mu : ℝ} (hM : 8 ≤ M)
    (har : (k.ra : ℝ) ≤ r) (hrrb : r ≤ (k.rb : ℝ))
    (hmuD : (k.muD : ℝ) ≤ mu)
    (ht : V22.Checks.inCell cell.lo cell.hi ((M : ℝ) / mu))
    (hshape : V22.persistentWindowConditions r ((k.muD : ℝ) * (cell.lo : ℝ) + 2))
    (hguard : 0 < V22.uMonoDerivative r ((k.muD : ℝ) * (cell.lo : ℝ) + 2)) :
    V22.deficitG ((1 + r) / 2) mu k.b k.beta M ≤ spikeWindowBound k cell ((M : ℝ) / mu) r := by
  obtain ⟨hra, hrb, _, _, _, _, _, _, _, _, hmu40, _, _⟩ := window_class_domains hk
  obtain ⟨hlo, _, _, hma, hmaeq⟩ := outer_cell_metadata hc hk hid
  have hmu : 0 < mu := by linarith
  have hr0 : 0 ≤ r := (hra.trans_le har).le
  have hrh : r ≤ 1 / 2 := hrrb.trans hrb
  let Na : ℝ := (k.muD : ℝ) * (cell.lo : ℝ) + 2
  let B : ℝ := ((M : ℝ) + 2) / mu
  let X : ℝ := spikeWindowMinimum k cell ((M : ℝ) / mu) r
  let Bmax : ℝ := (cell.hi : ℝ) * Na / (Na - 2)
  have hNa : 10 ≤ Na := by dsimp [Na]; linarith
  have haN : Na ≤ (M : ℝ) + 2 := by
    have hMlo := (le_div_iff₀ hmu).1 ht.1
    have hprod := mul_le_mul_of_nonneg_right hmuD (show 0 ≤ (cell.lo : ℝ) from by linarith)
    dsimp [Na]
    nlinarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hBmax : B ≤ Bmax := by
    have hscale := (window_size_scaling hmu hNa haN).2
    have htprod := mul_le_mul_of_nonneg_right ht.2 (show 0 ≤ Na from by linarith)
    exact hscale.trans (div_le_div_of_nonneg_right htprod (show 0 ≤ Na - 2 from by linarith))
  obtain ⟨j, hj, _⟩ := shared_fiberInfimum_attained (mu := mu)
    (show 0 ≤ (1+r)/2 from by linarith) (show (1+r)/2 ≤ 1 from by linarith) M
  have hF := spike_window_cell_fiber hc hk hid hM har hrrb hmuD ht hshape hguard j
  change B * X ≤ V22.fiberFunction ((1+r)/2) mu M j at hF
  have hcost : -B * X ≤ Bmax * V22.positivePart (-X) := by
    by_cases hx : 0 ≤ X
    · have hleft : -B * X ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hB) hx
      have hz : V22.positivePart (-X) = 0 := max_eq_right (by linarith)
      rw [hz, mul_zero]
      exact hleft
    · have hx0 : 0 ≤ -X := by linarith
      have hz : V22.positivePart (-X) = -X := max_eq_left hx0
      rw [hz]
      have hmul := mul_le_mul_of_nonneg_right hBmax hx0
      nlinarith
  unfold V22.deficitG spikeWindowBound V22.positivePart
  rw [hj]
  apply max_le_max _ le_rfl
  change V22.psi ((M : ℝ) / mu) + V22.targetLine k.b k.beta ((M : ℝ) / mu) -
    V22.fiberFunction ((1+r)/2) mu M j ≤
      V22.psi ((M : ℝ) / mu) + V22.targetLine k.b k.beta ((M : ℝ) / mu) + Bmax * max (-X) 0
  change -B * X ≤ Bmax * max (-X) 0 at hcost
  linarith

/-- Public lane-D native transport, with original class/cell/M-block
domains and both q halves. The supplied source licenses are independent of
the min(Phi,Def_g) numerical certificate. -/
theorem spike_window_deficit_bound {cell : V22.V22SpikeCell} (hc : cell ∈ V22.spikeCells)
    {k : V22.V22Class} (hk : k ∈ V22.classes) (hid : k.classId = cell.classId)
    {i M : ℕ} {q mu : ℝ} (hi : i < 5) (hM : 8 ≤ M)
    (hr : V22.Checks.inCell k.ra k.rb |2*q-1|)
    (hq : V22.Checks.inCell (1/4) (3/4) q)
    (hmuD : (k.muD : ℝ) ≤ mu)
    (ht : V22.Checks.inCell cell.lo cell.hi ((M : ℝ) / mu))
    (hblock : V22.inSpikeBlock cell i (M : ℝ))
    (hshape : V22.persistentWindowConditions |2*q-1| ((k.muD : ℝ) * (cell.lo : ℝ) + 2))
    (hguard : 0 < V22.uMonoDerivative |2*q-1| ((k.muD : ℝ) * (cell.lo : ℝ) + 2)) :
    V22.deficitG q mu k.b k.beta M ≤ spikeWindowBound k cell ((M : ℝ) / mu) |2*q-1| := by
  have h := spike_window_deficit_positive hc hk hid hM hr.1 hr.2 hmuD ht hshape hguard
  by_cases hhalf : 1/2 ≤ q
  · have ha : |2*q-1| = 2*q-1 := abs_of_nonneg (by linarith)
    have he : (1+|2*q-1|)/2 = q := by rw [ha]; ring
    simpa only [he] using h
  · have ha : |2*q-1| = 1-2*q := by rw [abs_of_nonpos (by linarith : 2*q-1 ≤ 0)]; ring
    have he : (1+|2*q-1|)/2 = 1-q := by rw [ha]; ring
    rw [he, shared_deficitG_reflection (by linarith [hq.1] : 0 < q)
      (by linarith [hq.2] : q < 1)] at h
    exact h

/-- Independent original-cell-start lower family for every integer offset,
on both activity halves, together with the exact multiplier interval.
This retains the native cell/class/block fields and uses only the local
shape and derivative licenses; no marked-cell price certificate is used. -/
theorem spike_window_original_start_family
    {cell : V22.V22SpikeCell} (hc : cell ∈ V22.spikeCells)
    {k : V22.V22Class} (hk : k ∈ V22.classes) (hid : k.classId = cell.classId)
    {i M : ℕ} {q mu : ℝ} (hi : i < 5) (hM : 8 ≤ M)
    (hr : V22.Checks.inCell k.ra k.rb |2*q-1|)
    (hq : V22.Checks.inCell (1/4) (3/4) q) (hmuD : (k.muD : ℝ) ≤ mu)
    (ht : V22.Checks.inCell cell.lo cell.hi ((M : ℝ) / mu))
    (hblock : V22.inSpikeBlock cell i (M : ℝ))
    (hshape : V22.persistentWindowConditions |2*q-1| ((k.muD : ℝ) * (cell.lo : ℝ) + 2))
    (hguard : 0 < V22.uMonoDerivative |2*q-1| ((k.muD : ℝ) * (cell.lo : ℝ) + 2)) :
    (∀ j : ℤ, (((M : ℝ) + 2) / mu) *
      spikeWindowMinimum k cell ((M : ℝ) / mu) |2*q-1| ≤
        V22.fiberFunction q mu M j) ∧
    (M : ℝ) / mu ≤ ((M : ℝ) + 2) / mu ∧
    ((M : ℝ) + 2) / mu ≤
      (cell.hi : ℝ) * ((k.muD : ℝ) * (cell.lo : ℝ) + 2) /
        ((k.muD : ℝ) * (cell.lo : ℝ) + 2 - 2) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hmu40, _, _⟩ := window_class_domains hk
  obtain ⟨hlo, _, _, _, _⟩ := outer_cell_metadata hc hk hid
  have hmu : 0 < mu := by linarith
  let Na : ℝ := (k.muD : ℝ) * (cell.lo : ℝ) + 2
  have hNa : 10 ≤ Na := by
    dsimp [Na]
    have hprod := mul_le_mul_of_nonneg_left hmu40 (show 0 ≤ (cell.lo : ℝ) from by linarith)
    nlinarith
  have haN : Na ≤ (M : ℝ) + 2 := by
    have hMlo := (le_div_iff₀ hmu).1 ht.1
    have hprod := mul_le_mul_of_nonneg_right hmuD (show 0 ≤ (cell.lo : ℝ) from by linarith)
    dsimp [Na]
    nlinarith
  have hscale := window_size_scaling hmu hNa haN
  refine ⟨?_, hscale.1, ?_⟩
  · intro j
    by_cases hhalf : 1/2 ≤ q
    · have ha : |2*q-1| = 2*q-1 := abs_of_nonneg (by linarith)
      have he : (1+|2*q-1|)/2 = q := by rw [ha]; ring
      simpa only [he] using
        (spike_window_cell_fiber hc hk hid hM hr.1 hr.2 hmuD ht hshape hguard j)
    · have ha : |2*q-1| = 1-2*q := by
        rw [abs_of_nonpos (by linarith : 2*q-1 ≤ 0)]
        ring
      have he : (1+|2*q-1|)/2 = 1-q := by rw [ha]; ring
      have h := spike_window_cell_fiber hc hk hid hM hr.1 hr.2 hmuD ht hshape hguard
        ((M : ℤ) - j)
      have hreflect : V22.fiberFunction (1 - q) mu M ((M : ℤ) - j) =
          V22.fiberFunction q mu M j := by
        rw [shared_fiberFunction_eq, shared_fiberFunction_eq]
        exact fiber_reflection (by linarith [hq.1] : 0 < q)
          (by linarith [hq.2] : q < 1) M j
      rw [he, hreflect] at h
      exact h
  · have hprod := mul_le_mul_of_nonneg_right ht.2 (show 0 ≤ Na from by linarith)
    exact hscale.2.trans
      (div_le_div_of_nonneg_right hprod (show 0 ≤ Na - 2 from by linarith))

/-- Exact marked minimum transport needed by the finite B3 consumer. -/
theorem spike_window_minimum_transport {cell : V22.V22SpikeCell} (hc : cell ∈ V22.spikeCells)
    {k : V22.V22Class} (hk : k ∈ V22.classes) (hid : k.classId = cell.classId)
    {i M : ℕ} {q mu L : ℝ} (hi : i < 5) (hM : 8 ≤ M)
    (hr : V22.Checks.inCell k.ra k.rb |2*q-1|)
    (hq : V22.Checks.inCell (1/4) (3/4) q) (hmuD : (k.muD : ℝ) ≤ mu)
    (ht : V22.Checks.inCell cell.lo cell.hi ((M : ℝ) / mu))
    (hblock : V22.inSpikeBlock cell i (M : ℝ))
    (hshape : V22.persistentWindowConditions |2*q-1| ((k.muD : ℝ) * (cell.lo : ℝ) + 2))
    (hguard : 0 < V22.uMonoDerivative |2*q-1| ((k.muD : ℝ) * (cell.lo : ℝ) + 2))
    (hcert : min (V22.Checks.spikePhi cell i ((M : ℝ)/mu) M)
      (spikeWindowBound k cell ((M : ℝ)/mu) |2*q-1|) ≤ L) :
    min (V22.Checks.spikePhi cell i ((M : ℝ)/mu) M) (V22.deficitG q mu k.b k.beta M) ≤ L := by
  have hd := spike_window_deficit_bound hc hk hid hi hM hr hq hmuD ht hblock hshape hguard
  exact (min_le_min le_rfl hd).trans hcert

/-- Corollary 5.15 source licenses discharge the native window bound. -/
theorem source_spike_window_bound (hB3 : V22.Checks.lemma_7_14) (hD1p : V22.Checks.lemma_7_18)
    {cell : V22.V22SpikeCell} (hc : cell ∈ V22.spikeCells) (hmark : cell.window = true)
    {k : V22.V22Class} (hk : k ∈ V22.classes) (hid : k.classId = cell.classId)
    {i M : ℕ} {q mu : ℝ} (hi : i < 5) (hM : 8 ≤ M)
    (hr : V22.Checks.inCell k.ra k.rb |2*q-1|)
    (hq : V22.Checks.inCell (1/4) (3/4) q) (hmuD : (k.muD : ℝ) ≤ mu)
    (ht : V22.Checks.inCell cell.lo cell.hi ((M : ℝ) / mu))
    (hblock : V22.inSpikeBlock cell i (M : ℝ)) :
    V22.deficitG q mu k.b k.beta M ≤ spikeWindowBound k cell ((M : ℝ)/mu) |2*q-1| := by
  obtain ⟨hshape, hguard⟩ := hB3.2.2 cell hc hmark k hk hid |2*q-1| hr
  have hp := hD1p.2 k hk cell hc hid.symm hmark |2*q-1| hr.1 hr.2
  have hpersist : V22.persistentWindowConditions |2*q-1| ((k.muD : ℝ) * (cell.lo : ℝ) + 2) :=
    ⟨hshape.1, hshape.2.1, hp⟩
  exact spike_window_deficit_bound hc hk hid hi hM hr hq hmuD ht hblock hpersist hguard

end

end Erdos993Lean.Analytic.V22.Analysis
