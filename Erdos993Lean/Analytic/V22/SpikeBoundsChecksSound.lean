import Erdos993Lean.Analytic.V22.Compute.SpikeBoundsChecks
import Erdos993Lean.Analytic.V22.RayChecksSound
import Erdos993Lean.Analytic.V22.SpikeCoefficientChecksSound
import Erdos993Lean.Analytic.V22.SpikeWindowExprsSound

/-! Conditional exact consumers of both full 7.14 statements.
The sole numerical hypothesis is the concrete SpikeBoundsChecks.check.
The separately named analytic transport is an explicit parameter, with
no constructed instance or claim that its obligation has been discharged. -/

namespace Erdos993Lean.Analytic.V22.Compute.SpikeBoundsChecks

noncomputable section

open SpikeWindowExprs (DeficitToWindowPriceTransport)

theorem cellOK_of_check (h : check = true) {c : V22SpikeCell} (hc : c ∈ spikeCells) :
    cellOK c = true := (List.all_eq_true.mp h) c hc

theorem domainOK_of_check (h : check = true) {c : V22SpikeCell} (hc : c ∈ spikeCells)
    {i : Nat} (hi : i < 5) : domainOK c i = true := by
  have hp := cellOK_of_check h hc
  simp only [cellOK, Bool.and_eq_true] at hp
  exact (List.all_eq_true.mp hp.1.1) i (List.mem_range.mpr hi)

theorem coefficientOK_of_check (h : check = true) {c : V22SpikeCell} (hc : c ∈ spikeCells)
    {i : Nat} (hi : i < 5) : coefficientOK c i = true := by
  have hp := cellOK_of_check h hc
  simp only [cellOK, Bool.and_eq_true] at hp
  exact (List.all_eq_true.mp hp.1.2) i (List.mem_range.mpr hi)

theorem pureOK_of_check (h : check = true) {c : V22SpikeCell} (hc : c ∈ spikeCells)
    (hw : c.window = false) {i : Nat} (hi : i < 5) : pureOK c i = true := by
  have hp := cellOK_of_check h hc
  simp only [cellOK, Bool.and_eq_true] at hp
  have hall : (List.range 5).all (pureOK c) = true := by
    simpa only [hw, Bool.false_eq_true, if_false] using hp.2
  exact (List.all_eq_true.mp hall) i (List.mem_range.mpr hi)

theorem markedClassOK_of_check (h : check = true) {c : V22SpikeCell} (hc : c ∈ spikeCells)
    (hw : c.window = true) {k : V22Class} (hk : k ∈ classes)
    (hid : k.classId = c.classId) : markedClassOK c k = true := by
  have hp := cellOK_of_check h hc
  simp only [cellOK, Bool.and_eq_true] at hp
  have hall : classes.all (fun k =>
      if k.classId == c.classId then markedClassOK c k else true) = true := by
    simpa only [hw, if_true] using hp.2
  have hx := (List.all_eq_true.mp hall) k hk
  simpa [hid] using hx

theorem coefficientOK_sound {c : V22SpikeCell} {i : Nat}
    (h : coefficientOK c i = true) {t : ℝ} (ht : Checks.inCell c.lo c.hi t) :
    Checks.spikePhiCoefficientsValid c i t :=
  SpikeCoefficientChecks.checkedBlockOK_sound h ht

/-- Starts are rechecked using actual class/cell values, without identifying
an actual class with the candidate generator's lookup result. -/
theorem startOK_sound {c : V22SpikeCell} {k : V22Class} (h : startOK c k = true)
    {r : ℝ} (hr : Checks.inCell k.ra k.rb r) :
    windowConditions r ((k.muD : ℝ)*(c.lo : ℝ)+2) ∧
      persistentWindowConditions r ((k.muD : ℝ)*(c.lo : ℝ)+2) ∧
      0 < uMonoDerivative r ((k.muD : ℝ)*(c.lo : ℝ)+2) := by
  cases hf : markedFor c with
  | none => simp [startOK, hf] at h
  | some d =>
      have hp : SpikeWindowExprs.startPass k c d.startPieces = true := by
        simpa [startOK, hf] using h
      have hs := SpikeWindowExprs.startPass_sound hp hr
      simpa only [SpikeWindowExprs.cellStart_cast] using hs

/-- Stronger six-digit pure-ray bound, on every actual parameter of an
unmarked original cell and block. -/
theorem nonwindow_log_sound (h : check = true) {c : V22SpikeCell} (hc : c ∈ spikeCells)
    (hw : c.window = false) {i : Nat} (hi : i < 5) {t M : ℝ}
    (ht : Checks.inCell c.lo c.hi t) (hM : inSpikeBlock c i M) :
    Checks.spikePhiCoefficientsValid c i t ∧
      Checks.spikePhi c i t M ≤ (c.logBounds.getD i 0 : ℝ) := by
  have hp := pureOK_of_check h hc hw hi
  have hr := RayChecks.checkedBlockOK_log_sound hp ht hM
  exact ⟨coefficientOK_sound (coefficientOK_of_check h hc hi) ht, hr.2⟩

/-- The window branch keeps the integer fiber, exact actual class and mean,
all coefficient guards, and all starting-window hypotheses. -/
theorem window_log_sound (transport : DeficitToWindowPriceTransport) (h : check = true)
    {c : V22SpikeCell} (hc : c ∈ spikeCells) (hw : c.window = true)
    {k : V22Class} (hk : k ∈ classes) (hid : k.classId = c.classId)
    {i : Nat} (hi : i < 5) {t q : ℝ} {M : Nat}
    (ht : Checks.inCell c.lo c.hi t) (hr : Checks.inCell k.ra k.rb |2*q-1|)
    (hq : Checks.inCell (1/4) (3/4) q) (hM : inSpikeBlock c i M)
    (hmu : (k.muD : ℝ) ≤ (M : ℝ)/t) :
    Checks.spikePhiCoefficientsValid c i t ∧
      min (Checks.spikePhi c i t M) (deficitG q ((M : ℝ)/t) k.b k.beta M) ≤
        (c.logBounds.getD i 0 : ℝ) := by
  have hcguard := coefficientOK_sound (coefficientOK_of_check h hc hi) ht
  have hp := markedClassOK_of_check h hc hw hk hid
  simp only [markedClassOK, Bool.and_eq_true] at hp
  have hor := (List.all_eq_true.mp hp.2) i (List.mem_range.mpr hi)
  rcases Bool.or_eq_true_iff.mp hor with hpure | hwindow
  · have hs := RayChecks.checkedBlockOK_min_log_sound
      (X := deficitG q ((M : ℝ)/t) k.b k.beta M) hpure ht hM
    exact ⟨hcguard, hs.2⟩
  · have hd := domainOK_of_check h hc hi
    simp only [domainOK, decide_eq_true_eq] at hd
    have hlo : (0 : ℝ) < (c.lo : ℝ) := by exact_mod_cast hd.2.1
    have htpos : 0 < t := hlo.trans_le ht.1
    have hm1 : (8 : ℝ) ≤ (GeneratedRayData.m1 c i : ℝ) := by
      exact_mod_cast hd.2.2.1
    have hmlower : (GeneratedRayData.m1 c i : ℝ) ≤ (M : ℝ) := by
      simpa only [RayChecks.m1_cast] using hM.1
    have hMreal : (8 : ℝ) ≤ (M : ℝ) := hm1.trans hmlower
    have hMnat : 8 ≤ M := by exact_mod_cast hMreal
    have hstart : ∀ r : ℝ, (k.ra : ℝ) ≤ r → r ≤ (k.rb : ℝ) →
        windowConditions r ((k.muD : ℝ)*(c.lo : ℝ)+2) ∧
          persistentWindowConditions r ((k.muD : ℝ)*(c.lo : ℝ)+2) ∧
          0 < uMonoDerivative r ((k.muD : ℝ)*(c.lo : ℝ)+2) := by
      intro r hr0 hr1
      exact startOK_sound hp.1 ⟨hr0,hr1⟩
    cases hf : markedFor c with
    | none => simp [windowOK, hf] at hwindow
    | some d =>
        have hpass : SpikeWindowExprs.cellPass k c (c.logBounds.getD i 0) d.price = true := by
          simpa [windowOK, hf] using hwindow
        exact ⟨hcguard, SpikeWindowExprs.marked_min_bound_of_transport transport hk hc
          hid.symm hw hstart hi hpass htpos hMnat ht hr hq hM hmu⟩

/-- All six-digit exports are separately checked below their displayed
Table 4 values, including blocks which use a marked window bound. -/
theorem exports_le_table (h : check = true) {c : V22SpikeCell} (hc : c ∈ spikeCells)
    {i : Nat} (hi : i < 5) : c.logBounds.getD i 0 ≤ c.bounds.getD i 0 := by
  have hd := domainOK_of_check h hc hi
  simp only [domainOK, decide_eq_true_eq] at hd
  exact hd.2.2.2

theorem check_sound (transport : DeficitToWindowPriceTransport) (h : check = true) :
    Checks.lemma_7_14 ∧ Checks.lemma_7_14_certified := by
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro c hc hw i hi t M ht hM
      have hs := nonwindow_log_sound h hc hw hi ht hM
      have he : (c.logBounds.getD i 0 : ℝ) ≤ (c.bounds.getD i 0 : ℝ) := by
        exact_mod_cast (exports_le_table h hc hi)
      exact ⟨hs.1, hs.2.trans he⟩
    · intro c hc hw k hk hid i hi t q M ht hr hq hM hmu
      have hs := window_log_sound transport h hc hw hk hid hi ht hr hq hM hmu
      have he : (c.logBounds.getD i 0 : ℝ) ≤ (c.bounds.getD i 0 : ℝ) := by
        exact_mod_cast (exports_le_table h hc hi)
      exact ⟨hs.1, hs.2.trans he⟩
    · intro c hc hw k hk hid r hr
      have hp := markedClassOK_of_check h hc hw hk hid
      have hstart : startOK c k = true := (Bool.and_eq_true_iff.mp hp).1
      have hs := startOK_sound hstart hr
      simpa using (show windowConditions r ((k.muD : ℝ)*(c.lo : ℝ)+2) ∧
        0 < uMonoDerivative r ((k.muD : ℝ)*(c.lo : ℝ)+2) from ⟨hs.1, hs.2.2⟩)
  · refine ⟨?_, ?_, ?_⟩
    · intro c hc hw i hi t M ht hM
      exact nonwindow_log_sound h hc hw hi ht hM
    · intro c hc hw k hk hid i hi t q M ht hr hq hM hmu
      exact window_log_sound transport h hc hw hk hid hi ht hr hq hM hmu
    · intro c hc i hi
      exact exports_le_table h hc hi

theorem lemma_7_14_of_check (transport : DeficitToWindowPriceTransport) (h : check = true) :
    Checks.lemma_7_14 := (check_sound transport h).1

theorem lemma_7_14_certified_of_check (transport : DeficitToWindowPriceTransport)
    (h : check = true) : Checks.lemma_7_14_certified := (check_sound transport h).2

end
end Erdos993Lean.Analytic.V22.Compute.SpikeBoundsChecks
