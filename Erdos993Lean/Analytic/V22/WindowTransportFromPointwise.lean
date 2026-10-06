import Erdos993Lean.Analytic.V22.WindowPriceInfimumSound
import Erdos993Lean.Analytic.V22.SpikeWindowExprsSound

/-!
# The retained all-offset family suffices for the marked-spike transport

Source: the fixed-start argument of Lemmas 5.9--5.13, Theorem 5.14, and
Corollary 5.15 in the repaired note. The finite check supplies the original
cell start conditions; the remaining analytic object is a lower bound on the
actual `fiberFunction` at every integer offset. This module consumes that
object and proves only the multiplier and infimum steps. It does not construct
the analytic family or provide an unconditional instance of the transport.

The domains below are identical to `DeficitToWindowPriceTransport.bound`,
including the class, marked cell, exact mean, integer block, and original
start hypotheses. For marked cells below the class `tau`, the producer must
prove the generic fixed-start argument; the final stated range of Theorem
5.14 alone does not cover those cells. The start is never replaced by a
refined subcell start.
-/

namespace Erdos993Lean.Analytic.V22

open Compute.SpikeWindowExprs
open Checks (inCell)

noncomputable section

/-- The exact analytic object remaining after the numerical window checks.
Every integer offset, actual fiber, and original-cell start is retained. -/
structure FixedStartFiberLowerFamily : Prop where
  bound : ∀ c ∈ classes, ∀ cell ∈ spikeCells, cell.classId = c.classId → cell.window = true →
    (∀ r : ℝ, (c.ra : ℝ) ≤ r → r ≤ (c.rb : ℝ) →
      windowConditions r ((c.muD : ℝ)*(cell.lo : ℝ)+2) ∧
        persistentWindowConditions r ((c.muD : ℝ)*(cell.lo : ℝ)+2) ∧
        0 < uMonoDerivative r ((c.muD : ℝ)*(cell.lo : ℝ)+2)) →
    ∀ i : Nat, i < 5 → ∀ (t q : ℝ) (M : Nat), 0 < t → 8 ≤ M →
      inCell cell.lo cell.hi t → inCell c.ra c.rb |2*q-1| → inCell (1/4) (3/4) q →
      inSpikeBlock cell i M → (c.muD : ℝ) ≤ (M : ℝ)/t →
      ∀ j : ℤ, (((M : ℝ)+2)/((M : ℝ)/t)) *
        Checks.windowCellMinimum c (asWindowCell cell) t |2*q-1| ≤
          fiberFunction q ((M : ℝ)/t) M j

/-- Positivity of the exact eight class means, checked by kernel reduction
of the finite rational list. This introduces no native computation theorem. -/
theorem fixedStart_class_muD_pos {c : V22Class} (hc : c ∈ classes) :
    0 < (c.muD : ℝ) := by
  have hall : classes.all (fun k => decide ((0 : Rat) < k.muD)) = true := by decide
  have hrat : (0 : Rat) < c.muD :=
    of_decide_eq_true ((List.all_eq_true.mp hall) c hc)
  exact_mod_cast hrat

/-- Positivity of the exact original spike-cell lower endpoints, also
checked by kernel reduction of the finite rational list. -/
theorem fixedStart_spike_lo_pos {cell : V22SpikeCell} (hc : cell ∈ spikeCells) :
    0 < (cell.lo : ℝ) := by
  have hall : spikeCells.all (fun k => decide ((0 : Rat) < k.lo)) = true := by decide
  have hrat : (0 : Rat) < cell.lo :=
    of_decide_eq_true ((List.all_eq_true.mp hall) cell hc)
  exact_mod_cast hrat

/-- The actual mean and original cell imply both the frozen start bound
and the exact multiplier bound used by the one-sided infimum argument. -/
theorem fixedStart_multiplier_bounds {d lo hi t m : ℝ}
    (hd : 0 < d) (hlo : 0 < lo) (ht : 0 < t) (hm : 0 < m)
    (hcellLo : lo ≤ t) (hcellHi : t ≤ hi) (hmean : d ≤ m / t) :
    d * lo + 2 ≤ m + 2 ∧
      0 ≤ (m + 2) / (m / t) ∧
      (m + 2) / (m / t) ≤ hi * (d * lo + 2) / (d * lo) := by
  have hbase : 0 < d * lo := mul_pos hd hlo
  have hdt : d * t ≤ m := (le_div_iff₀ ht).mp hmean
  have hbaseM : d * lo ≤ m :=
    (mul_le_mul_of_nonneg_left hcellLo hd.le).trans hdt
  have hratio : (m + 2) / m ≤ (d * lo + 2) / (d * lo) := by
    apply (div_le_div_iff₀ hm hbase).mpr
    nlinarith only [hbaseM]
  have hratioNonneg : 0 ≤ (d * lo + 2) / (d * lo) := by
    exact div_nonneg (by linarith) hbase.le
  have hBIdentity : (m + 2) / (m / t) = t * ((m + 2) / m) := by
    field_simp [ht.ne', hm.ne'] <;> ring
  have hBNonneg : 0 ≤ (m + 2) / (m / t) :=
    div_nonneg (by linarith) (div_pos hm ht).le
  refine ⟨by linarith, hBNonneg, ?_⟩
  calc
    (m + 2) / (m / t) = t * ((m + 2) / m) := hBIdentity
    _ ≤ t * ((d * lo + 2) / (d * lo)) :=
      mul_le_mul_of_nonneg_left hratio ht.le
    _ ≤ hi * ((d * lo + 2) / (d * lo)) :=
      mul_le_mul_of_nonneg_right hcellHi hratioNonneg
    _ = hi * (d * lo + 2) / (d * lo) := by ring

/-- The frozen start and multiplier bounds at the exact class/cell data.
The upper price uses the original `cell.hi` and original `cell.lo`. -/
theorem fixedStart_cell_bounds {c : V22Class} {cell : V22SpikeCell}
    (hc : c ∈ classes) (hcell : cell ∈ spikeCells)
    {t : ℝ} {M : Nat} (ht : 0 < t) (hM : 0 < M)
    (htcell : inCell cell.lo cell.hi t) (hmean : (c.muD : ℝ) ≤ (M : ℝ)/t) :
    (c.muD : ℝ) * (cell.lo : ℝ) + 2 ≤ (M : ℝ) + 2 ∧
      0 ≤ ((M : ℝ) + 2) / ((M : ℝ) / t) ∧
      ((M : ℝ) + 2) / ((M : ℝ) / t) ≤ (bMax c cell : ℝ) := by
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have hbounds := fixedStart_multiplier_bounds
    (fixedStart_class_muD_pos hc) (fixedStart_spike_lo_pos hcell)
    ht hMr htcell.1 htcell.2 hmean
  simpa only [bMax_cast] using hbounds

/-- Consuming the retained all-offset analytic object discharges the
named deficit transport. No instance of that analytic object is supplied. -/
theorem transport_of_pointwise (family : FixedStartFiberLowerFamily) :
    DeficitToWindowPriceTransport := by
  refine ⟨?_⟩
  intro c hc cell hcell hid hw hstart i hi t q M htpos hM ht hr hq hblock hmean
  have hMn : 0 < M := by omega
  have hbounds := fixedStart_cell_bounds hc hcell htpos hMn ht hmean
  have hpoint := family.bound c hc cell hcell hid hw hstart i hi t q M
    htpos hM ht hr hq hblock hmean
  have hdef := deficitG_div_le_class_window_price_of_pointwise (c := c)
    (B := ((M : ℝ) + 2) / ((M : ℝ) / t))
    (Bmax := (bMax c cell : ℝ))
    (X := Checks.windowCellMinimum c (asWindowCell cell) t |2*q-1|)
    hMn htpos hbounds.2.1 hbounds.2.2 hpoint
  simpa only [windowPrice] using hdef

end

end Erdos993Lean.Analytic.V22
