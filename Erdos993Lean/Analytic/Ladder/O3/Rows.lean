import Mathlib
import Erdos993Lean.Analytic.N48.TailChecks.P22
import Erdos993Lean.Analytic.N48.TailChecks.P26
import Erdos993Lean.Analytic.N48.TailChecks.P27
import Erdos993Lean.Analytic.N48.TailChecks.P28
import Erdos993Lean.Analytic.Ladder.O3.Row05
import Erdos993Lean.Analytic.Ladder.O3.Row06
import Erdos993Lean.Analytic.Ladder.O3.Row07
import Erdos993Lean.Analytic.Ladder.O3.Row08
import Erdos993Lean.Analytic.Ladder.O3.Row09
import Erdos993Lean.Analytic.Ladder.O3.Row10
import Erdos993Lean.Analytic.Ladder.O3.Row11
import Erdos993Lean.Analytic.Ladder.O3.Row12
import Erdos993Lean.Analytic.Ladder.O3.Row13
import Erdos993Lean.Analytic.Ladder.O3.Row14
import Erdos993Lean.Analytic.Ladder.O3.Row15
import Erdos993Lean.Analytic.Ladder.O3.Row16
import Erdos993Lean.Analytic.Ladder.O3.Row17
import Erdos993Lean.Analytic.Ladder.O3.Row18
import Erdos993Lean.Analytic.Ladder.O3.Row19
import Erdos993Lean.Analytic.Ladder.O3.Row20
import Erdos993Lean.Analytic.Ladder.O3.Row21
import Erdos993Lean.Analytic.Ladder.O3.Row22
import Erdos993Lean.Analytic.Ladder.O3.Row23
import Erdos993Lean.Analytic.Ladder.O3.Row24
import Erdos993Lean.Analytic.Ladder.O3.Row25
import Erdos993Lean.Analytic.Ladder.O3.Row26

/-!
# The 26 O3 ladder rows at `t = 0` (lane A21)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A21.  Source: lane O3R's `LEAN/ladder/o3/rows.json` (the 26
sub-band rows of `REACH_BELOW_52.md` §5(c), all CERTIFIED by the unmodified O3 checker; `INDEX.md`), lane A10's verified
cell checker `TailCert.Compute.checkBand`.  Rows 1–4 (the `N = 48` step) are lane A20's `N48.TailChecks.rowP22` …
`rowP28`; rows 5–26 are this lane's `Row05.lean` … `Row26.lean`, one `native_decide` each.

* `rowLo`, `rowHi`, `rowA`, `rowEll`: the 26 rows (index `i` = row `i + 1`): interval, potential coefficient, rate.
* **`rows_ok`**: every row passes lane A10's checker at `t = 0`.

Scalarity check: each `ℓ` summarizes the Laplace transform of the free count `M` at `z = 0` on its interval
(`E(1 − q)^M ≤ e^{−ℓ m}`, T3-2), produced by the certificate `T3UNonneg λ 0 a ℓ`; `a` is the potential's coefficient
(consumed only by `T3UNonneg`); the consumers are `N45/Tail.lean` and `N44/Tail.lean` through the piece tables.
-/

namespace Erdos993Lean.Analytic.Ladder.O3

private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- The lower edges of the 26 rows. -/
def rowLo : List Rat :=
  [R (13) 10, R (8) 5, R (33) 20, R (17) 10, R (1) 1, R (103) 100, R (26) 25, R (21) 20, R (107) 100, R (27) 25, R (11) 10, R (27) 20, R (7) 4, R (9) 5, R (37) 20, R (19) 10, R (39) 50, R (87) 100, R (89) 100, R (91) 100, R (23) 25, R (23) 25, R (47) 50, R (24) 25, R (97) 100, R (99) 100]

/-- The upper edges of the 26 rows. -/
def rowHi : List Rat :=
  [R (27) 20, R (33) 20, R (17) 10, R (7) 4, R (103) 100, R (26) 25, R (21) 20, R (107) 100, R (27) 25, R (11) 10, R (28) 25, R (7) 5, R (9) 5, R (37) 20, R (19) 10, R (39) 20, R (4) 5, R (22) 25, R (23) 25, R (23) 25, R (93) 100, R (47) 50, R (24) 25, R (97) 100, R (99) 100, R (1) 1]

/-- The potential coefficients `a` of the 26 rows. -/
def rowA : List Rat :=
  [R (7) 100, R (47) 500, R (97) 1000, R (1) 10, R (23) 500, R (23) 500, R (7) 125, R (7) 125, R (29) 500, R (59) 1000, R (11) 200, R (81) 1000, R (101) 1000, R (93) 1000, R (19) 200, R (27) 250, R (37) 1000, R (1) 25, R (41) 1000, R (21) 500, R (6) 125, R (43) 1000, R (43) 1000, R (1) 20, R (9) 250, R (11) 250]

/-- The rates `ℓ` at `t = 0` of the 26 rows. -/
def rowEll : List Rat :=
  [R (23) 50, R (939) 2000, R (47) 100, R (941) 2000, R (881) 2000, R (449) 1000, R (901) 2000, R (449) 1000, R (907) 2000, R (113) 250, R (907) 2000, R (37) 80, R (941) 2000, R (47) 100, R (47) 100, R (47) 100, R (817) 2000, R (171) 400, R (851) 2000, R (217) 500, R (871) 2000, R (173) 400, R (871) 2000, R (441) 1000, R (879) 2000, R (889) 2000]

theorem rowLo_length : rowLo.length = 26 := by decide
theorem rowHi_length : rowHi.length = 26 := by decide

/-! ### The rows as literals (kernel `decide`), so that the check theorems apply by rewriting -/

theorem rowData00 : rowLo.getD 0 0 = 13/10 ∧ rowHi.getD 0 0 = 27/20 ∧ rowA.getD 0 0 = 7/100 ∧ rowEll.getD 0 0 = 23/50 := by
  decide +kernel
theorem rowData01 : rowLo.getD 1 0 = 8/5 ∧ rowHi.getD 1 0 = 33/20 ∧ rowA.getD 1 0 = 47/500 ∧ rowEll.getD 1 0 = 939/2000 := by
  decide +kernel
theorem rowData02 : rowLo.getD 2 0 = 33/20 ∧ rowHi.getD 2 0 = 17/10 ∧ rowA.getD 2 0 = 97/1000 ∧ rowEll.getD 2 0 = 47/100 := by
  decide +kernel
theorem rowData03 : rowLo.getD 3 0 = 17/10 ∧ rowHi.getD 3 0 = 7/4 ∧ rowA.getD 3 0 = 1/10 ∧ rowEll.getD 3 0 = 941/2000 := by
  decide +kernel
theorem rowData04 : rowLo.getD 4 0 = 1 ∧ rowHi.getD 4 0 = 103/100 ∧ rowA.getD 4 0 = 23/500 ∧ rowEll.getD 4 0 = 881/2000 := by
  decide +kernel
theorem rowData05 : rowLo.getD 5 0 = 103/100 ∧ rowHi.getD 5 0 = 26/25 ∧ rowA.getD 5 0 = 23/500 ∧ rowEll.getD 5 0 = 449/1000 := by
  decide +kernel
theorem rowData06 : rowLo.getD 6 0 = 26/25 ∧ rowHi.getD 6 0 = 21/20 ∧ rowA.getD 6 0 = 7/125 ∧ rowEll.getD 6 0 = 901/2000 := by
  decide +kernel
theorem rowData07 : rowLo.getD 7 0 = 21/20 ∧ rowHi.getD 7 0 = 107/100 ∧ rowA.getD 7 0 = 7/125 ∧ rowEll.getD 7 0 = 449/1000 := by
  decide +kernel
theorem rowData08 : rowLo.getD 8 0 = 107/100 ∧ rowHi.getD 8 0 = 27/25 ∧ rowA.getD 8 0 = 29/500 ∧ rowEll.getD 8 0 = 907/2000 := by
  decide +kernel
theorem rowData09 : rowLo.getD 9 0 = 27/25 ∧ rowHi.getD 9 0 = 11/10 ∧ rowA.getD 9 0 = 59/1000 ∧ rowEll.getD 9 0 = 113/250 := by
  decide +kernel
theorem rowData10 : rowLo.getD 10 0 = 11/10 ∧ rowHi.getD 10 0 = 28/25 ∧ rowA.getD 10 0 = 11/200 ∧ rowEll.getD 10 0 = 907/2000 := by
  decide +kernel
theorem rowData11 : rowLo.getD 11 0 = 27/20 ∧ rowHi.getD 11 0 = 7/5 ∧ rowA.getD 11 0 = 81/1000 ∧ rowEll.getD 11 0 = 37/80 := by
  decide +kernel
theorem rowData12 : rowLo.getD 12 0 = 7/4 ∧ rowHi.getD 12 0 = 9/5 ∧ rowA.getD 12 0 = 101/1000 ∧ rowEll.getD 12 0 = 941/2000 := by
  decide +kernel
theorem rowData13 : rowLo.getD 13 0 = 9/5 ∧ rowHi.getD 13 0 = 37/20 ∧ rowA.getD 13 0 = 93/1000 ∧ rowEll.getD 13 0 = 47/100 := by
  decide +kernel
theorem rowData14 : rowLo.getD 14 0 = 37/20 ∧ rowHi.getD 14 0 = 19/10 ∧ rowA.getD 14 0 = 19/200 ∧ rowEll.getD 14 0 = 47/100 := by
  decide +kernel
theorem rowData15 : rowLo.getD 15 0 = 19/10 ∧ rowHi.getD 15 0 = 39/20 ∧ rowA.getD 15 0 = 27/250 ∧ rowEll.getD 15 0 = 47/100 := by
  decide +kernel
theorem rowData16 : rowLo.getD 16 0 = 39/50 ∧ rowHi.getD 16 0 = 4/5 ∧ rowA.getD 16 0 = 37/1000 ∧ rowEll.getD 16 0 = 817/2000 := by
  decide +kernel
theorem rowData17 : rowLo.getD 17 0 = 87/100 ∧ rowHi.getD 17 0 = 22/25 ∧ rowA.getD 17 0 = 1/25 ∧ rowEll.getD 17 0 = 171/400 := by
  decide +kernel
theorem rowData18 : rowLo.getD 18 0 = 89/100 ∧ rowHi.getD 18 0 = 23/25 ∧ rowA.getD 18 0 = 41/1000 ∧ rowEll.getD 18 0 = 851/2000 := by
  decide +kernel
theorem rowData19 : rowLo.getD 19 0 = 91/100 ∧ rowHi.getD 19 0 = 23/25 ∧ rowA.getD 19 0 = 21/500 ∧ rowEll.getD 19 0 = 217/500 := by
  decide +kernel
theorem rowData20 : rowLo.getD 20 0 = 23/25 ∧ rowHi.getD 20 0 = 93/100 ∧ rowA.getD 20 0 = 6/125 ∧ rowEll.getD 20 0 = 871/2000 := by
  decide +kernel
theorem rowData21 : rowLo.getD 21 0 = 23/25 ∧ rowHi.getD 21 0 = 47/50 ∧ rowA.getD 21 0 = 43/1000 ∧ rowEll.getD 21 0 = 173/400 := by
  decide +kernel
theorem rowData22 : rowLo.getD 22 0 = 47/50 ∧ rowHi.getD 22 0 = 24/25 ∧ rowA.getD 22 0 = 43/1000 ∧ rowEll.getD 22 0 = 871/2000 := by
  decide +kernel
theorem rowData23 : rowLo.getD 23 0 = 24/25 ∧ rowHi.getD 23 0 = 97/100 ∧ rowA.getD 23 0 = 1/20 ∧ rowEll.getD 23 0 = 441/1000 := by
  decide +kernel
theorem rowData24 : rowLo.getD 24 0 = 97/100 ∧ rowHi.getD 24 0 = 99/100 ∧ rowA.getD 24 0 = 9/250 ∧ rowEll.getD 24 0 = 879/2000 := by
  decide +kernel
theorem rowData25 : rowLo.getD 25 0 = 99/100 ∧ rowHi.getD 25 0 = 1 ∧ rowA.getD 25 0 = 11/250 ∧ rowEll.getD 25 0 = 889/2000 := by
  decide +kernel

/-- **The 26 O3 ladder rows pass lane A10's checker at `t = 0`** (26 `native_decide` checks: lane A20's four and this lane's 22). -/
theorem rows_ok : ∀ i < 26, TailCert.Compute.checkBand (rowLo.getD i 0) (rowHi.getD i 0) (rowA.getD i 0) (rowEll.getD i 0) 0 = true := by
  intro i hi
  interval_cases i
  · obtain ⟨e1, e2, e3, e4⟩ := rowData00
    rw [e1, e2, e3, e4]
    exact N48.TailChecks.rowP22
  · obtain ⟨e1, e2, e3, e4⟩ := rowData01
    rw [e1, e2, e3, e4]
    exact N48.TailChecks.rowP26
  · obtain ⟨e1, e2, e3, e4⟩ := rowData02
    rw [e1, e2, e3, e4]
    exact N48.TailChecks.rowP27
  · obtain ⟨e1, e2, e3, e4⟩ := rowData03
    rw [e1, e2, e3, e4]
    exact N48.TailChecks.rowP28
  · obtain ⟨e1, e2, e3, e4⟩ := rowData04
    rw [e1, e2, e3, e4]
    exact row05
  · obtain ⟨e1, e2, e3, e4⟩ := rowData05
    rw [e1, e2, e3, e4]
    exact row06
  · obtain ⟨e1, e2, e3, e4⟩ := rowData06
    rw [e1, e2, e3, e4]
    exact row07
  · obtain ⟨e1, e2, e3, e4⟩ := rowData07
    rw [e1, e2, e3, e4]
    exact row08
  · obtain ⟨e1, e2, e3, e4⟩ := rowData08
    rw [e1, e2, e3, e4]
    exact row09
  · obtain ⟨e1, e2, e3, e4⟩ := rowData09
    rw [e1, e2, e3, e4]
    exact row10
  · obtain ⟨e1, e2, e3, e4⟩ := rowData10
    rw [e1, e2, e3, e4]
    exact row11
  · obtain ⟨e1, e2, e3, e4⟩ := rowData11
    rw [e1, e2, e3, e4]
    exact row12
  · obtain ⟨e1, e2, e3, e4⟩ := rowData12
    rw [e1, e2, e3, e4]
    exact row13
  · obtain ⟨e1, e2, e3, e4⟩ := rowData13
    rw [e1, e2, e3, e4]
    exact row14
  · obtain ⟨e1, e2, e3, e4⟩ := rowData14
    rw [e1, e2, e3, e4]
    exact row15
  · obtain ⟨e1, e2, e3, e4⟩ := rowData15
    rw [e1, e2, e3, e4]
    exact row16
  · obtain ⟨e1, e2, e3, e4⟩ := rowData16
    rw [e1, e2, e3, e4]
    exact row17
  · obtain ⟨e1, e2, e3, e4⟩ := rowData17
    rw [e1, e2, e3, e4]
    exact row18
  · obtain ⟨e1, e2, e3, e4⟩ := rowData18
    rw [e1, e2, e3, e4]
    exact row19
  · obtain ⟨e1, e2, e3, e4⟩ := rowData19
    rw [e1, e2, e3, e4]
    exact row20
  · obtain ⟨e1, e2, e3, e4⟩ := rowData20
    rw [e1, e2, e3, e4]
    exact row21
  · obtain ⟨e1, e2, e3, e4⟩ := rowData21
    rw [e1, e2, e3, e4]
    exact row22
  · obtain ⟨e1, e2, e3, e4⟩ := rowData22
    rw [e1, e2, e3, e4]
    exact row23
  · obtain ⟨e1, e2, e3, e4⟩ := rowData23
    rw [e1, e2, e3, e4]
    exact row24
  · obtain ⟨e1, e2, e3, e4⟩ := rowData24
    rw [e1, e2, e3, e4]
    exact row25
  · obtain ⟨e1, e2, e3, e4⟩ := rowData25
    rw [e1, e2, e3, e4]
    exact row26

end Erdos993Lean.Analytic.Ladder.O3
