import Erdos993Lean.Analytic.V22.Defs

/-!
# The late finite-check statements of the repaired fiber note

Definitions only: Lemmas 7.15--7.21 of the repaired `note.tex`.
The cell identities and rational ranges are retained. Neither the displayed
Table 5 prices nor its displayed margins are used as exact quantities.
The averaging recipe uses the fixed six-significant-digit upward certified
B3 exports in `V22SpikeCell.logBounds`; its positivity is a stronger numerical
obligation than positivity with the unrounded internal bounds.
-/

namespace Erdos993Lean.Analytic.V22.Checks

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Lemma 5.7: the fixed starting `N` of one wing cell. -/
def wingN0 (c : V22WingClass) (cell : V22Cell) : ℝ :=
  (c.muW : ℝ) * (cell.lo : ℝ) + 2

def wingNuMax (c : V22WingClass) (cell : V22Cell) : ℝ :=
  min 6 ((c.rb : ℝ) * Real.sqrt (wingN0 c cell))

def wingKPrime (c : V22WingClass) (cell : V22Cell) (t : ℝ) : ℝ :=
  let N0 := wingN0 c cell
  kappaA N0 c.rb * Ghat t (N0 - 2) / rhoStar N0 c.rb

def wingBPrime (c : V22WingClass) (cell : V22Cell) (t : ℝ) : ℝ :=
  let N0 := wingN0 c cell
  4 * Ghat t (N0 - 2) / rhoStar N0 c.rb

/-- Lemma 5.7: `c(N)`, with the cell's starting coefficients frozen. -/
def wingC (c : V22WingClass) (cell : V22Cell) (t N : ℝ) : ℝ :=
  (N - 1) / (1 - (c.ra : ℝ) ^ 2) - wingKPrime c cell t

def wingDe (c : V22WingClass) (cell : V22Cell) : ℝ :=
  let N0 := wingN0 c cell
  4 / ((rhoStar N0 c.rb) ^ 2 * betaE N0 c.rb (wingNuMax c cell))

/-- Lemma 5.7: `τ₁`, retaining the exact two-endpoint template constants. -/
def wingTau1 (c : V22WingClass) (cell : V22Cell) (t : ℝ) : ℝ :=
  let M0 := wingN0 c cell - 2
  2 - 6 * G (lambdaT t) + (71 / 10) * |G1 (lambdaT t)|
    - (kbar M0) ^ 2 * G2 (lambdaT t) / (M0 + 3)

/-- Lemma 5.7: the complete real function `w(N)` used by Lemma 7.15. -/
def wingW (c : V22WingClass) (cell : V22Cell) (t N : ℝ) : ℝ :=
  (N - 2) * gaussianSlack t + wingTau1 c cell t
    + wingC c cell t N * (c.ra : ℝ) ^ 2 * N
    - wingBPrime c cell t * (c.ra : ℝ) * Real.sqrt N
    - |G1 (lambdaT t)| * wingDe c cell

/-- Note Lemma 7.15 (C1): all four hypotheses of Lemma 5.7 and the
nonnegative minimum over the whole half-line, on the eleven exact wing cells. -/
def lemma_7_15 : Prop :=
  ∀ c ∈ wingClasses, ∀ cell ∈ wingCells, cell.classId = c.classId →
    ∀ t : ℝ, (cell.lo : ℝ) ≤ t → t ≤ (cell.hi : ℝ) →
      0 < wingC c cell t (wingN0 c cell) ∧
      wingBPrime c cell t / (2 * wingC c cell t (wingN0 c cell)) ≤
        (c.ra : ℝ) * Real.sqrt (wingN0 c cell) ∧
      0 < rhoStar (wingN0 c cell) c.rb ∧
      0 < betaE (wingN0 c cell) c.rb (wingNuMax c cell) ∧
      ∀ N : ℝ, wingN0 c cell ≤ N → 0 ≤ wingW c cell t N

/-- Note Lemma 7.16 (D0): the target is strictly negative at the exact upper
cutoff of each of the eight window classes. -/
def lemma_7_16 : Prop :=
  ∀ c ∈ classes, psi c.thi + (c.b : ℝ) + (c.beta : ℝ) * ((c.thi : ℝ) - 1) < 0

/-- Note Lemma 7.17 (D1): all three window shape conditions at the exact
starting `N=μ_D τ+2`, uniformly on each closed class activity range. -/
def lemma_7_17 : Prop :=
  ∀ c ∈ classes, ∀ r : ℝ, (c.ra : ℝ) ≤ r → r ≤ (c.rb : ℝ) →
    windowConditions r ((c.muD : ℝ) * (c.tau : ℝ) + 2)

/-- The exact monotone form (c3') of the window shape condition. -/
def c3PrimeAt (r N : ℝ) : Prop :=
  3 ≤ 12 * (1 - (r + ZR r N 3) ^ 2) / (1 - r ^ 2)

/-- Note Lemma 7.18 (D1'): (c3') at the eight class starts and at the least
`N` of each of the fourteen explicitly window-marked spike cells. -/
def lemma_7_18 : Prop :=
  (∀ c ∈ classes, ∀ r : ℝ, (c.ra : ℝ) ≤ r → r ≤ (c.rb : ℝ) →
    c3PrimeAt r ((c.muD : ℝ) * (c.tau : ℝ) + 2)) ∧
  (∀ c ∈ classes, ∀ cell ∈ spikeCells, cell.classId = c.classId →
    cell.window = true → ∀ r : ℝ, (c.ra : ℝ) ≤ r → r ≤ (c.rb : ℝ) →
      c3PrimeAt r ((c.muD : ℝ) * (cell.lo : ℝ) + 2))

/-- Note Lemma 7.19 (D2): the explicit derivative lower bound of Lemma 5.12
is positive at `m=μ_D τ+3` for every actual activity in the class. -/
def lemma_7_19 : Prop :=
  ∀ c ∈ classes, ∀ r : ℝ, (c.ra : ℝ) ≤ r → r ≤ (c.rb : ℝ) →
    0 < uMonoDerivative r ((c.muD : ℝ) * (c.tau : ℝ) + 2)

/-- Lemma 7.20: the full pointwise class target. -/
def classTarget (c : V22Class) (t : ℝ) : ℝ :=
  psi t + (c.b : ℝ) + (c.beta : ℝ) * (t - 1)

/-- A cell crosses the sign boundary precisely when it has both a positive
and a nonpositive target value. -/
def targetChangesSign (c : V22Class) (cell : V22Cell) : Prop :=
  (∃ t : ℝ, (cell.lo : ℝ) ≤ t ∧ t ≤ (cell.hi : ℝ) ∧ 0 < classTarget c t) ∧
  (∃ t : ℝ, (cell.lo : ℝ) ≤ t ∧ t ≤ (cell.hi : ℝ) ∧ classTarget c t ≤ 0)

/-- Lemma 7.20: the lower-range recipe is capped by the class's `W_lo`.
The split bonus and both forms of the persistent condition use the fixed
class lower bonus `D_lo`; the error and upper shape coefficient retain
the actual `r`, as enclosed in `fc_window.window_cell`. -/
def windowCellLower (c : V22Class) (cell : V22Cell) (t r : ℝ) : ℝ :=
  let N0 := (c.muD : ℝ) * (cell.lo : ℝ) + 2
  let Dlo := Delta c.ra N0
  let Wlo := min 3 (1 + Dlo)
  let lhs := lambdaT t + hbar (N0 - 2) + windowEL r N0 + windowRhoLbar r N0
  let wc := if 2 ≤ Dlo then lhs ≤ Real.log (1 + rho N0 * (Dlo - 2) / 2) else lhs ≤ 0
  let Xsplit := 1 - 2 / rho N0 * windowGhat t N0
    + Dlo / (1 + windowSbar t r N0 + windowRhoLbar r N0 * Dlo / 2)
    - 2 * windowEL r N0 / rho N0
  if wc then Wlo else min Wlo (max Xsplit (windowLogAt t r N0))

/-- Lemma 7.20: the upper-range recipe at the actual class activity.
Adding `c0Prime` back to `eU` drops its negative `-c₀'` term, exactly as
in `fc_window.window_cell`; the positive bonus uses the class's `D_lo`. -/
def windowCellUpper (c : V22Class) (cell : V22Cell) (t r : ℝ) : ℝ :=
  let N0 := (c.muD : ℝ) * (cell.lo : ℝ) + 2
  1 + Delta c.ra N0 - 2 / rhoStar N0 c.rb *
    G (min 0 (lambdaT t + (71 / 20) / (N0 + 1)
      + rhoU r N0 * Delta r N0 / 2 - (eU r N0 + c0Prime r N0)))

/-- Lemma 7.20: all three ranges with the exact fixed-class recipes of
`fc_window.window_cell`, enclosed over the actual `r`. -/
def windowCellMinimum (c : V22Class) (cell : V22Cell) (t r : ℝ) : ℝ :=
  min (windowCellLower c cell t r) (min 3 (windowCellUpper c cell t r))

/-- Note Lemma 7.20 (D3): both pointwise sign cases and the stronger
sign-crossing-cell requirement, on all fifty-four exact window cells. -/
def lemma_7_20 : Prop :=
  ∀ c ∈ classes, ∀ cell ∈ windowCells, cell.classId = c.classId →
    ∀ t r : ℝ, (cell.lo : ℝ) ≤ t → t ≤ (cell.hi : ℝ) →
      (c.ra : ℝ) ≤ r → r ≤ (c.rb : ℝ) →
      (0 < classTarget c t → classTarget c t / t ≤ windowCellMinimum c cell t r) ∧
      (classTarget c t ≤ 0 →
        let N0 := (c.muD : ℝ) * (cell.lo : ℝ) + 2
        classTarget c t * (N0 - 2) / (t * N0) ≤ windowCellMinimum c cell t r) ∧
      (targetChangesSign c cell → max (classTarget c t / t) 0 ≤ windowCellMinimum c cell t r)

/-- Section 5.3: exact activity endpoints of the inherited subinterval. -/
def rowQa (p : Nat) : ℝ := (pieceV22 p).lamLo / (1 + (pieceV22 p).lamLo)
def rowQb (p : Nat) : ℝ := (pieceV22 p).lamHi / (1 + (pieceV22 p).lamHi)
def rowEll0 (p : Nat) : ℝ := (((pieceV22 p).tilts.getD 0 (0, 0)).2 : ℝ)
def rowLb (p : Nat) : ℝ := -Real.log (1 - rowQb p)
def rowRhi (p : Nat) : ℝ := max |2 * rowQa p - 1| |2 * rowQb p - 1|
def rowVmin (p : Nat) : ℝ := min (rowQa p * (1 - rowQa p)) (rowQb p * (1 - rowQb p))

/-- Lemmas 5.3 and 7.12: the eight exact small-fiber constants. -/
def smallFiberK (M : Nat) : ℝ :=
  (smallK.getD M 0 : ℝ)

def rowA (p M : Nat) : ℝ := smallFiberK M / (4 * gaussianAmplitude * Real.sqrt (rowVmin p))
def rowSmallBase (p M : Nat) : ℝ :=
  rowA p M * Real.rpow (startingMean p) (3 / 2) + psi ((M : ℝ) / startingMean p) + excess p

/-- Lemma 5.3's two cases, exactly as the supplementary row recipe uses
them. The second branch keeps the larger bound `A μ₀^(3/2)`. -/
def rowSmallPrice (p M : Nat) : ℝ :=
  (if 0 < rowSmallBase p M then rowSmallBase p M
   else rowA p M * Real.rpow (startingMean p) (3 / 2)) *
    Real.rpow (1 - rowQb p) (-(M : ℝ)) * Real.exp (-rowEll0 p * startingMean p)

def maxList (xs : List ℝ) : ℝ := xs.foldl max 0
def rowZa (p : Nat) : ℝ := maxList ((List.range 8).map (rowSmallPrice p))

/-- Lemma 7.21 uses only central cells below the wing cut, and the exact
class cells on the outer subintervals. -/
def rowUsesCell (p : Nat) (cell : V22SpikeCell) : Prop :=
  match classForPiece p with
  | some c => cell.classId = c.classId
  | none => cell.classId = 0 ∧ (cell.hi : ℝ) ≤ spikeCutoff p

/-- Lemma 7.21: the lower `M` of one cell/block after enforcing the row's
actual mean and the `M≥8` restriction. -/
def rowBlockMlow (p : Nat) (cell : V22SpikeCell) (i : Nat) : ℝ :=
  max (max ((blockMultipliers.getD i 0 : ℝ) * (cell.ma : ℝ)) 8)
    ((cell.lo : ℝ) * startingMean p)

/-- Lemma 7.21: maximum of the two valid decay exponents, retaining the
cell's exact right endpoint and its lower `M` bound. -/
def rowBlockExponent (p : Nat) (cell : V22SpikeCell) (i : Nat) : ℝ :=
  max ((rowEll0 p / (cell.hi : ℝ) - rowLb p) * rowBlockMlow p cell i)
    ((rowEll0 p - (cell.hi : ℝ) * rowLb p) * startingMean p)

/-- Fixed six-digit upward certified exports, not the rounded Table 5
prices and not the four-digit Table 4 display. -/
def rowBlockPrice (p : Nat) (cell : V22SpikeCell) (i : Nat) : ℝ :=
  ((cell.logBounds.getD i 0 : ℝ) + excess p) * Real.exp (-rowBlockExponent p cell i)

def rowZb (p : Nat) : ℝ :=
  maxList (spikeCells.flatMap fun cell =>
    if rowUsesCell p cell then (List.range 5).map (rowBlockPrice p cell) else [])

/-- Lemma 5.5: the exact `m_c=max(μ₀,8/0.22)`. -/
def rowMc (p : Nat) : ℝ := max (startingMean p) (400 / 11)
def rowSmallRate (p : Nat) : ℝ := rowEll0 p - (11 / 50) * rowLb p
def rowZc (p : Nat) : ℝ :=
  (Real.rpow (rowMc p) (3 / 2) / (16 * Real.sqrt (rowVmin p) * gaussianAmplitude) + excess p) *
    Real.exp (-rowSmallRate p * rowMc p)

/-- Equation (5.2): the margin with the reconstructed three spike prices. -/
def rowMargin (p : Nat) : ℝ :=
  1 + excess p - ((pieceV22 p).theta : ℝ) - 9 * ((pieceV22 p).D : ℝ) / (2 * startingMean p)
    - (rowRhi p) ^ 2 / ((1 - (rowRhi p) ^ 2) * startingMean p)
    - max (rowZa p) (max (rowZb p) (rowZc p))

/-- Lemma 5.3: the full small-fiber monotonicity provisos. -/
def rowSmallSideConditions (p : Nat) : Prop :=
  ∀ M : Nat, M < 8 →
    (0 < rowSmallBase p M →
      (3 / 2) * rowA p M * Real.sqrt (startingMean p) ≤ rowEll0 p * rowSmallBase p M) ∧
    (rowSmallBase p M ≤ 0 → (3 / 2 : ℝ) ≤ rowEll0 p * startingMean p)

/-- Note Lemma 7.21 (ROW-v21): fifty-five positive real margins with
the inherited caps, exact starting means, all small-fiber and very-small-`t`
provisos, and strictly decaying weight on every cell used. The retained
six-digit certified exports make the numerical positivity obligation at
least as strong as the unrounded internal recipe. Displayed least margins
remain diagnostics and are not substituted for mathematical prices. -/
def lemma_7_21 : Prop :=
  ∀ p : Nat, p < 55 →
    19 ≤ startingMean p ∧ 0 ≤ excess p ∧ excess p ≤ 1 ∧
    0 < rowEll0 p ∧ 0 < rowVmin p ∧ rowSmallSideConditions p ∧
    (3 / 2 : ℝ) ≤ rowSmallRate p * rowMc p ∧
    (∀ cell ∈ spikeCells, rowUsesCell p cell → rowLb p < rowEll0 p / (cell.hi : ℝ)) ∧
    0 < rowMargin p

end

end Erdos993Lean.Analytic.V22.Checks
