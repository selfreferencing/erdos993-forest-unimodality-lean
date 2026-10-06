import Erdos993Lean.Analytic.V22.Functions
import Erdos993Lean.Analytic.V22.RationalData
import Erdos993Lean.Analytic.V21.Pieces

/-! Shared definitions for the repaired paper v2.2, Tables 1 and 2.
The v2.1 activity edges, caps and rates are reused verbatim. -/

namespace Erdos993Lean.Analytic.V22

noncomputable section

/-- The existing exact activity, theta, hand-variance and Laplace-rate row. -/
def pieceV22 (p : Nat) := Erdos993Lean.Analytic.V21.pieceV21 p

/-- Table 2: starting mean of subinterval `p`. Statements restrict `p < 55`. -/
def startingMean (p : Nat) : ℝ := (mu0Data.getD p 0 : ℚ)

/-- Table 1 class membership, with the subinterval identity retained. -/
def classForPiece (p : Nat) : Option V22Class := classes.find? (fun c => decide (p ∈ c.iotas))

/-- The wing class of Theorem 5.8 (`thm:wing`), if present. -/
def wingForPiece (p : Nat) : Option V22WingClass := wingClasses.find? (fun c => decide (p ∈ c.iotas))

/-- Excess of the subinterval's class; zero on the central and wing pieces. -/
def excess (p : Nat) : ℝ := match classForPiece p with
  | some c => (c.b : ℚ)
  | none => 0

/-- The exact spike cutoff, including the three wing cutoffs. -/
def spikeCutoff (p : Nat) : ℝ := match classForPiece p with
  | some c => (c.tau : ℚ)
  | none => match wingForPiece p with
    | some c => (c.tau : ℚ)
    | none => 3 / 5

/-- Class data attached to a spike cell, if it is an outer cell. -/
def spikeClass (c : V22SpikeCell) : Option V22Class := classes.find? (fun k => k.classId == c.classId)

/-- The activity bound of Lemma 7.14. -/
def spikeRm (c : V22SpikeCell) : ℝ := match spikeClass c with
  | some k => (k.rb : ℚ)
  | none => 1 / 4

/-- The starting mean of the spike class, including the central value 19. -/
def spikeMean (c : V22SpikeCell) : ℝ := match spikeClass c with
  | some k => (k.muD : ℚ)
  | none => 19

/-- The five exact block multipliers in Table 4. -/
def blockMultipliers : List Nat := [1, 2, 4, 8, 16]

/-- The block represented by index `i<5`; the last block is unbounded above. -/
def inSpikeBlock (c : V22SpikeCell) (i : Nat) (M : ℝ) : Prop :=
  let m : ℝ := (blockMultipliers.getD i 0 : Nat)
  m * (c.ma : ℚ) ≤ M ∧ (i = 4 ∨ M ≤ 2 * m * (c.ma : ℚ))

end

end Erdos993Lean.Analytic.V22
