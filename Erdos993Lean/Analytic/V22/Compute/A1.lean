import Erdos993Lean.Analytic.TailCert.Compute.Ival

/-!
# A1: the six exact polynomial cells

The repaired note's Lemma 7.2 uses the polynomial extension of Lambda(a)/a.
On each cell the positive polynomial factors are taken at its lower endpoint
and the factor 1-a at its upper endpoint. This module contains the computable
recipe only. A passing check is consumed by V22/A1Sound.lean.
-/

namespace Erdos993Lean.Analytic.V22.Compute.A1

open Erdos993Lean.Analytic.TailCert.Compute

abbrev Cell := Rat × Rat

/-- The six source cells, with both exact nominal endpoints retained. -/
def cells : List Cell :=
  [(0, 303 / 1000), (303 / 1000, 423 / 1000),
   (423 / 1000, 479 / 1000), (479 / 1000, 507 / 1000),
   (507 / 1000, 522 / 1000), (522 / 1000, 66 / 125)]

/-- Multiplication powers need no sign guard. -/
def powI (A : Ival) : Nat → Ival
  | 0 => pt one
  | n + 1 => mul (powI A n) A

/-- The exact polynomial Lambda, evaluated with outward interval arithmetic. -/
def lamI (A : Ival) : Ival :=
  add (add (add (add (add (mul (ofRat 2) A)
    (divNat (powI A 2) 2)) (divNat (powI A 3) 3))
    (divNat (powI A 4) 4)) (divNat (powI A 5) 5))
    (divNat (powI A 6) 6)

/-- The polynomial Lambda(a)/a, including its value 2 at zero. -/
def lamAI (A : Ival) : Ival :=
  add (add (add (add (add (ofRat 2) (divNat A 2))
    (divNat (powI A 2) 3)) (divNat (powI A 3) 4))
    (divNat (powI A 4) 5)) (divNat (powI A 5) 6)

/-- Outward enclosure of the monotone lower-corner formula Qlo. -/
def cornerI (c : Cell) : Ival :=
  let A := ofRat c.1
  let L := lamI A
  let LA := lamAI A
  sub (mul (mul (mul (ofRat (18 / 25)) (powI LA 2))
    (add (ofRat 1) (divNat (powI L 2) 75)))
    (sub (ofRat 1) (ofRat c.2))) (ofRat 2)

def threshold : Rat := 53 / 10000

/-- The real monotonicity bridge requires this exact source domain. -/
def domainGuard (c : Cell) : Bool :=
  decide (0 ≤ c.1 ∧ c.1 ≤ c.2 ∧ c.2 ≤ 66 / 125)

/-- Comparing to the threshold's outward upper endpoint is sound. -/
def passes (c : Cell) : Bool :=
  domainGuard c && decide ((ofRat threshold).hi ≤ (cornerI c).lo)

/-- No certificate theorem is installed here; the D4 layer may prove this Bool. -/
def check : Bool := cells.all passes

end Erdos993Lean.Analytic.V22.Compute.A1
