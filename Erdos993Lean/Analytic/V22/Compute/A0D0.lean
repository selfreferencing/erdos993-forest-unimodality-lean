import Erdos993Lean.Analytic.TailCert.Compute.Ival
import Erdos993Lean.Analytic.V22.RationalData

/-! Exact-rational interval recipes for note Lemmas 7.1 (A0) and 7.16 (D0).
These definitions do not assert that any cell passed. -/

namespace Erdos993Lean.Analytic.V22.Compute
open Erdos993Lean.Analytic.TailCert.Compute

def phiQ (s : Rat) : Rat := (18/25)*(2-s/2)^2-2/(1+s)
def psiQ (t : Rat) : Rat := t-(9/2)*(t-1)^2

/-- A0's exact endpoint margins over the asserted lower bound. -/
def a0Recipe0 : Ival := ofRat (phiQ 0-399/500)
def a0Recipe1 : Ival := ofRat (phiQ (67/100)-399/500)
def a0Pass : Bool := decide (0 ≤ a0Recipe0.lo) && decide (0 ≤ a0Recipe1.lo)

/-- D0's exact rational margin, positive precisely when its target is negative. -/
def d0Margin (c : V22Class) : Rat := -(psiQ c.thi+c.b+c.beta*(c.thi-1))
def d0Recipe (c : V22Class) : Ival := ofRat (d0Margin c)
def d0Pass (c : V22Class) : Bool := decide (0 < (d0Recipe c).lo)

end Erdos993Lean.Analytic.V22.Compute
