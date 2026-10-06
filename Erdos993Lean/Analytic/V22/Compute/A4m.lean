import Erdos993Lean.Analytic.V22.Compute.WindowExprs
import Erdos993Lean.Analytic.V22.Compute.Box

/-! A4m: direct enclosure of the actual activity on exact rational subcells.
The source has one grouped cell with 24 termwise subcells. This pure enclosure
uses 4000 smaller subcells and retains the stronger stated threshold 0.058. -/

namespace Erdos993Lean.Analytic.V22.Compute.A4m

def pieces : List Span := subdivide (3793/10000) (1/2) 4000
def recipe : Expr := .sub (WindowExprs.windowH (.var 0) (.rat (229/20))) (.rat (29/500))
def check : Bool := partitionFrom (3793/10000) (1/2) pieces && nonnegativeOn recipe pieces

end Erdos993Lean.Analytic.V22.Compute.A4m
