import Erdos993Lean.Analytic.HandVariance.Compute.Expr

/-!
# Exact recipe data types for the 4,321 hand variance checks

Source: TWIN v1.8 Appendix N.4, families `chk:tgt` and `chk:mc`.
Only exact rational inputs are stored. Reported floating-point lower bounds
are deliberately absent: acceptance must come from the sound Lean checker.
-/

namespace Erdos993Lean.Analytic.HandVariance.Compute

/-- One rational interval in a retained spatial coordinate. -/
structure Span where
  lo : Rat
  hi : Rat
  deriving Repr

/-- An AC vertex-function check, source `tgt:thm` and `mc:sec:method` (2). -/
structure VertexCheck where
  spatial : Span
  r : Rat
  J : Rat
  /-- `true` denotes the expression with denominator `gamma`. -/
  useGamma : Bool
  deriving Repr

/-- A CA check, retaining whether the source uses positive `Lbar` or Taylor. -/
structure CACheck where
  spatial : Span
  usePositiveL : Bool
  deriving Repr

/-- One activity interval with its exact polygon and all spatial recipes.
Segment numbers are lo=0, mid=1, u1=2, u2=3, u3=4, u4=5. -/
structure Activity where
  segment : Nat
  activity : Span
  center : Rat
  polygonActivity : Rat
  leftEnd : Rat
  Jcap : Rat
  useCut : Bool
  vertices : List (Rat × Rat)
  vertexChecks : List VertexCheck
  caChecks : List CACheck
  /-- Source mid uses two spatial halves; other segments use one evaluation. -/
  useHalves : Bool
  deriving Repr

/-- One polygon Taylor check, source paragraph after `tgt:lem:poly`. -/
structure PolygonCheck where
  activity : Rat
  intercept : Rat
  slope : Rat
  spatial : Span
  deriving Repr

/-- One child-tail chain check; `none` is the terminal endpoint at infinity. -/
structure ChainCheck where
  activity : Rat
  left : Rat
  right : Option Rat
  deriving Repr

/-- A polygon retains its lines, cap, exact Taylor partition and tail chain. -/
structure Polygon where
  activity : Rat
  tailStart : Rat
  lines : List (Rat × Rat)
  checks : List PolygonCheck
  chain : List ChainCheck
  deriving Repr

/-- One selected-leaf base check, `mc:lem:base` or the base of `tgt:thm`. -/
structure BaseCheck where
  segment : Nat
  activity : Span
  useHalves : Bool
  deriving Repr

end Erdos993Lean.Analytic.HandVariance.Compute
