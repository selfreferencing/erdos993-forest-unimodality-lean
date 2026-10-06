import Erdos993Lean.Analytic.V22.Compute.Expr
import Erdos993Lean.Analytic.V22.Compute.Grid
import Erdos993Lean.Analytic.V22.RationalData

/-!
# B1: exact small-fiber kernel recipes

Source: repaired Lemma 7.12 and supplementary_code/fc_check_B.py:51-78.
The expression preserves both weights, all three binomial masses, and the
source's division-first order. Binomial masses are zero outside their support.
Finite checks and their soundness are separate from these computable recipes.
-/

namespace Erdos993Lean.Analytic.V22.Compute.B1

def qE : Expr := .var 0
def oneMinusQE : Expr := .sub (.rat 1) qE

/-- Pascal recursion needs only Lean core; real soundness identifies it with
the ordinary binomial coefficient. -/
def binNat : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => binNat n k + binNat n (k + 1)

/-- The complete binomial mass, including its zero extension. -/
def binomialE (M : Nat) (j : Int) : Expr :=
  if 0 ≤ j ∧ j ≤ (M : Int) then
    .mul (.mul (.rat (binNat M j.toNat)) (.powNat qE j.toNat))
      (.powNat oneMinusQE (M - j.toNat))
  else .rat 0

def weightLE : Expr :=
  .mul (.powNat qE 2) (.sub (.rat 3) (.mul (.rat 4) qE))

def weightRE : Expr :=
  .mul (.powNat oneMinusQE 2) (.sub (.mul (.rat 4) qE) (.rat 1))

def fLE (M : Nat) (j : Int) : Expr :=
  .sub (.mul oneMinusQE (binomialE M j)) (.mul qE (binomialE M (j - 1)))

def fRE (M : Nat) (j : Int) : Expr :=
  .sub (.mul qE (binomialE M j)) (.mul oneMinusQE (binomialE M (j + 1)))

/-- Same rational expression as the source's kw_iv. Both divisions are guarded. -/
def kernelE (M : Nat) (j : Int) : Expr :=
  .add (.mul (.div weightLE qE) (fLE M j))
    (.mul (.div weightRE oneMinusQE) (fRE M j))

/-- The source's exact claimed margin is retained, not replaced by positivity. -/
def slackE (M : Nat) (j : Int) : Expr :=
  .sub (.add (kernelE M j) (.rat (smallK.getD M 0)))
    (.rat (smallMargins.getD M 0))

/-- Enumerating k=0,...,M+2 retains j=-1,...,M+1 exactly. -/
def offset (k : Nat) : Int := (k : Int) - 1

/-- The source's 800 exact adjacent cells of [1/4,3/4]. -/
def qPieces : List Span :=
  (List.range 800).map fun (i : Nat) =>
    (1 / 4 + (i : Rat) / 1600, 1 / 4 + ((i + 1 : Nat) : Rat) / 1600)

/-- Eight grouped fiber checks, retaining all 52 supported offsets and all
800 activity cells. Partition coverage and expression guards are checked. -/
def check : Bool :=
  partitionFrom (1 / 4) (3 / 4) qPieces &&
    (List.range 8).all fun M =>
      (List.range (M + 3)).all fun k =>
        nonnegativeOn (slackE M (offset k)) qPieces

end Erdos993Lean.Analytic.V22.Compute.B1
