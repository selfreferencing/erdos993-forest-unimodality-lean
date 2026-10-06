import Erdos993Lean.Analytic.Ladder.O2.Data

/-!
# O2 certificate checker: the covers of the three O2R rows (lane A21)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A21.  Converted by `LEAN/lanes/A21/scratch/gen_o2.py` (lane A18's
token converter) from `LEAN/ladder/o2/certs/tight_cert_O2R{1,2,3}.json.gz` to one preorder string per root box
(`'l'`/`'x'`: split `λ`/`x`, lower half first; `'r'`: a leaf).  The soundness of the walk does not depend on these data.
-/

namespace Erdos993Lean.Analytic.Ladder.O2

/-- The twelve root covers of the O2R row 1 (777 leaves). -/
def o2r1Toks : List String := [
  "r",
  "r",
  "r",
  "xrr",
  "xxxxxrrxrrxxrrxrrxxxxrrxrrxxrxrrxxrrxrxrrxxxxxrrxrrxxxrrxrrxxrrxrrxxxxxrrxrrxxrrxrrxxxrrxrrxxrrxxrrxrrxxxxxrrxrrxxrrxrrxxxrrxrrxxrrxrrxxxxrrxrrxxrrxrrxxxrrxrrxxrrrxxxxxxrrxrrxxrrxrrxxxrrxrrxrrxxxrrxrrxrrxxxrrrxrrxxxxxxrrrxrrxrrxrrxrr",
  "xxxrrxrrxxrrxlrxrrxlrrlrr",
  "xxxlxrrxrrlxrrxrlrrxlxrrlxrrxrrlxlrrlrrlxrrxrrxxllrrlrxrrlrlrrxlrlrrlrlrxrr",
  "xxlxrrxrrlxrrxrrxlxrrxrrxlrrlrr",
  "xxxlrrlrxrrxlrrlrrxxlrrlrrxxlrrxlrrllrrxlrrlrrxxlxlrrlrrxlrrlrxrrlxlrrlrxrrxlxrrxrrlxrrrxlxlxrrrlrrxlrrlrrlxlrrlrrxlrrlrxrr",
  "xxxxxlxlrrlxrrxrrxlxrrxrrlxrlrrxlrrlrrlxlxrlrrxlrrlrrlxlrrlrrxlrrlrrxlxlrrlrrxlrrlrrlxlrrlrrxlrrrxlxlxlrrlrrxlrrrlxrrxrrxlxrrxrrlxrrxrrlxlxrrxrrlrrxlrrlrrxxlxlrrlrrxlrrlrrlxlrrlrrxlrrlrrxlxlrrlrrxlrrlrrlxlrrlrrxlrrlrxrrxxlxxlxrrxrrlxrrrxlrrlrrxxlxrrrlrrxlrrlxrrxrrxlxlxrrxrrlrrxlrrlrrlxlrrlxrrrxlrrlrrxlxxlxrrxrrlxrrxrrxlxrrxrrlxrrrxxlxrrrlxrrxrrxlxrrxrrlrrlxxlxrxrrxrxrrlxrrxrrxlxrrxrrlxrrxrrxxlxrrxrrlxrrxrrxlxrrxrrlxrrxrrxxxlxxlxrrxrrlxrrxrrxlxrrxrrlxrxrrxxrrxrrxxlxrrxrrlxrrxrrxlxrrxrrlxxrrxrrxxrrxrrlxxlxxrrxrrxxrrxrrlxxrrxrrxxrrxrrxlxxrrxrrxxrrxrrlxxrrxrrxxrrxrrxxlxxrrxrrxxrrxrrlxxrrxrrxxrrxrrxlxxrrxrrxxrrxrrlxxrrxrrxxrrxrrxlxxlxrrxrrlxrrxrrxlxrrxrrlxrrxrrxxlxxrrrxxrrrlxrrxrrxlxrrxrrlxrrxrrlxxlxrrxrrlxrrxrrxlrrlrrxxlxrrxrrlrrxlrrlrrxxxlxlrrlrrxlrrlrrllrrxlrrlrrxllrrxlrrlrrllrrxlrrlrrxxlxlrrlrrxlrrlrrlxlrrlrrxlrrlrrxlxlrrlrrxlrrlrrlxrrxrr",
  "xxxxxllrrlrrllrrlrrlxlrrlrrxlrrlrrxlxlrrrxlrrlrrxlrrlrrxxxlrrlrrxlrrlrrxxlrrlrrxlrrlrrxxxxlrrlrrxlrrlrrxxlrrlrrlrrxxlrrlrrxxlrrlrrxlrrlrr",
  "xxxxlrrlrrxlrrlrrxxlrrlrrxlrrlrrxxxlrrlrrxlrrlrrxxlrrlrrxlrrlrr"
]

/-- The twelve root covers of the O2R row 2 (460 leaves). -/
def o2r2Toks : List String := [
  "r",
  "r",
  "r",
  "xrr",
  "xxxxxrrxrrxxrrxrrxxxrrxxrrxrxrrxxxxrrxrxrrxxxrrxxrrxrrxxxrxrrxxrrxrrxxxrrxrxrrxxxrrxrrxxrrxrrxxxxxxxrrxrrxxrrxrrxxxrrxrrxxrrxrrxxxxrrxrrxxrrrxxrrxrrxxxxrrrxrrxxrrrxxxrrrxrrxxxxxrrxrrxrrxrrxrr",
  "xxxrrxrrxxrrxxrrxrr",
  "xxxxrrxrrxlrxrrlxrrxrrxxlxrrrlrrxrr",
  "xxxrrxrrxxrrxrxrr",
  "xxxrrxrrxxrrxxrrxxxrlrrxlrrlrxrrxxlxrrxrrlxrrxrrxlxlrrrxrrlxrrxrr",
  "xxxxxxlxrrxrrlxrrxrrxlxrrxrrlxlrrlrrxlrrlrrxxlxlrrlrrxlrrlrrlxlrrlrrxlrrlrrxlxlrrlrrxlrrlrrlxlrrlrrxlrrrxxxlxlrrrrlrrxlrrlrxrrxxlxrrxrrlxrrxrrxlxrrrlrrxxxxlrxrrlxrrxrrxlrrlrrxxlxrrxrrlxrrxrrxlxrrxrrlxrrxrrxxxlxrrxrrlxrxrrxrxrrxlxxrrxrrxxrrxrrlxxrrxrrxxrrrxxlxrrxrrlxxrrxrrxxrrxrrxlxxrrrxxrrrlxrrxrrxxxxxlxrrxrrlxrrxrrxlxrrxrrlxrrxrxrrxxlxlrrxrrxxrrxrrlxxrrxrrxxrrxrrxlxxrrxrrxxrrxrrlxxrrxrrxxrrxrrxxxlxrrxxrrrlxrrxrrxlxrrxrrlxrrxrrxxlxrrxrrlxrrxrrxlrrlrrxxxxlrrlrrlrrxlrrlrrxxlrrlrrxlrrxlrrr",
  "xxxxxlrrlrrxlrrlrrxxlrrrxrrxxlrrxrrxxrrxrrxxxxrrxrrxrrxxrrxrr",
  "xxxxrrrxxrrxrrxxrrxrxrr"
]

/-- The twelve root covers of the O2R row 3 (317 leaves). -/
def o2r3Toks : List String := [
  "r",
  "r",
  "r",
  "xrr",
  "xxxxrrxrrxxrrxrrxxrrxrr",
  "xxrrxrr",
  "xxrrxrxrr",
  "xxxrrxrxrrxxlxrrxrrlxrrxrrxlxrrxrrxrxrr",
  "xxxxrrrxrrxxrrxrxrr",
  "xxxrrxxrrxrrxxxxxrlrxrlrrxlxrlrrxlrrlrrlxlrrlrrxlrrlrrxxlxlrrlrrxlrrlrrlxlrrrxlrrlrrxlxlrrlrrxlrrlrrlxlrrlrrxlrrlrrxxxlxlrrlrrrlxrlrrxlrrlrrxlxlrrrxrrlxrrxrrxxlxrrxrrlxlrrrxrrxlxrrxrrlxrrxrlrrxxxxlxlrrlrrxlrrlrrlxlrrlrrxlrrlrrxlxlrrlrrxlrrlrrlxlrrlrrxlrrlrrxxlxlrrlrrxlrrlrrlxlrrlrrxlrrlrrxlxlrrlrrxlrrlrrlxlrrlrrxlrrlrrxxxlxlrrlrrxlrrlrrlxlrrrxrrxlxrrxrrlxrrxrrxlxxrrxrrxxrrxrrxlxrrrlrr",
  "xxxxxlxrrxrrlxrrxrrxlxrrxrrxlrrlrrxxxlrrlrrxlrrlrrxxlrrlrrlrrxxxlrrlrrxlrrlrrxxlrrlrrxlrrrxxxxrrxrrxxrrrxxrrxrr",
  "xxxxrrrxrrxxrrxxrrxrr"
]

end Erdos993Lean.Analytic.Ladder.O2
