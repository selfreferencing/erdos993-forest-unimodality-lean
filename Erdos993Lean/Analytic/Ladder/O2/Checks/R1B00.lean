import Erdos993Lean.Analytic.Ladder.O2.Tokens

/-!
# O2 certificate check: O2R row 1 (`[33/20, 7/4]`, `γ = 39/20`), root box 0 (lane A21)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A21.  `checkRoot o2r1SD 0 (o2r1Toks.getD 0 "") = true`, by lane
A18's cell checker (`Erdos993Lean/Analytic/O2/Cert/Compute/Engine.lean`, sound by `O2.Cert.rootOK_sound`).

Trust: the one `native_decide` of this module (`Lean.ofReduceBool`: the Lean compiler, here including the
natively compiled libraries `Erdos993LeanO2CertCompute` (lane A18) and `Erdos993LeanTailCertCompute` (lane A10)).
-/

namespace Erdos993Lean.Analytic.Ladder.O2

open Erdos993Lean.Analytic.O2.Cert.Compute

set_option profiler true
set_option profiler.threshold 500

/-- O2R row 1, root box 0, by `native_decide`. -/
theorem o2r1_b00 : checkRoot o2r1SD 0 (o2r1Toks.getD 0 "") = true := by native_decide

end Erdos993Lean.Analytic.Ladder.O2
