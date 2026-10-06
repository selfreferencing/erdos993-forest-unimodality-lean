import Erdos993Lean.Analytic.V22.Main
import Erdos993Lean.Analytic.V22.Analysis.CheckedInterface

/-! The unconditional paper v2.2 assembly. E's checked above-start theorem
instantiates F's unchanged ParameterNoValley interface on the actual mixture. -/
namespace Erdos993Lean.Analytic.V22

open Erdos993Lean

/-- Paper v2.2 Theorem 1.1: every finite forest has a unimodal independence sequence. -/
theorem erdos993_v22_final : Erdos993Statement :=
  erdos993_v22 V22.parameterNoValley_checked

end Erdos993Lean.Analytic.V22
