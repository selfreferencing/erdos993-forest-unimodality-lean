import Erdos993Lean.Analytic.Reserve.Assembly
import Erdos993Lean.Analytic.Reserve.Tail
import Erdos993Lean.Analytic.Reserve.Entropy
import Erdos993Lean.Analytic.Reserve.Cert.Sound
import Erdos993Lean.Analytic.Ladder.O1.BoxR1
import Erdos993Lean.Analytic.Ladder.O1.BoxR2
import Erdos993Lean.Analytic.Ladder.O1.BoxR3

/-!
# O1 on the three O1R rows: `Var M ≤ D m` on `[8/5, 33/20]` (`D = 7/5`), `[13/10, 7/5]` (`13/10`), `[22/25, 47/50]` (`11/10`)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A21.  Sources: lane R4X's `LEAN/r4x/REACH_BELOW_52.md` §5(b) (the
three O1 refits of the ladder), lane O1R's certificates and Lean drafts (`LEAN/ladder/o1/`: `INDEX.md`,
`lean_data/O1RDraft.lean`, whose text this module follows), the referee's independent replay
(`LEAN/referee/ladder_replay/REVIEW_LADDER_REPLAY.md`: all three rows CONFIRMED, every cell direct; the 16 hypotheses
of `Tails.tailOK_of` re-checked exactly with the envelopes below; verdict ADOPTED, `LEAN_CAMPAIGN_LOG.md` 20:45), and
the O1 machinery of lanes A11–A14: `Reserve.bandVar_of_ok` (`Reserve/Assembly.lean`), `Tails.tailOK_of`
(`Reserve/Tail.lean`), `Cert.leafOK_of_check`, `Cert.boxOK_of_check` (`Reserve/Cert/Sound.lean`), `entropyOK`.

All three rows use β = 0, α = 23q/50 and γ = λ(3 + λ)/13 (the B+ family, which is also the central family of
`band2`, `band3`); only `D` and the activity interval are new.

* `bandR1`, `bandR2`, `bandR3`: the rows as lane A11's `Reserve.Band`.
* `tailOK_bandRk`: the analytic tails from lane A13's rational envelopes (`Λ = hi`, `R = gDen/(3 + lo)`,
  `Γ = hi(3 + hi)/gDen`, `α₀ = aCoef·lo/(1 + lo)`), checked by `norm_num`.
* `leafOK_bandRk`: the selected-leaf base, lane A12's kernel checker (`decide +kernel`; 1, 1 and 2 cells).
* `boxOK_bandRk`: the finite box from the `native_decide` checks `box_R1` … `box_R3` (`BoxR1.lean` … `BoxR3.lean`).
* **`bandVar_bandR1_proved`, `bandVar_bandR2_proved`, `bandVar_bandR3_proved`**: O1 on the three rows, for every forest
  and every maximum-weight independent set (`Reserve.BandVar`).

Trust: the three `native_decide` box checks; everything else `propext`, `Classical.choice`, `Quot.sound`.

Scalarity check: `D` is the row's cap on `Var M / E M` (the variance of the free count `M`), produced by the cell
certificate through `bandVar_of_ok` and consumed by O4 on the sub-bands of the `N = 45` and `N = 44` steps
(`N45/Analytic.lean`, `N44/Analytic.lean`); `α, β, γ` are the reserve's multipliers, consumed only by the cell
comparisons; the envelopes `Λ, R, Γ, α₀` are per-row inputs of the tail lemma.
-/

namespace Erdos993Lean.Analytic.Ladder.O1

open Erdos993Lean.Analytic.Reserve Erdos993Lean.Analytic.Reserve.Tails
open Erdos993Lean.Analytic.Reserve.Cert Erdos993Lean.Analytic.Reserve.Cert.Compute

/-- O1R row 1: `λ ∈ [8/5, 33/20]`, `D = 7/5`, `α = 23q/50`, `β = 0`, `γ = λ(3+λ)/13` (the B+ family extended past
`8/5`). -/
def bandR1 : Band := ⟨8/5, 33/20, 7/5, 23/50, 13⟩

/-- O1R row 2: `λ ∈ [13/10, 7/5]`, `D = 13/10`, B+ multipliers. -/
def bandR2 : Band := ⟨13/10, 7/5, 13/10, 23/50, 13⟩

/-- O1R row 3: `λ ∈ [22/25, 47/50]`, `D = 11/10`, central multipliers. -/
def bandR3 : Band := ⟨22/25, 47/50, 11/10, 23/50, 13⟩

/-- **The analytic tails on the O1R row 1** (`Λ = 33/20`, `R = 65/23`, `Γ = 3069/5200`, `α₀ = 92/325`). -/
theorem tailOK_bandR1 : TailOK bandR1 :=
  tailOK_of bandR1 (Λ := 33 / 20) (R := 65 / 23) (Γ := 3069 / 5200) (α₀ := 92 / 325)
    (by norm_num [bandR1]) (by norm_num [bandR1]) (by norm_num [bandR1]) (by norm_num [bandR1])
    (by norm_num [bandR1]) (by norm_num [bandR1]) (by norm_num [bandR1]) (by norm_num [bandR1])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- **The analytic tails on the O1R row 2** (`Λ = 7/5`, `R = 130/43`, `Γ = 154/325`, `α₀ = 13/50`). -/
theorem tailOK_bandR2 : TailOK bandR2 :=
  tailOK_of bandR2 (Λ := 7 / 5) (R := 130 / 43) (Γ := 154 / 325) (α₀ := 13 / 50)
    (by norm_num [bandR2]) (by norm_num [bandR2]) (by norm_num [bandR2]) (by norm_num [bandR2])
    (by norm_num [bandR2]) (by norm_num [bandR2]) (by norm_num [bandR2]) (by norm_num [bandR2])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- **The analytic tails on the O1R row 3** (`Λ = 47/50`, `R = 325/97`, `Γ = 9259/32500`, `α₀ = 253/1175`). -/
theorem tailOK_bandR3 : TailOK bandR3 :=
  tailOK_of bandR3 (Λ := 47 / 50) (R := 325 / 97) (Γ := 9259 / 32500) (α₀ := 253 / 1175)
    (by norm_num [bandR3]) (by norm_num [bandR3]) (by norm_num [bandR3]) (by norm_num [bandR3])
    (by norm_num [bandR3]) (by norm_num [bandR3]) (by norm_num [bandR3]) (by norm_num [bandR3])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- The selected-leaf base on the O1R row 1 (kernel `decide`). -/
theorem leafOK_bandR1 : LeafOK bandR1 := leafOK_of_check bandR1 (by decide +kernel)

/-- The selected-leaf base on the O1R row 2 (kernel `decide`). -/
theorem leafOK_bandR2 : LeafOK bandR2 := leafOK_of_check bandR2 (by decide +kernel)

/-- The selected-leaf base on the O1R row 3 (kernel `decide`). -/
theorem leafOK_bandR3 : LeafOK bandR3 := leafOK_of_check bandR3 (by decide +kernel)

/-- **The finite box of the O1R row 1** (85,150 cells, `native_decide`). -/
theorem boxOK_bandR1 : BoxOK bandR1 := boxOK_of_check bandR1 trieR1 box_R1

/-- **The finite box of the O1R row 2** (71,868 cells, `native_decide`). -/
theorem boxOK_bandR2 : BoxOK bandR2 := boxOK_of_check bandR2 trieR2 box_R2

/-- **The finite box of the O1R row 3** (82,108 cells, `native_decide`). -/
theorem boxOK_bandR3 : BoxOK bandR3 := boxOK_of_check bandR3 trieR3 box_R3

/-- **O1 on `[8/5, 33/20]`**, `D = 7/5`: `Var M ≤ (7/5) m` for every forest, every activity of the row and every
maximum-weight independent set. -/
theorem bandVar_bandR1_proved : BandVar bandR1 :=
  bandVar_of_ok bandR1 (by norm_num [BandSide, bandR1]) entropyOK boxOK_bandR1 tailOK_bandR1 leafOK_bandR1

/-- **O1 on `[13/10, 7/5]`**, `D = 13/10`. -/
theorem bandVar_bandR2_proved : BandVar bandR2 :=
  bandVar_of_ok bandR2 (by norm_num [BandSide, bandR2]) entropyOK boxOK_bandR2 tailOK_bandR2 leafOK_bandR2

/-- **O1 on `[22/25, 47/50]`**, `D = 11/10`. -/
theorem bandVar_bandR3_proved : BandVar bandR3 :=
  bandVar_of_ok bandR3 (by norm_num [BandSide, bandR3]) entropyOK boxOK_bandR3 tailOK_bandR3 leafOK_bandR3

end Erdos993Lean.Analytic.Ladder.O1
