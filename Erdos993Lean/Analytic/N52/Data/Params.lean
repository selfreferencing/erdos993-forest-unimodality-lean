import Erdos993Lean.Analytic.Atlas.Params

/-!
# The n ≥ 52 strip atlas: band parameters (lane A19)

The strip of band `i` (0-based) is `[q(λ_i), q(λ_{i+1})] × [stripFloor_i, (bandAt i).mmin]`: from the O5 floor
at `n ≥ 52`, `stripFloor_i = k_i/(2 q(λ_{i+1}))` with the ranks `k_i = 14` (bands 1–15, `k > ⌈52/4⌉ = 13`),
`15` (16–18), `16` (19–24), `17` (25–29), `18` (30) from the two Lean density records `x = 1`, `x = 11/10`
(`Erdos993Lean/Analytic/N52/Density.lean` proves the floor and the agreement), to Profile30's floor at `n ≥ 61`
(`Atlas.bandAt i`'s `mmin`, the lower edge of lane A9's lower atlas).  The other parameters (`D`, `θ`, the rates,
the edges) are lane A9's `Atlas.bandAt i` (Profile30's data).  This file imports only Lean's core.
-/

namespace Erdos993Lean.Analytic.N52.Data

open Erdos993Lean.Analytic.Atlas

private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- The floor of `m` at `n ≥ 52` per band (0-based): `k_i / (2 q(λ_{i+1}))`. -/
def stripFloor : List Rat :=
  [R (238) 9, R (49) 2, R (203) 9, R (21) 1, R (217) 11, R (56) 3, R (231) 13, R (17) 1, R (49) 3, R (63) 4, R (46) 3, R (329) 22, R (336) 23, R (343) 24, R (14) 1, R (765) 52, R (130) 9, R (795) 56, R (432) 29, R (44) 3, R (72) 5, R (184) 13, R (96) 7, R (40) 3, R (221) 16, R (187) 14, R (493) 38, R (1037) 82, R (221) 18, R (90) 7]

/-- The parameters of the strip of band `i`: lane A9's band with the n ≥ 52 floor. -/
def stripBand (i : Nat) : Band := { bandAt i with mmin := stripFloor.getD i 0 }

/-- The top of the strip of band `i`: Profile30's floor at `n ≥ 61`. -/
def stripCap (i : Nat) : Rat := (bandAt i).mmin

end Erdos993Lean.Analytic.N52.Data
