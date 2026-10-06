import Erdos993Lean.Analytic.Atlas.Checker

/-!
# The MGF + two-sided atlas checker (lane A22, milestone L3): Boolean checks in exact rational arithmetic

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A22.  Sources: the contract `LEAN/atlas_mgf/SPEC.md` v2 §§3–4
(M30, 2026-09-29 00:25: the checks (S), (T), (F), (Mg) and the data format), M30's `LEAN/atlas_mgf/ATLAS_MGF_PROOF.md`
(Theorem B) and its replay `replay_mgf.py`, lane R3X's seed constructor `LEAN/r3x/r3x_atlas_mgf.py`, Soul's
`SOUL/O4/ATLAS_PROOF.md` and lane A9's checker `Erdos993Lean/Analytic/Atlas/Checker.lean`, whose rational helpers,
binomial rows, kernel factor bounds and cover test are reused verbatim (this file imports it and only Lean's core).

What a passing check means is proved, for arbitrary data, in `Erdos993Lean/Analytic/MGF/Atoms.lean` and
`Erdos993Lean/Analytic/MGF/Sound.lean` (standard axioms only): `pieceOK` gives the criterion `ExplicitThresholdMGF2`
(`Erdos993Lean/Analytic/MGF/Criterion.lean`) at every `(q, m)` of the piece's rectangle.

## A box (`MBox`; SPEC v2 §3)

`q ∈ [ql, qh]`, `m ∈ [ml, mh]`; the dual `(ν, c, α, β, γ, a, b, z_k)` centred at `m0`:
`π(M) = α + β(M − m0) − γ(M − m0)²`, the two-sided kernel weights `a, b ≥ 0`, the tail prices `z_k ≥ 0` (one per tilt of
the piece); the cutoff `N` (fibres `M < N` are checked atom by atom, fibres `M ≥ N` by the elementary tail).  The tail
bases `s_k = 1 − qh + qh t_k` (the box's UPPER `q`: `s_k(q) = 1 − q + q t_k` decreases in `q` for `t_k ≤ 1`), the fibre
bound `rhs(M) = π(M) − ∑_k z_k s_k^M`, the elementary kernel constant `B = max(a, b)`, and `U_k = 1/∑_{i ≤ 120} x^i/i!`
at `x = ℓ_k ml` (`≥ e^{−ℓ_k ml}`).

## The checks of a box (`boxOK`)

* (S) `sane`: `0 < ql < qh < 1`, `ν > 0`, `γ ≥ 0`, `a, b ≥ 0`, `z ≥ 0`, `0 < ml ≤ mh`.
* (T) `tailOK` (every fibre `M ≥ N`): `π(N) ≤ −B − c²/(4ν)` and `β − 2γ(N − m0) ≤ 0` (the kernel is at least `−B`,
  `νδ² + cδ ≥ −c²/(4ν)`, `π` is nonincreasing from `N` on, and the priced rows only lower `rhs`).  No Fourier bound.
* (F) `fibresAll`: for every fibre `M < N`, with the binomial rows at `ql, q0, qh` carried as integer rows and the
  powers `s_k^M` carried along `M`:
  - (outside) `rhs(M)` is below the minimum of `νx² + cx` on `(−∞, −2 − ql·M]` and on `[M + 2 − qh·M, ∞)` (the kernel
    vanishes for `j ≤ −2` and `j ≥ M + 2`);
  - (atoms) `−1 ≤ j ≤ M + 1`: the fibre skips entirely when `lev := rhs + B + c²/(4ν) ≤ 0`; otherwise the atoms from
    `jloOf` to `jhiOf` are enumerated (SPEC v2's range `max(−1, ⌊ql M + vtx⌋ − R)` to `min(M + 1, ⌈qh M + vtx⌉ + R)`,
    `R = ⌈√(lev/ν)⌉ + 1`, `vtx = −c/(2ν)`, each end verified exactly by `leftY`/`rightY`; the atoms outside skip since
    `ν(δ − vtx)² ≥ lev` there, `κ₂ ≥ −B`); an enumerated atom passes when
    - it skips exactly (`atomSkip`: `ν d² ≥ lev` for the distance `d` from `vtx` to `[j − qh M, j − ql M]`), or
    - Soul's FIRST-ORDER bound `rhs ≤ κ₂_{q0}(M, j) − rad·K₁ + qmin` holds, or the SECOND-ORDER bound
      `rhs ≤ h(q0) − rad |h'(q0)| − (rad²/2)(K₂ + 2νM²)` with `h = κ₂ + cδ + νδ²` (`joint`), where for `0 ≤ j ≤ M`
      `κ₂_q = W(q) P(q)`, `W = b_M(j; q)/(q(1 − q))`, `P(x) = (a a_j)(1 − x)² + (b b_j) x²` (Soul's `a_j, b_j`),
      `K₁ = W_max (|P'|_max + |L|_max |P|_max)`, `K₂ = W_max (|P''| + 2 |L|_max |P'|_max + (|L|²_max + |L'|_max) |P|_max)`,
      `h'(q0) = W(q0)(P'(q0) + L(q0) P(q0)) − M(c + 2νδ0)`; at `j = −1`: `κ₂ = −b(1 − q)^M`, `K₁ = b M (1 − ql)^{M−1}`,
      `K₂ = b M(M − 1)(1 − ql)^{M−2}`; at `j = M + 1`: `κ₂ = −a q^M`, `K₁ = a M qh^{M−1}`, `K₂ = a M(M − 1) qh^{M−2}`;
      `qmin` is the exact minimum of `νδ² + cδ` on `δ ∈ [j − qh·M, j − ql·M]`.
* (Mg) `margin > 0`: `α + min(β(ml − m0), β(mh − m0)) − γ(D·mh + max((ml − m0)², (mh − m0)²)) − ν θ v_max mh −
  ∑_k z_k U_k > 0`.

## The piece (`pieceOK`)

The caps `θ, D ≥ 0`, the tilts `0 ≤ t_k ≤ 1` with rates `ℓ_k ≥ 0`; every box passes; the boxes cover
`[q(λ_lo), q(λ_hi)] × [mlo, mhi]` exactly (consecutive q-slabs, per slab a chain of boxes in `m`; SPEC v2 §4
`COVER.json`).
-/

namespace Erdos993Lean.Analytic.MGF

open Erdos993Lean.Analytic.Atlas

/-! ## Boxes and pieces -/

/-- One box of the MGF + two-sided atlas with its rational dual (centred at `m0`) and the cutoff `N`. -/
structure MBox where
  ql : Rat
  qh : Rat
  ml : Rat
  mh : Rat
  /-- the centre of the dual's quadratic minorant -/
  m0 : Rat
  nu : Rat
  c : Rat
  alpha : Rat
  beta : Rat
  gamma : Rat
  /-- the weight of `f_L/q` -/
  a : Rat
  /-- the weight of `f_R/(1 − q)` -/
  b : Rat
  /-- the tail prices `z_k`, one per tilt -/
  z : List Rat
  /-- the cutoff: fibres `M < N` are checked atom by atom, fibres `M ≥ N` by the elementary tail -/
  N : Nat

/-- One piece of the atlas: the caps `θ` (O2), `D` (O1), the certified tilts `(t_k, ℓ_k)` (O3) and the activity
interval `[λ_lo, λ_hi]`. -/
structure MPiece where
  theta : Rat
  D : Rat
  tilts : List (Rat × Rat)
  lamLo : Rat
  lamHi : Rat

namespace MBox

variable (b : MBox)

/-- The q-midpoint. -/
def q0 : Rat := (b.ql + b.qh) / 2

/-- The q-half-width. -/
def rad : Rat := (b.qh - b.ql) / 2

/-- `π(M) = α + β(M − m0) − γ(M − m0)²`. -/
def piQ (M : Nat) : Rat :=
  b.alpha + b.beta * ((M : Rat) - b.m0) - b.gamma * (((M : Rat) - b.m0) * ((M : Rat) - b.m0))

/-- `max_{q ∈ [ql, qh]} q(1 − q)`. -/
def vmax : Rat :=
  if b.ql ≤ 1 / 2 ∧ 1 / 2 ≤ b.qh then 1 / 4 else qmax (b.ql * (1 - b.ql)) (b.qh * (1 - b.qh))

/-- The elementary kernel constant `B = max(a, b)`: `a f_L/q + b f_R/(1 − q) ≥ −B` (SPEC v2 §3). -/
def kapB : Rat := qmax b.a b.b

/-- The vertex `−c/(2ν)` of `νδ² + cδ`. -/
def vtx : Rat := -b.c / (2 * b.nu)

/-- The tail bases `s_k = 1 − qh + qh t_k` of the tilts (the valid lower bounds of `s_k(q)` on the box). -/
def sVals (P : MPiece) : List Rat := P.tilts.map fun x => 1 - b.qh + b.qh * x.1

end MBox

/-- `∑_k z_k p_k` by position (the shorter list decides). -/
def pricedQ : List Rat → List Rat → Rat
  | z :: zs, p :: ps => z * p + pricedQ zs ps
  | _, _ => 0

/-- The fibre bound `rhs(M) = π(M) − ∑_k z_k s_k^M`, given the powers `pw_k = s_k^M`. -/
def rhsM (b : MBox) (pw : List Rat) (M : Nat) : Rat := b.piQ M - pricedQ b.z pw

/-! ## The two-sided kernel from a binomial row -/

/-- `κ₂_q(M, j) = a f_L/q + b f_R/(1 − q) = b(j) (a(1 − q)/q + b q/(1 − q)) − a b(j − 1) − b b(j + 1)` from the
binomial values `f` at `q`. -/
def kapRow2 (q : Rat) (j : Nat) (f : Nat → Rat) (a bb : Rat) : Rat :=
  f j * (a * (1 - q) / q + bb * q / (1 - q)) - a * (if j = 0 then 0 else f (j - 1)) - bb * f (j + 1)

/-! ## Skipping (elementary bounds only) -/

/-- `lev = rhs + B + c²/(4ν)`: an atom with `ν(δ − vtx)² ≥ lev` for every `q` of the box needs no binomial value
(`κ₂ + cδ + νδ² ≥ −B + ν(δ − vtx)² − c²/(4ν)`). -/
def skipLev (b : MBox) (rhs : Rat) : Rat := rhs + b.kapB + b.c * b.c / (4 * b.nu)

/-- The distance `ql·M + vtx − (jlo − 1)` covered on the left of `jlo`. -/
def leftY (b : MBox) (M : Nat) (jlo : Int) : Rat := b.ql * (M : Rat) + b.vtx - ((jlo : Rat) - 1)

/-- The distance `(jhi + 1) − qh·M − vtx` covered on the right of `jhi`. -/
def rightY (b : MBox) (M : Nat) (jhi : Int) : Rat := ((jhi : Rat) + 1) - b.qh * (M : Rat) - b.vtx

/-- `⌈√X⌉` for a rational `X`: the least natural `R` with `X ≤ R²` (bisection with fuel, no floating point; a heuristic
for the enumeration range, whose ends are verified exactly by `leftY`/`rightY`). -/
def sqrtCeil (X : Rat) : Nat := go 64 0 ((Rat.ceil X).toNat + 1)
where
  /-- `go k lo hi`: bisection between `lo` and `hi` (`X ≤ hi²`), `k` more steps. -/
  go : Nat → Nat → Nat → Nat
    | 0, _, hi => hi
    | k + 1, lo, hi =>
      if hi ≤ lo + 1 then (if X ≤ ((lo * lo : Nat) : Rat) then lo else hi)
      else
        let mid := (lo + hi) / 2
        if X ≤ ((mid * mid : Nat) : Rat) then go k lo mid else go k mid hi

/-- The radius `R = ⌈√(lev/ν)⌉ + 1` of SPEC v2 §3 (F). -/
def skipRad (b : MBox) (lev : Rat) : Int := (sqrtCeil (lev / b.nu) : Int) + 1

/-- The first enumerated atom: `max(−1, ⌊ql M + vtx⌋ − R)` if the left skip condition holds there, else `−1`. -/
def jloOf (b : MBox) (M : Nat) (lev : Rat) : Int :=
  let jlo := Rat.floor (b.ql * (M : Rat) + b.vtx) - skipRad b lev
  if decide (0 ≤ leftY b M jlo) && decide (lev ≤ b.nu * (leftY b M jlo * leftY b M jlo)) then max jlo (-1)
  else -1

/-- The last enumerated atom: `min(M + 1, ⌈qh M + vtx⌉ + R)` if the right skip condition holds there, else `M + 1`. -/
def jhiOf (b : MBox) (M : Nat) (lev : Rat) : Int :=
  let jhi := Rat.ceil (b.qh * (M : Rat) + b.vtx) + skipRad b lev
  if decide (0 ≤ rightY b M jhi) && decide (lev ≤ b.nu * (rightY b M jhi * rightY b M jhi)) then
    min jhi ((M : Int) + 1)
  else (M : Int) + 1

/-- The distance from `v` to the interval `[lo, hi]`. -/
def distMin (lo hi v : Rat) : Rat := if v < lo then lo - v else if hi < v then v - hi else 0

/-- The exact skip test of one atom: `ν d² ≥ lev` for the distance `d` from `vtx` to `δ ∈ [j − qh M, j − ql M]`. -/
def atomSkip (b : MBox) (M : Nat) (rhs : Rat) (j : Int) : Bool :=
  let d := distMin ((j : Rat) - b.qh * (M : Rat)) ((j : Rat) - b.ql * (M : Rat)) b.vtx
  decide (skipLev b rhs ≤ b.nu * (d * d))

/-! ## The atoms of one fibre -/

/-- Soul's second-order alternative: with `h(q) = κ₂_q + cδ + νδ²`,
`h(q0) − rad |h'(q0)| − (rad²/2)(|κ₂''|_max + 2νM²)`, the value and slope at `q0` exact, `δ0 = j − q0 M`. -/
def joint (b : MBox) (M : Nat) (j : Int) (kap k1 k2 : Rat) : Rat :=
  let d0 := (j : Rat) - b.q0 * (M : Rat)
  kap + (b.nu * (d0 * d0) + b.c * d0) - b.rad * qabs (k1 - (M : Rat) * (b.c + 2 * b.nu * d0)) -
    b.rad * b.rad * (k2 + 2 * b.nu * ((M : Rat) * (M : Rat))) / 2

/-- The atom `(M, j)`, `0 ≤ j ≤ M`: Soul's first-order bound with the two-sided coefficients `a a_j`, `b b_j`, or
else the second-order one. -/
def atomMid (b : MBox) (M j : Nat) (fl f0 fh : Nat → Rat) (pas : Array Nat) (rhs : Rat) : Bool :=
  let a := b.a * coefA M j
  let bb := b.b * coefB M j
  let wm := wmax M j b.ql b.qh fl fh pas
  let pa := pabs a bb b.ql b.qh
  let dp := dpabs a bb b.ql b.qh
  let la := labs M j b.ql b.qh
  decide (rhs ≤ kapRow2 b.q0 j f0 b.a b.b - b.rad * (wm * (dp + la * pa)) +
    quadMinI b.nu b.c ((j : Rat) - b.qh * (M : Rat)) ((j : Rat) - b.ql * (M : Rat))) ||
  decide (rhs ≤ joint b M (j : Int) (kapRow2 b.q0 j f0 b.a b.b)
    (f0 j / (b.q0 * (1 - b.q0)) * (dpval a bb b.q0 + lcomb M j b.q0 b.q0 * pval a bb b.q0))
    (wm * (qabs (2 * (a + bb)) + 2 * la * dp + (la * la + lpabs M j b.ql b.qh) * pa)))

/-- The atom `(M, −1)`: `κ₂ = −b(1 − q)^M`, `|κ₂'| ≤ b M (1 − ql)^{M−1}`, `|κ₂''| ≤ b M(M − 1)(1 − ql)^{M−2}`. -/
def atomNeg (b : MBox) (M : Nat) (rhs : Rat) : Bool :=
  decide (rhs ≤ -(b.b * (1 - b.q0) ^ M) - b.rad * (b.b * ((M : Rat) * (1 - b.ql) ^ (M - 1))) +
    quadMinI b.nu b.c (-1 - b.qh * (M : Rat)) (-1 - b.ql * (M : Rat))) ||
  decide (rhs ≤ joint b M (-1) (-(b.b * (1 - b.q0) ^ M)) (b.b * ((M : Rat) * (1 - b.q0) ^ (M - 1)))
    (b.b * ((M : Rat) * ((M : Rat) - 1) * (1 - b.ql) ^ (M - 2))))

/-- The atom `(M, M + 1)`: `κ₂ = −a q^M`, `|κ₂'| ≤ a M qh^{M−1}`, `|κ₂''| ≤ a M(M − 1) qh^{M−2}`. -/
def atomTop (b : MBox) (M : Nat) (rhs : Rat) : Bool :=
  decide (rhs ≤ -(b.a * b.q0 ^ M) - b.rad * (b.a * ((M : Rat) * b.qh ^ (M - 1))) +
    quadMinI b.nu b.c ((M : Rat) + 1 - b.qh * (M : Rat)) ((M : Rat) + 1 - b.ql * (M : Rat))) ||
  decide (rhs ≤ joint b M ((M : Int) + 1) (-(b.a * b.q0 ^ M)) (-(b.a * ((M : Rat) * b.q0 ^ (M - 1))))
    (b.a * ((M : Rat) * ((M : Rat) - 1) * b.qh ^ (M - 2))))

/-- The atom at the integer `j ∈ [−1, M + 1]`: the exact skip test, or the bound of its kind. -/
def atomAt (b : MBox) (M : Nat) (fl f0 fh : Nat → Rat) (pas : Array Nat) (rhs : Rat) (j : Int) : Bool :=
  atomSkip b M rhs j ||
  (if j = -1 then atomNeg b M rhs
  else if j = (M : Int) + 1 then atomTop b M rhs
  else atomMid b M j.toNat fl f0 fh pas rhs)

/-- The atoms `lo, lo + 1, …, lo + k − 1`. -/
def atomsFrom (b : MBox) (M : Nat) (fl f0 fh : Nat → Rat) (pas : Array Nat) (rhs : Rat) :
    Int → Nat → Bool
  | _, 0 => true
  | lo, k + 1 => atomAt b M fl f0 fh pas rhs lo && atomsFrom b M fl f0 fh pas rhs (lo + 1) k

/-- The whole fibre `M` (binomial values `fl`, `f0`, `fh` at `ql`, `q0`, `qh`; powers `pw_k = s_k^M`): the
half-lines, then either every atom skips (`lev ≤ 0`) or the atoms between `jloOf` and `jhiOf` are checked (the others
skip). -/
def fibreOK (b : MBox) (M : Nat) (fl f0 fh : Nat → Rat) (pas : Array Nat) (pw : List Rat) : Bool :=
  let rhs := rhsM b pw M
  let lev := skipLev b rhs
  decide (rhs ≤ quadMinLeft b.nu b.c (-2 - b.ql * (M : Rat))) &&
  decide (rhs ≤ quadMinRight b.nu b.c ((M : Rat) + 2 - b.qh * (M : Rat))) &&
  (decide (lev ≤ 0) ||
    atomsFrom b M fl f0 fh pas rhs (jloOf b M lev) (jhiOf b M lev - jloOf b M lev + 1).toNat)

/-- The fibres `M, M + 1, …, M + k − 1`, carrying the integer rows at `ql, q0, qh`, the powers `r^M`, Pascal's row
and the powers `s_k^M`. -/
def fibresLoop (b : MBox) (zl z0 zh : Zq) (sv : List Rat) : Nat → Nat → Array Nat → Array Nat → Array Nat →
    Nat → Nat → Nat → Array Nat → List Rat → Bool
  | 0, _, _, _, _, _, _, _, _, _ => true
  | k + 1, M, rl, r0, rh, rlM, r0M, rhM, pas, pw =>
    fibreOK b M (bval rl rlM) (bval r0 r0M) (bval rh rhM) pas pw &&
      fibresLoop b zl z0 zh sv k (M + 1) (zrowStep zl rl) (zrowStep z0 r0) (zrowStep zh rh)
        (rlM * zl.r) (r0M * z0.r) (rhM * zh.r) (pascalStep pas) (List.zipWith (· * ·) pw sv)

/-- Every fibre `M < N`. -/
def fibresAll (P : MPiece) (b : MBox) : Bool :=
  fibresLoop b (zq b.ql) (zq b.q0) (zq b.qh) (b.sVals P) b.N 0 #[1] #[1] #[1] 1 1 1 #[1]
    ((b.sVals P).map fun _ => 1)

/-! ## The tail `M ≥ N`, the sanity checks and the margin -/

/-- (T) The fibres `M ≥ N` by the elementary bound: `π(N) ≤ −B − c²/(4ν)` and `π` nonincreasing from `N` on. -/
def tailOK (b : MBox) : Bool :=
  decide (b.piQ b.N ≤ -b.kapB - b.c * b.c / (4 * b.nu)) &&
  decide (b.beta - 2 * b.gamma * ((b.N : Rat) - b.m0) ≤ 0)

/-- (S) Sanity of the data. -/
def sane (b : MBox) : Bool :=
  decide (0 < b.ql) && decide (b.ql < b.qh) && decide (b.qh < 1) && decide (0 < b.nu) &&
  decide (0 ≤ b.gamma) && decide (0 ≤ b.a) && decide (0 ≤ b.b) && b.z.all (fun x => decide (0 ≤ x)) &&
  decide (0 < b.ml) && decide (b.ml ≤ b.mh)

/-- The rational upper bound `1/∑_{i ≤ 120} x^i/i!` of `e^{−x}` (`x ≥ 0`; SPEC v2 §3, 121 terms). -/
def expNegUp (x : Rat) : Rat := 1 / expPartial x 121

/-- The upper bounds `U_k = expNegUp(ℓ_k·ml) ≥ e^{−ℓ_k ml}` of the piece's tilts. -/
def uList (P : MPiece) (ml : Rat) : List Rat := P.tilts.map fun x => expNegUp (x.2 * ml)

/-- (Mg) The expectation margin with the priced rows `∑_k z_k U_k`. -/
def margin (P : MPiece) (b : MBox) : Rat :=
  b.alpha + qmin (b.beta * (b.ml - b.m0)) (b.beta * (b.mh - b.m0)) -
    b.gamma * (P.D * b.mh + qmax ((b.ml - b.m0) * (b.ml - b.m0)) ((b.mh - b.m0) * (b.mh - b.m0))) -
    b.nu * P.theta * b.vmax * b.mh - pricedQ b.z (uList P b.ml)

/-- **All checks of one box.** -/
def boxOK (P : MPiece) (b : MBox) : Bool :=
  sane b && tailOK b && decide (0 < margin P b) && fibresAll P b

/-! ## The cover -/

/-- The boxes of `chain` contain the q-slab `[lo, hi]` and their m-intervals cover `[s, target]`. -/
def chainOK (boxes : List MBox) (lo hi : Rat) : Rat → Rat → List Nat → Bool
  | _, _, [] => false
  | s, target, i :: rest =>
    match boxes[i]? with
    | some b =>
      decide (b.ql ≤ lo) && decide (hi ≤ b.qh) && decide (b.ml ≤ s) &&
        (decide (target ≤ b.mh) || chainOK boxes lo hi b.mh target rest)
    | none => false

/-- The slabs cover `[start, qhi]` in `q`, each on `[mlo, mhi]` in `m`. -/
def slabsOK (boxes : List MBox) (qhi mlo mhi : Rat) : Rat → List Slab → Bool
  | _, [] => false
  | start, sl :: rest =>
    decide (sl.lo ≤ start) && chainOK boxes sl.lo sl.hi mlo mhi sl.chain &&
      (decide (qhi ≤ sl.hi) || slabsOK boxes qhi mlo mhi sl.hi rest)

/-- **The cover of `[qlo, qhi] × [mlo, mhi]`** by the boxes, slab by slab. -/
def coverOK (boxes : List MBox) (qlo qhi mlo mhi : Rat) (slabs : List Slab) : Bool :=
  slabsOK boxes qhi mlo mhi qlo slabs

/-! ## One piece -/

/-- The piece parameters: `θ, D ≥ 0`, the tilts `0 ≤ t_k ≤ 1` with rates `ℓ_k ≥ 0`. -/
def pieceSane (P : MPiece) : Bool :=
  decide (0 ≤ P.D) && decide (0 ≤ P.theta) &&
    P.tilts.all fun x => decide (0 ≤ x.1) && decide (x.1 ≤ 1) && decide (0 ≤ x.2)

/-- **All checks of one piece**: the parameters, every box, and the cover of `[q(λ_lo), q(λ_hi)] × [mlo, mhi]`. -/
def pieceOK (P : MPiece) (mlo mhi : Rat) (boxes : List MBox) (slabs : List Slab) : Bool :=
  pieceSane P && boxes.all (fun b => boxOK P b) &&
    coverOK boxes (actQQ P.lamLo) (actQQ P.lamHi) mlo mhi slabs

end Erdos993Lean.Analytic.MGF
