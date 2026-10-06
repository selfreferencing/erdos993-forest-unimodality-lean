import Mathlib
import Erdos993Lean.Analytic.MGF.Atoms
import Erdos993Lean.Analytic.MGF.Pieces
import Erdos993Lean.Analytic.Atlas.Fibres
import Erdos993Lean.Analytic.Atlas.Sound

/-!
# The MGF + two-sided atlas (lane A22): a passing piece gives the criterion `ExplicitThresholdMGF2`

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A22.  Sources: `LEAN/atlas_mgf/SPEC.md` v2 §3 (Theorem B: what a
box certifies), M30's `ATLAS_MGF_PROOF.md`, lane A9's `Atlas/Fibres.lean` and `Atlas/Sound.lean` (whose proofs are
repeated with the two changes: the priced rows in the fibre bound and the elementary tail); the checker
`Erdos993Lean/Analytic/MGF/Checker.lean`, the atoms `Erdos993Lean/Analytic/MGF/Atoms.lean`.

The conversion of the box theorem to the criterion at a point `(q, m)` of the box: `ν`, `c`, `γ`, `a`, `b`, `z` as in the
dual, `π` re-centred at `m` (`d = m − m0`, `α' = α + βd − γd²`, `β' = β − 2γd`), the rows `(s_k(q), e^{−ℓ_k m})` of the
piece's tilts.  (P) holds because `s_k(q) ≥ s_k(qh) ≥ 0` (so the checked fibre bound `π(M) − ∑ z_k s_k(qh)^M` dominates
`π(M) − ∑ z_k s_k(q)^M`); (Mg) is the checker's margin, because `e^{−ℓ_k m} ≤ e^{−ℓ_k ml} ≤ U_k` and the moment terms
are bounded over the box exactly as in `Atlas/Sound.lean`.

## Results (namespace `Erdos993Lean.Analytic.MGF`)

* `PowInv`, `powInv_zero`, `powInv_step`; `pricedQ_map_cast`, `pricedTail_nonneg`, `pricedTail_mono`,
  `pricedMargin_le`; `exp_neg_le_expNegUp` (121 terms).
* `FibreGood P b M` (the pointwise bound (P) at the fibre `M` with the tail-base rows); `jloOf_spec`, `jhiOf_spec`,
  **`fibreOK2_sound`**, `fibresLoop2_sound`, **`tailOK2_sound`** (the elementary tail), **`box_pointwise2`**.
* **`box_explicitThresholdMGF2`**: a box passing `boxOK P` (with `pieceSane P`) gives
  `ExplicitThresholdMGF2 q m θ D (mgfRows (castTilts P.tilts) q m)` at every `(q, m)` of the box.
* `chainOK2_sound`, `slabsOK2_sound`, `coverOK2_sound`; **`pieceOK_sound`**, **`pieceOK_noValley`**: a passing piece
  gives the criterion, and the no-valley property in MGF form, at every `q ∈ [q(λ_lo), q(λ_hi)]`, `m ∈ [mlo, mhi]`.

All results use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

open Erdos993Lean.Analytic Erdos993Lean.Analytic.Atlas Erdos993Lean.Analytic.NoValley

namespace Erdos993Lean.Analytic.MGF

/-! ## The priced rows -/

/-- The powers invariant of the fibre loop: `pw_k = s_k^M` for the tail bases `s_k`. -/
def PowInv (sv pw : List ℚ) (M : ℕ) : Prop := pw = sv.map fun s => s ^ M

theorem powInv_zero (sv : List ℚ) : PowInv sv (sv.map fun _ => 1) 0 := by
  simp [PowInv]

theorem powInv_step {sv pw : List ℚ} {M : ℕ} (h : PowInv sv pw M) :
    PowInv sv (List.zipWith (· * ·) pw sv) (M + 1) := by
  unfold PowInv at h ⊢
  subst h
  induction sv with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.map_cons, List.zipWith_cons_cons, List.cons.injEq]
    exact ⟨by rw [pow_succ], ih⟩

/-- The checker's priced sum of `M`-th powers of rational bases is `pricedTail` of the cast lists. -/
theorem pricedQ_pow_cast {α : Type*} (z : List ℚ) (l : List α) (g : α → ℚ) (M : ℕ) :
    ((pricedQ z (l.map fun x => g x ^ M) : ℚ) : ℝ) =
      pricedTail (z.map (Rat.cast : ℚ → ℝ)) (l.map fun x => (((g x : ℚ) : ℝ), (0 : ℝ))) M := by
  induction z generalizing l with
  | nil => cases l <;> simp [pricedQ]
  | cons x xs ih =>
    cases l with
    | nil => simp [pricedQ]
    | cons y ys =>
      simp only [pricedQ, List.map_cons, pricedTail_cons_cons]
      push_cast
      rw [ih ys]

/-- The checker's priced sum with exponent `1` (the margin's `∑ z_k U_k`). -/
theorem pricedQ_one_cast {α : Type*} (z : List ℚ) (l : List α) (g : α → ℚ) :
    ((pricedQ z (l.map g) : ℚ) : ℝ) =
      pricedTail (z.map (Rat.cast : ℚ → ℝ)) (l.map fun x => (((g x : ℚ) : ℝ), (0 : ℝ))) 1 := by
  have h := pricedQ_pow_cast z l g 1
  simpa using h

theorem pricedTail_nonneg : ∀ (z : List ℝ) (rows : List (ℝ × ℝ)) (M : ℕ), (∀ x ∈ z, 0 ≤ x) →
    (∀ r ∈ rows, 0 ≤ r.1) → 0 ≤ pricedTail z rows M := by
  intro z
  induction z with
  | nil => intro rows M _ _; simp
  | cons x xs ih =>
    intro rows M hz hr
    cases rows with
    | nil => simp
    | cons r rs =>
      simp only [pricedTail_cons_cons]
      have hx := hz x (List.mem_cons_self ..)
      have hr1 := hr r (List.mem_cons_self ..)
      have := ih rs M (fun y hy => hz y (List.mem_cons_of_mem _ hy)) (fun r' hr' => hr r' (List.mem_cons_of_mem _ hr'))
      have : 0 ≤ x * r.1 ^ M := mul_nonneg hx (pow_nonneg hr1 M)
      linarith

/-- Rows with larger nonnegative bases give a larger priced sum (`z ≥ 0`). -/
theorem pricedTail_mono : ∀ (z : List ℝ) (rows rows' : List (ℝ × ℝ)) (M : ℕ), (∀ x ∈ z, 0 ≤ x) →
    rows.length = rows'.length →
    (∀ i (hi : i < rows.length) (hi' : i < rows'.length), 0 ≤ rows[i].1 ∧ rows[i].1 ≤ rows'[i].1) →
    pricedTail z rows M ≤ pricedTail z rows' M := by
  intro z
  induction z with
  | nil => intro rows rows' M _ _ _; simp
  | cons x xs ih =>
    intro rows rows' M hz hlen hle
    cases rows with
    | nil =>
      cases rows' with
      | nil => simp
      | cons _ _ => simp at hlen
    | cons r rs =>
      cases rows' with
      | nil => simp at hlen
      | cons r' rs' =>
        simp only [pricedTail_cons_cons]
        have hx := hz x (List.mem_cons_self ..)
        have h0 := hle 0 (by simp) (by simp)
        simp only [List.getElem_cons_zero] at h0
        have hrest := ih rs rs' M (fun y hy => hz y (List.mem_cons_of_mem _ hy)) (by simpa using hlen)
          (fun i hi hi' => by
            have := hle (i + 1) (by simpa using hi) (by simpa using hi')
            simpa using this)
        have hpow : r.1 ^ M ≤ r'.1 ^ M := pow_le_pow_left₀ h0.1 h0.2 M
        have := mul_le_mul_of_nonneg_left hpow hx
        linarith

/-- `∑ z_k e_k ≤ ∑ z_k U_k` when `z_k ≥ 0` and `e_k ≤ U_k` (by position, same length; the bounds `U_k` are the first
components of a row list, priced with exponent `1`). -/
theorem pricedMargin_le : ∀ (z : List ℝ) (rows U : List (ℝ × ℝ)), (∀ x ∈ z, 0 ≤ x) →
    rows.length = U.length → (∀ i (hi : i < rows.length) (hi' : i < U.length), rows[i].2 ≤ U[i].1) →
    pricedMargin z rows ≤ pricedTail z U 1 := by
  intro z
  induction z with
  | nil => intro rows U _ _ _; simp
  | cons x xs ih =>
    intro rows U hz hlen hle
    cases rows with
    | nil =>
      cases U with
      | nil => simp
      | cons _ _ => simp at hlen
    | cons r rs =>
      cases U with
      | nil => simp at hlen
      | cons u us =>
        simp only [pricedMargin_cons_cons, pricedTail_cons_cons, pow_one]
        have hx := hz x (List.mem_cons_self ..)
        have h0 := hle 0 (by simp) (by simp)
        simp only [List.getElem_cons_zero] at h0
        have hrest := ih rs us (fun y hy => hz y (List.mem_cons_of_mem _ hy)) (by simpa using hlen)
          (fun i hi hi' => by
            have := hle (i + 1) (by simpa using hi) (by simpa using hi')
            simpa using this)
        have := mul_le_mul_of_nonneg_left h0 hx
        linarith

/-- `e^{−x} ≤ 1/∑_{i ≤ 120} x^i/i!` for rational `x ≥ 0` (SPEC v2's `U_k`, 121 terms). -/
theorem exp_neg_le_expNegUp {x : ℚ} (hx : 0 ≤ x) : Real.exp (-(x : ℝ)) ≤ ((expNegUp x : ℚ) : ℝ) := by
  have hxR : (0 : ℝ) ≤ x := by exact_mod_cast hx
  have hS : ((expPartial x 121 : ℚ) : ℝ) = ∑ l ∈ Finset.range 121, (x : ℝ) ^ l / (l.factorial : ℝ) := by
    rw [expPartial_eq]; push_cast; rfl
  have hle := Real.sum_le_exp_of_nonneg hxR 121
  have hpos : (1 : ℝ) ≤ ∑ l ∈ Finset.range 121, (x : ℝ) ^ l / (l.factorial : ℝ) := by
    rw [Finset.sum_range_succ']
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    have : 0 ≤ ∑ l ∈ Finset.range 120, (x : ℝ) ^ (l + 1) / ((l + 1).factorial : ℝ) :=
      Finset.sum_nonneg fun l _ => by positivity
    linarith
  unfold expNegUp
  push_cast
  rw [hS, Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by linarith) hle

/-! ## The fibres -/

/-- The tail-base rows of a box: `(s_k(qh), 0)` as reals (the second component is unused). -/
noncomputable def baseRows (tilts : List (ℚ × ℚ)) (qh : ℚ) : List (ℝ × ℝ) :=
  tilts.map fun x => (((1 - qh + qh * x.1 : ℚ) : ℝ), (0 : ℝ))

/-- **The pointwise fibre bound (P)** of a box at the fibre `M` with the tail-base rows: for every `q ∈ [ql, qh]` and
every integer `j`, `π(M) − ∑_k z_k s_k(qh)^M ≤ κ₂_q(M, j) + c(j − qM) + ν(j − qM)²`. -/
def FibreGood (P : MPiece) (b : MBox) (M : ℕ) : Prop :=
  ∀ q : ℝ, (b.ql : ℝ) ≤ q → q ≤ b.qh → ∀ j : ℤ,
    ((b.piQ M : ℚ) : ℝ) - pricedTail (b.z.map (Rat.cast : ℚ → ℝ)) (baseRows P.tilts b.qh) M ≤
      kernel2 q b.a b.b M j + (b.c : ℝ) * ((j : ℝ) - q * M) + (b.nu : ℝ) * ((j : ℝ) - q * M) ^ 2

theorem rhsM_cast {P : MPiece} {b : MBox} {pw : List ℚ} {M : ℕ} (hpw : PowInv (b.sVals P) pw M) :
    ((rhsM b pw M : ℚ) : ℝ) =
      ((b.piQ M : ℚ) : ℝ) - pricedTail (b.z.map (Rat.cast : ℚ → ℝ)) (baseRows P.tilts b.qh) M := by
  unfold rhsM
  rw [hpw]
  unfold MBox.sVals baseRows
  simp only [List.map_map, Function.comp_def]
  have h := pricedQ_pow_cast b.z P.tilts (fun x => 1 - b.qh + b.qh * x.1) M
  push_cast at h ⊢
  rw [h]

theorem jloOf_spec {b : MBox} {M : ℕ} {lev : ℚ} {j : ℤ} (hj : -1 ≤ j) (hlt : j < MGF.jloOf b M lev) :
    ∃ jlo : ℤ, j < jlo ∧ 0 ≤ MGF.leftY b M jlo ∧ lev ≤ b.nu * (MGF.leftY b M jlo * MGF.leftY b M jlo) := by
  unfold MGF.jloOf at hlt
  simp only at hlt
  split_ifs at hlt with h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨_, by omega, h.1, h.2⟩
  · omega

theorem jhiOf_spec {b : MBox} {M : ℕ} {lev : ℚ} {j : ℤ} (hj : j ≤ (M : ℤ) + 1) (hlt : MGF.jhiOf b M lev < j) :
    ∃ jhi : ℤ, jhi < j ∧ 0 ≤ MGF.rightY b M jhi ∧ lev ≤ b.nu * (MGF.rightY b M jhi * MGF.rightY b M jhi) := by
  unfold MGF.jhiOf at hlt
  simp only at hlt
  split_ifs at hlt with h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨_, by omega, h.1, h.2⟩
  · omega

/-- **A passing fibre gives (P) at that fibre** for every `q` of the box and every integer `j`. -/
theorem fibreOK2_sound {P : MPiece} {b : MBox} {M : ℕ} {fl f0 fh : ℕ → ℚ} {pas : Array ℕ} {pw : List ℚ}
    (hfl : BinomFn b.ql M fl) (hf0 : BinomFn b.q0 M f0) (hfh : BinomFn b.qh M fh) (hpas : PasInv M pas)
    (hpw : PowInv (b.sVals P) pw M)
    (h0 : (0 : ℝ) < b.ql) (hlh : (b.ql : ℝ) ≤ b.qh) (h1 : (b.qh : ℝ) < 1) (hnu : 0 < b.nu) (ha : 0 ≤ b.a)
    (hb : 0 ≤ b.b) (hok : MGF.fibreOK b M fl f0 fh pas pw = true) : FibreGood P b M := by
  unfold MGF.fibreOK at hok
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hL, hRt⟩, hrest⟩ := hok
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hnuR : (0 : ℝ) < b.nu := by exact_mod_cast hnu
  intro q hq hq' j
  rw [← rhsM_cast hpw]
  rcases lt_or_ge j (-1) with hj | hj
  · rw [kernel2_of_lt hj, zero_add]
    have hjr : (j : ℝ) ≤ -2 := by exact_mod_cast (by omega : j ≤ -2)
    have hQ := quadMinLeft_le (mu := b.nu) (c := b.c) (a := -2 - b.ql * (M : ℚ)) hnu
      (x := (j : ℝ) - q * M) (by push_cast; nlinarith)
    have hL' : ((rhsM b pw M : ℚ) : ℝ) ≤ ((quadMinLeft b.nu b.c (-2 - b.ql * (M : ℚ)) : ℚ) : ℝ) := by
      exact_mod_cast hL
    nlinarith [hQ, hL']
  rcases lt_or_ge ((M : ℤ) + 1) j with hj2 | hj2
  · rw [kernel2_of_gt hj2, zero_add]
    have hjr : (M : ℝ) + 2 ≤ (j : ℝ) := by exact_mod_cast (by omega : (M : ℤ) + 2 ≤ j)
    have hQ := quadMinRight_le (mu := b.nu) (c := b.c) (a := (M : ℚ) + 2 - b.qh * (M : ℚ)) hnu
      (x := (j : ℝ) - q * M) (by push_cast; nlinarith)
    have hR' : ((rhsM b pw M : ℚ) : ℝ) ≤ ((quadMinRight b.nu b.c ((M : ℚ) + 2 - b.qh * (M : ℚ)) : ℚ) : ℝ) := by
      exact_mod_cast hRt
    nlinarith [hQ, hR']
  have hκ := kernel2_ge_kapB h0 h1 ha hb M hq hq' j
  have hsq : 0 ≤ ((j : ℝ) - q * M - ((b.vtx : ℚ) : ℝ)) * ((j : ℝ) - q * M - ((b.vtx : ℚ) : ℝ)) :=
    mul_self_nonneg _
  rcases hrest with hlev | hatoms
  · refine skip_sound hnu hκ ?_
    have := (Rat.cast_le (K := ℝ)).mpr hlev
    unfold MGF.skipLev at this
    push_cast at this ⊢
    nlinarith
  · by_cases hjl : j < MGF.jloOf b M (MGF.skipLev b (rhsM b pw M))
    · obtain ⟨jlo, hjlo, hY0, hY⟩ := jloOf_spec hj hjl
      refine skip_sound hnu hκ ?_
      have hY0' : (0 : ℝ) ≤ ((MGF.leftY b M jlo : ℚ) : ℝ) := by exact_mod_cast hY0
      have hY' := (Rat.cast_le (K := ℝ)).mpr hY
      unfold MGF.skipLev at hY'
      have hLY : ((MGF.leftY b M jlo : ℚ) : ℝ) = (b.ql : ℝ) * M + ((b.vtx : ℚ) : ℝ) - ((jlo : ℝ) - 1) := by
        unfold MGF.leftY; push_cast; ring
      have hjj : (j : ℝ) ≤ (jlo : ℝ) - 1 := by exact_mod_cast (by omega : j ≤ jlo - 1)
      have hd : (j : ℝ) - q * M - ((b.vtx : ℚ) : ℝ) ≤ -((MGF.leftY b M jlo : ℚ) : ℝ) := by
        rw [hLY]; nlinarith
      have hsq2 : ((MGF.leftY b M jlo : ℚ) : ℝ) * ((MGF.leftY b M jlo : ℚ) : ℝ) ≤
          ((j : ℝ) - q * M - ((b.vtx : ℚ) : ℝ)) * ((j : ℝ) - q * M - ((b.vtx : ℚ) : ℝ)) := by
        nlinarith
      push_cast at hY' ⊢
      nlinarith [mul_le_mul_of_nonneg_left hsq2 hnuR.le]
    by_cases hjh : MGF.jhiOf b M (MGF.skipLev b (rhsM b pw M)) < j
    · obtain ⟨jhi, hjhi, hY0, hY⟩ := jhiOf_spec hj2 hjh
      refine skip_sound hnu hκ ?_
      have hY0' : (0 : ℝ) ≤ ((MGF.rightY b M jhi : ℚ) : ℝ) := by exact_mod_cast hY0
      have hY' := (Rat.cast_le (K := ℝ)).mpr hY
      unfold MGF.skipLev at hY'
      have hRY : ((MGF.rightY b M jhi : ℚ) : ℝ) = ((jhi : ℝ) + 1) - (b.qh : ℝ) * M - ((b.vtx : ℚ) : ℝ) := by
        unfold MGF.rightY; push_cast; ring
      have hjj : (jhi : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (by omega : jhi + 1 ≤ j)
      have hd : ((MGF.rightY b M jhi : ℚ) : ℝ) ≤ (j : ℝ) - q * M - ((b.vtx : ℚ) : ℝ) := by
        rw [hRY]; nlinarith
      have hsq2 : ((MGF.rightY b M jhi : ℚ) : ℝ) * ((MGF.rightY b M jhi : ℚ) : ℝ) ≤
          ((j : ℝ) - q * M - ((b.vtx : ℚ) : ℝ)) * ((j : ℝ) - q * M - ((b.vtx : ℚ) : ℝ)) := by
        nlinarith
      push_cast at hY' ⊢
      nlinarith [mul_le_mul_of_nonneg_left hsq2 hnuR.le]
    · push_neg at hjl hjh
      have hat := atomsFrom2_sound _ _ hatoms j hjl (by
        have : MGF.jhiOf b M (MGF.skipLev b (rhsM b pw M)) - MGF.jloOf b M (MGF.skipLev b (rhsM b pw M)) + 1 ≥ 0 := by
          omega
        rw [Int.toNat_of_nonneg this]; omega)
      exact atomAt2_sound hfl hf0 hfh hpas h0 hlh h1 hnu ha hb hj hj2 hat hq hq'

/-- The loop over the fibres (integer rows at `ql, q0, qh`, the powers `s_k^M`). -/
theorem fibresLoop2_sound {P : MPiece} {b : MBox} (h0 : (0 : ℝ) < b.ql) (hlh : (b.ql : ℝ) ≤ b.qh)
    (h1 : (b.qh : ℝ) < 1) (hnu : 0 < b.nu) (ha : 0 ≤ b.a) (hb : 0 ≤ b.b) :
    ∀ (k M : ℕ) (rl r0 rh : Array ℕ) (rlM r0M rhM : ℕ) (pas : Array ℕ) (pw : List ℚ),
      ZRowInv b.ql M rl rlM → ZRowInv b.q0 M r0 r0M → ZRowInv b.qh M rh rhM → PasInv M pas →
      PowInv (b.sVals P) pw M →
      MGF.fibresLoop b (zq b.ql) (zq b.q0) (zq b.qh) (b.sVals P) k M rl r0 rh rlM r0M rhM pas pw = true →
        ∀ M', M ≤ M' → M' < M + k → FibreGood P b M' := by
  have hl0 : (0 : ℚ) ≤ b.ql := by exact_mod_cast h0.le
  have hl1 : b.ql ≤ 1 := by exact_mod_cast (by linarith : (b.ql : ℝ) ≤ 1)
  have hh0 : (0 : ℚ) ≤ b.qh := by exact_mod_cast (by linarith : (0 : ℝ) ≤ b.qh)
  have hh1 : b.qh ≤ 1 := by exact_mod_cast h1.le
  have hq00 : (0 : ℚ) ≤ b.q0 := by unfold MBox.q0; linarith
  have hq01 : b.q0 ≤ 1 := by unfold MBox.q0; linarith
  intro k
  induction k with
  | zero => intro M _ _ _ _ _ _ _ _ _ _ _ _ _ _ M' h1' h2'; omega
  | succ k ih =>
    intro M rl r0 rh rlM r0M rhM pas pw hrl hr0 hrh hpas hpw hok M' hM1 hM2
    unfold MGF.fibresLoop at hok
    simp only [Bool.and_eq_true] at hok
    rcases eq_or_lt_of_le hM1 with he | hlt
    · subst he
      exact fibreOK2_sound (bval_binomFn hrl) (bval_binomFn hr0) (bval_binomFn hrh) hpas hpw h0 hlh h1 hnu
        ha hb hok.1
    · exact ih (M + 1) _ _ _ _ _ _ _ _ (zRowInv_step hl0 hl1 hrl) (zRowInv_step hq00 hq01 hr0)
        (zRowInv_step hh0 hh1 hrh) (pasInv_step hpas) (powInv_step hpw) hok.2 M' (by omega) (by omega)

/-- The tail-base rows have nonnegative bases when `0 ≤ t_k` and `qh ≤ 1`. -/
theorem baseRows_nonneg {P : MPiece} {qh : ℚ} (hqh0 : 0 ≤ qh) (hqh : qh ≤ 1)
    (ht : ∀ x ∈ P.tilts, 0 ≤ x.1) : ∀ r ∈ baseRows P.tilts qh, 0 ≤ r.1 := by
  intro r hr
  unfold baseRows at hr
  rw [List.mem_map] at hr
  obtain ⟨x, hx, rfl⟩ := hr
  have h2 := ht x hx
  have h3 : (0 : ℚ) ≤ 1 - qh + qh * x.1 := by nlinarith
  show (0 : ℝ) ≤ ((1 - qh + qh * x.1 : ℚ) : ℝ)
  exact_mod_cast h3

/-- **The fibres `M ≥ N`** by the elementary bound: `π(M) ≤ π(N) ≤ −B − c²/(4ν)`, the priced rows only lower `rhs`. -/
theorem tailOK2_sound {P : MPiece} {b : MBox} (h0 : (0 : ℝ) < b.ql) (hlh : (b.ql : ℝ) ≤ b.qh)
    (h1 : (b.qh : ℝ) < 1) (hnu : 0 < b.nu)
    (hga : 0 ≤ b.gamma) (ha : 0 ≤ b.a) (hb : 0 ≤ b.b) (hz : ∀ x ∈ b.z, 0 ≤ x) (ht : ∀ x ∈ P.tilts, 0 ≤ x.1)
    (hok : MGF.tailOK b = true) : ∀ M, b.N ≤ M → FibreGood P b M := by
  unfold MGF.tailOK at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hpi, hbeta⟩ := hok
  intro M hNM q hq hq' j
  have hNM' : (b.N : ℝ) ≤ M := by exact_mod_cast hNM
  have hκ := kernel2_ge_kapB h0 h1 ha hb M hq hq' j
  have hquad := NoValley.quad_lower_bound (ν := (b.nu : ℝ)) (by exact_mod_cast hnu) (b.c : ℝ)
    ((j : ℝ) - q * M)
  have hpiN : ((b.piQ b.N : ℚ) : ℝ) ≤ -((b.kapB : ℚ) : ℝ) - (b.c : ℝ) * (b.c : ℝ) / (4 * (b.nu : ℝ)) := by
    have := (Rat.cast_le (K := ℝ)).mpr hpi; push_cast at this; exact this
  have hmono : ((b.piQ M : ℚ) : ℝ) ≤ ((b.piQ b.N : ℚ) : ℝ) := by
    rw [MBox.piQ_cast, MBox.piQ_cast]
    have hb' : ((b.beta - 2 * b.gamma * ((b.N : ℚ) - b.m0) : ℚ) : ℝ) ≤ 0 := by exact_mod_cast hbeta
    push_cast at hb'
    have hg : (0 : ℝ) ≤ b.gamma := by exact_mod_cast hga
    nlinarith [mul_nonneg (sub_nonneg.mpr hNM') hg, mul_nonneg (sub_nonneg.mpr hNM') (sub_nonneg.mpr hNM')]
  have hts : 0 ≤ pricedTail (b.z.map (Rat.cast : ℚ → ℝ)) (baseRows P.tilts b.qh) M := by
    have hqh0 : (0 : ℚ) ≤ b.qh := by exact_mod_cast (h0.le.trans hlh)
    refine pricedTail_nonneg _ _ M ?_ (baseRows_nonneg hqh0 (by exact_mod_cast h1.le) ht)
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact_mod_cast hz y hy
  have hc2 : -(b.c : ℝ) ^ 2 / (4 * (b.nu : ℝ)) = -((b.c : ℝ) * (b.c : ℝ) / (4 * (b.nu : ℝ))) := by ring
  rw [hc2] at hquad
  linarith

/-- **The pointwise bound (P) at every fibre** of a box passing `sane`, `tailOK` and `fibresAll`. -/
theorem box_pointwise2 {P : MPiece} {b : MBox} (ht : ∀ x ∈ P.tilts, 0 ≤ x.1) (hs : MGF.sane b = true)
    (htail : MGF.tailOK b = true) (hf : MGF.fibresAll P b = true) : ∀ M, FibreGood P b M := by
  unfold MGF.sane at hs
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, hlh⟩, h1⟩, hnu⟩, hga⟩, ha⟩, hb⟩, hz⟩, -⟩, -⟩ := hs
  have h0' : (0 : ℝ) < b.ql := by exact_mod_cast h0
  have hlh' : (b.ql : ℝ) ≤ b.qh := by exact_mod_cast hlh.le
  have h1' : (b.qh : ℝ) < 1 := by exact_mod_cast h1
  intro M
  rcases lt_or_ge M b.N with hMN | hMN
  · exact fibresLoop2_sound h0' hlh' h1' hnu ha hb b.N 0 _ _ _ _ _ _ _ _ (zRowInv_zero _) (zRowInv_zero _)
      (zRowInv_zero _) pasInv_zero (powInv_zero _) hf M (Nat.zero_le _) (by omega)
  · exact tailOK2_sound h0' hlh' h1' hnu hga ha hb hz ht htail M hMN

/-! ## From a passing box to the criterion -/

theorem MBox.vmax_ge {b : MBox} {q : ℝ} (hq : (b.ql : ℝ) ≤ q) (hq' : q ≤ b.qh) :
    q * (1 - q) ≤ ((b.vmax : ℚ) : ℝ) := by
  unfold MBox.vmax
  split_ifs with h
  · push_cast; nlinarith [sq_nonneg (q - 1 / 2)]
  · simp only [qmax_cast]
    push_cast
    push_neg at h
    by_cases hl : b.ql ≤ 1 / 2
    · have hh : b.qh < 1 / 2 := h hl
      have hh' : (b.qh : ℝ) < 1 / 2 := by
        have := (Rat.cast_lt (K := ℝ)).mpr hh; push_cast at this; linarith
      exact (by nlinarith : q * (1 - q) ≤ (b.qh : ℝ) * (1 - b.qh)).trans (le_max_right _ _)
    · push_neg at hl
      have hl' : (1 / 2 : ℝ) < b.ql := by
        have := (Rat.cast_lt (K := ℝ)).mpr hl; push_cast at this; linarith
      exact (by nlinarith : q * (1 - q) ≤ (b.ql : ℝ) * (1 - b.ql)).trans (le_max_left _ _)

/-- The piece's sanity, unpacked. -/
theorem pieceSane_spec {P : MPiece} (h : pieceSane P = true) :
    0 ≤ P.D ∧ 0 ≤ P.theta ∧ ∀ x ∈ P.tilts, 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 := by
  unfold pieceSane at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1, h.1.2, fun x hx => ⟨(h.2 x hx).1.1, (h.2 x hx).1.2, (h.2 x hx).2⟩⟩

/-- **A passing box gives the criterion** at every `(q, m)` of the box, with the rows `(s_k(q), e^{−ℓ_k m})` of the
piece's tilts (SPEC v2 §3, Theorem B). -/
theorem box_explicitThresholdMGF2 {P : MPiece} {b : MBox} (hPs : pieceSane P = true) (hok : MGF.boxOK P b = true)
    {q m : ℝ} (hq : (b.ql : ℝ) ≤ q) (hq' : q ≤ b.qh) (hm : (b.ml : ℝ) ≤ m) (hm' : m ≤ b.mh) :
    ExplicitThresholdMGF2 q m (P.theta : ℝ) (P.D : ℝ) (mgfRows (castTilts P.tilts) q m) := by
  obtain ⟨hD, hθ, htilts⟩ := pieceSane_spec hPs
  unfold MGF.boxOK at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hs, ht⟩, hmargin⟩, hf⟩ := hok
  have hpt := box_pointwise2 (fun x hx => (htilts x hx).1) hs ht hf
  have hs' := hs
  unfold MGF.sane at hs'
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hs'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, hlh⟩, h1⟩, hnu⟩, hga⟩, ha⟩, hb⟩, hz⟩, hml0⟩, hmlh⟩ := hs'
  have h0R : (0 : ℝ) < b.ql := by exact_mod_cast h0
  have h1R : (b.qh : ℝ) < 1 := by exact_mod_cast h1
  have hnuR : (0 : ℝ) < b.nu := by exact_mod_cast hnu
  have hgaR : (0 : ℝ) ≤ b.gamma := by exact_mod_cast hga
  have hzR : ∀ x ∈ b.z.map (Rat.cast : ℚ → ℝ), 0 ≤ x := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact_mod_cast hz y hy
  set m0 : ℝ := ((b.m0 : ℚ) : ℝ) with hm0
  set d : ℝ := m - m0 with hd
  refine ⟨b.nu, b.c, (b.alpha : ℝ) + (b.beta : ℝ) * d - (b.gamma : ℝ) * d ^ 2,
    (b.beta : ℝ) - 2 * (b.gamma : ℝ) * d, b.gamma, b.a, b.b, b.z.map (Rat.cast : ℚ → ℝ), hnuR, hgaR,
    by exact_mod_cast ha, by exact_mod_cast hb, hzR, ?_, ?_⟩
  · -- (P): the re-centred `π` is `π(M)`, and the rows at `q` dominate the tail-base rows
    intro M j
    have hπ : (b.alpha : ℝ) + (b.beta : ℝ) * d - (b.gamma : ℝ) * d ^ 2 +
        ((b.beta : ℝ) - 2 * (b.gamma : ℝ) * d) * ((M : ℝ) - m) - (b.gamma : ℝ) * ((M : ℝ) - m) ^ 2 =
        ((b.piQ M : ℚ) : ℝ) := by
      rw [MBox.piQ_cast, hd]; ring
    have hrows : pricedTail (b.z.map (Rat.cast : ℚ → ℝ)) (baseRows P.tilts b.qh) M ≤
        pricedTail (b.z.map (Rat.cast : ℚ → ℝ)) (mgfRows (castTilts P.tilts) q m) M := by
      refine pricedTail_mono _ _ _ M hzR ?_ ?_
      · unfold baseRows mgfRows castTilts; simp
      · intro i hi hi'
        unfold baseRows at hi ⊢
        unfold mgfRows castTilts at hi' ⊢
        simp only [List.getElem_map]
        set x := P.tilts[i]'(by simpa using hi) with hx
        have hxm : x ∈ P.tilts := List.getElem_mem _
        obtain ⟨ht0, ht1, -⟩ := htilts x hxm
        have ht0R : (0 : ℝ) ≤ ((x.1 : ℚ) : ℝ) := by exact_mod_cast ht0
        have ht1R : ((x.1 : ℚ) : ℝ) ≤ 1 := by exact_mod_cast ht1
        have hqhR : (0 : ℝ) ≤ b.qh := by linarith
        push_cast
        constructor
        · nlinarith
        · nlinarith
    have := hpt M q hq hq' j
    linarith
  · -- (Mg): the checker's margin
    have hmR : (0 : ℝ) < m := lt_of_lt_of_le (by exact_mod_cast hml0) hm
    have hmarg : (0 : ℝ) < ((MGF.margin P b : ℚ) : ℝ) := by exact_mod_cast hmargin
    unfold MGF.margin at hmarg
    push_cast at hmarg
    simp only [qmin_cast, qmax_cast] at hmarg
    push_cast at hmarg
    -- the priced margin is at most `∑ z_k U_k`
    have hU : pricedMargin (b.z.map (Rat.cast : ℚ → ℝ)) (mgfRows (castTilts P.tilts) q m) ≤
        ((pricedQ b.z (MGF.uList P b.ml) : ℚ) : ℝ) := by
      unfold MGF.uList
      rw [pricedQ_one_cast b.z P.tilts (fun x => expNegUp (x.2 * b.ml))]
      refine pricedMargin_le _ _ _ hzR ?_ ?_
      · unfold mgfRows castTilts; simp
      · intro i hi hi'
        unfold mgfRows castTilts at hi ⊢
        simp only [List.getElem_map]
        set x := P.tilts[i]'(by simpa using hi) with hx
        have hxm : x ∈ P.tilts := List.getElem_mem _
        obtain ⟨-, -, hl⟩ := htilts x hxm
        have hlR : (0 : ℝ) ≤ ((x.2 : ℚ) : ℝ) := by exact_mod_cast hl
        show Real.exp (-(((x.2 : ℚ) : ℝ) * m)) ≤ ((expNegUp (x.2 * b.ml) : ℚ) : ℝ)
        have hml : (0 : ℝ) ≤ b.ml := by exact_mod_cast hml0.le
        have hexp : Real.exp (-(((x.2 : ℚ) : ℝ) * m)) ≤ Real.exp (-(((x.2 * b.ml : ℚ) : ℝ))) := by
          apply Real.exp_le_exp.mpr
          push_cast
          nlinarith
        exact hexp.trans (exp_neg_le_expNegUp (mul_nonneg hl hml0.le))
    -- the moments
    have hdl : (b.ml : ℝ) - m0 ≤ d := by rw [hd]; linarith
    have hdh : d ≤ (b.mh : ℝ) - m0 := by rw [hd]; linarith
    have hlin : min ((b.beta : ℝ) * ((b.ml : ℝ) - m0)) ((b.beta : ℝ) * ((b.mh : ℝ) - m0)) ≤ (b.beta : ℝ) * d := by
      rcases le_total 0 (b.beta : ℝ) with hb' | hb'
      · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hdl hb')
      · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hdh hb')
    have hsq : d ^ 2 ≤ max (((b.ml : ℝ) - m0) * ((b.ml : ℝ) - m0)) (((b.mh : ℝ) - m0) * ((b.mh : ℝ) - m0)) := by
      rcases le_total 0 d with hd0 | hd0
      · exact (by nlinarith : d ^ 2 ≤ ((b.mh : ℝ) - m0) * ((b.mh : ℝ) - m0)).trans (le_max_right _ _)
      · exact (by nlinarith : d ^ 2 ≤ ((b.ml : ℝ) - m0) * ((b.ml : ℝ) - m0)).trans (le_max_left _ _)
    have hDR : (0 : ℝ) ≤ P.D := by exact_mod_cast hD
    have hθR : (0 : ℝ) ≤ P.theta := by exact_mod_cast hθ
    have hv := MBox.vmax_ge (b := b) hq hq'
    have hq0 : 0 ≤ q * (1 - q) := by nlinarith
    have hvm : q * (1 - q) * m ≤ ((b.vmax : ℚ) : ℝ) * b.mh :=
      mul_le_mul hv hm' hmR.le (hq0.trans hv)
    have hnuθ : 0 ≤ (b.nu : ℝ) * (P.theta : ℝ) := mul_nonneg hnuR.le hθR
    have hγsq := mul_le_mul_of_nonneg_left hsq hgaR
    have key1 : (b.nu : ℝ) * (P.theta : ℝ) * (q * (1 - q)) * m ≤
        (b.nu : ℝ) * (P.theta : ℝ) * ((b.vmax : ℚ) : ℝ) * (b.mh : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hvm hnuθ
      calc (b.nu : ℝ) * (P.theta : ℝ) * (q * (1 - q)) * m
          = (b.nu : ℝ) * (P.theta : ℝ) * (q * (1 - q) * m) := by ring
        _ ≤ (b.nu : ℝ) * (P.theta : ℝ) * (((b.vmax : ℚ) : ℝ) * (b.mh : ℝ)) := h
        _ = (b.nu : ℝ) * (P.theta : ℝ) * ((b.vmax : ℚ) : ℝ) * (b.mh : ℝ) := by ring
    have hγD' : (b.gamma : ℝ) * ((P.D : ℝ) * m) ≤ (b.gamma : ℝ) * ((P.D : ℝ) * (b.mh : ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm' hDR) hgaR
    rw [mul_add] at hmarg
    have e1 : (b.gamma : ℝ) * (P.D : ℝ) * m = (b.gamma : ℝ) * ((P.D : ℝ) * m) := by ring
    rw [e1]
    linarith only [hmarg, hlin, hγsq, hγD', key1, hU]

/-! ## The cover -/

theorem chainOK2_sound {boxes : List MBox} {lo hi : ℚ} : ∀ (chain : List ℕ) (s target : ℚ),
    MGF.chainOK boxes lo hi s target chain = true → ∀ m : ℝ, (s : ℝ) ≤ m → m ≤ (target : ℝ) →
      ∃ b ∈ boxes, b.ql ≤ lo ∧ hi ≤ b.qh ∧ (b.ml : ℝ) ≤ m ∧ m ≤ (b.mh : ℝ) := by
  intro chain
  induction chain with
  | nil => intro s target h; simp [MGF.chainOK] at h
  | cons i rest ih =>
    intro s target h m hsm hmt
    unfold MGF.chainOK at h
    split at h
    · rename_i b hb
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨hql, hqh⟩, hml⟩, hrest⟩ := h
      have hbmem : b ∈ boxes := List.mem_of_getElem? hb
      have hml' : (b.ml : ℝ) ≤ s := by exact_mod_cast hml
      by_cases hmb : m ≤ (b.mh : ℝ)
      · exact ⟨b, hbmem, hql, hqh, hml'.trans hsm, hmb⟩
      · push_neg at hmb
        rcases hrest with htb | hr
        · have : (target : ℝ) ≤ b.mh := by exact_mod_cast htb
          linarith
        · exact ih b.mh target hr m hmb.le hmt
    · simp at h

theorem slabsOK2_sound {boxes : List MBox} {qhi mlo mhi : ℚ} : ∀ (slabs : List Slab) (start : ℚ),
    MGF.slabsOK boxes qhi mlo mhi start slabs = true → ∀ q : ℝ, (start : ℝ) ≤ q → q ≤ (qhi : ℝ) →
      ∀ m : ℝ, (mlo : ℝ) ≤ m → m ≤ (mhi : ℝ) →
        ∃ b ∈ boxes, (b.ql : ℝ) ≤ q ∧ q ≤ b.qh ∧ (b.ml : ℝ) ≤ m ∧ m ≤ b.mh := by
  intro slabs
  induction slabs with
  | nil => intro start h; simp [MGF.slabsOK] at h
  | cons sl rest ih =>
    intro start h q hsq hqq m hm hm'
    unfold MGF.slabsOK at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hlo, hch⟩, hrest⟩ := h
    have hlo' : (sl.lo : ℝ) ≤ start := by exact_mod_cast hlo
    by_cases hqs : q ≤ (sl.hi : ℝ)
    · obtain ⟨b, hb, hql, hqh, hbm, hbm'⟩ := chainOK2_sound sl.chain mlo mhi hch m hm hm'
      have hql' : (b.ql : ℝ) ≤ sl.lo := by exact_mod_cast hql
      have hqh' : (sl.hi : ℝ) ≤ b.qh := by exact_mod_cast hqh
      exact ⟨b, hb, by linarith, by linarith, hbm, hbm'⟩
    · push_neg at hqs
      rcases hrest with hqh | hr
      · have : (qhi : ℝ) ≤ sl.hi := by exact_mod_cast hqh
        linarith
      · exact ih sl.hi hr q hqs.le hqq m hm hm'

/-- **The cover**: a passing `coverOK` covers `[qlo, qhi] × [mlo, mhi]` by the boxes. -/
theorem coverOK2_sound {boxes : List MBox} {qlo qhi mlo mhi : ℚ} {slabs : List Slab}
    (h : MGF.coverOK boxes qlo qhi mlo mhi slabs = true) {q m : ℝ} (hq : (qlo : ℝ) ≤ q) (hq' : q ≤ qhi)
    (hm : (mlo : ℝ) ≤ m) (hm' : m ≤ mhi) :
    ∃ b ∈ boxes, (b.ql : ℝ) ≤ q ∧ q ≤ b.qh ∧ (b.ml : ℝ) ≤ m ∧ m ≤ b.mh :=
  slabsOK2_sound slabs qlo h q hq hq' m hm hm'

/-! ## One piece -/

/-- **A passing piece gives the criterion** at every `q ∈ [q(λ_lo), q(λ_hi)]` and `m ∈ [mlo, mhi]`, with `0 < q < 1`. -/
theorem pieceOK_sound {P : MPiece} {mlo mhi : ℚ} {boxes : List MBox} {slabs : List Slab}
    (hok : pieceOK P mlo mhi boxes slabs = true) {q m : ℝ}
    (hq : actQ (P.lamLo : ℝ) ≤ q) (hq' : q ≤ actQ (P.lamHi : ℝ)) (hm : (mlo : ℝ) ≤ m) (hm' : m ≤ mhi) :
    0 < q ∧ q < 1 ∧ ExplicitThresholdMGF2 q m (P.theta : ℝ) (P.D : ℝ) (mgfRows (castTilts P.tilts) q m) := by
  unfold pieceOK at hok
  simp only [Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨⟨hPs, hboxes⟩, hcov⟩ := hok
  obtain ⟨b, hb, hbq, hbq', hbm, hbm'⟩ :=
    coverOK2_sound (q := q) (m := m) hcov (by rw [actQQ_cast]; exact hq) (by rw [actQQ_cast]; exact hq')
      hm hm'
  have hbok := hboxes b hb
  have hs : MGF.sane b = true := by
    unfold MGF.boxOK at hbok
    simp only [Bool.and_eq_true] at hbok
    exact hbok.1.1.1
  unfold MGF.sane at hs
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, -⟩, h1⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hs
  have h0R : (0 : ℝ) < b.ql := by exact_mod_cast h0
  have h1R : (b.qh : ℝ) < 1 := by exact_mod_cast h1
  exact ⟨by linarith, by linarith, box_explicitThresholdMGF2 hPs hbok hbq hbq' hbm hbm'⟩

/-- **A passing piece gives the no-valley property in MGF form** at every `(q, m)` of its rectangle. -/
theorem pieceOK_noValley {P : MPiece} {mlo mhi : ℚ} {boxes : List MBox} {slabs : List Slab}
    (hok : pieceOK P mlo mhi boxes slabs = true) {q m : ℝ}
    (hq : actQ (P.lamLo : ℝ) ≤ q) (hq' : q ≤ actQ (P.lamHi : ℝ)) (hm : (mlo : ℝ) ≤ m) (hm' : m ≤ mhi) :
    NoValleyAtMGF2 q m (P.theta : ℝ) (P.D : ℝ) (mgfRows (castTilts P.tilts) q m) := by
  obtain ⟨hq0, hq1, h⟩ := pieceOK_sound hok hq hq' hm hm'
  exact noValleyAtMGF2_of_explicit hq0 hq1 h

end Erdos993Lean.Analytic.MGF
