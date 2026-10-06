import Erdos993Lean.Analytic.HandVariance.Defs
import Erdos993Lean.Analytic.Reserve.Cert.Real

/-!
# Normalized parent and child functions of the hand variance proof

Source: `for_tong/TWIN_v1.8/apx_hand.tex`, Section `hand:var:set`,
Definition `mc:def:curve` and equation `arc:eq:maj`, in
`ProofRuns/2026-09-28_analytic_large_n/LEAN`.
The identities below preserve the existing reserve comparisons and their
activity, parent log-mass and child log-mass. They assert no comparison sign.
-/

namespace Erdos993Lean.Analytic.HandVariance

open Real Reserve

/-- Source: Section `hand:var:set`; `e_λ = exp Y / λ`. -/
noncomputable def parentE (lam Y : ℝ) : ℝ := exp Y / lam

/-- Source: Section `hand:var:set`; `k = p / φ₀`. -/
noncomputable def parentK (lam Y : ℝ) : ℝ := msg lam Y / lmass lam Y

/-- Source: Section `hand:var:set`; `ϑ = k + p - 1`. -/
noncomputable def parentTheta (lam Y : ℝ) : ℝ := parentK lam Y + msg lam Y - 1

/-- Source: Section `hand:var:set`; actual child coordinate `r = T / φ`. -/
noncomputable def childR (lam T : ℝ) : ℝ := T / lmass lam T

/-- Source: Section `hand:var:set`; `ĥ = H/p`, reusing the exact reserve form. -/
noncomputable def hHat (c : Band) (lam Y : ℝ) : ℝ := Reserve.Cert.hF c lam Y

/-- Source: Section `hand:var:set`; `L̄ = γ e_λ - ĥ Y`. -/
noncomputable def lBar (c : Band) (lam Y : ℝ) : ℝ :=
  gamma c lam * parentE lam Y - hHat c lam Y * Y

/-- Source: Section `hand:var:set`; `Z̄ = γ + J L̄`. -/
noncomputable def zBar (c : Band) (lam Y J : ℝ) : ℝ :=
  gamma c lam + J * lBar c lam Y

/-- Source: Section `hand:var:set`; `N = A_D - ĥ - α/k`. -/
noncomputable def nTerm (c : Band) (lam Y : ℝ) : ℝ :=
  capA c lam - hHat c lam Y - alpha c lam / parentK lam Y

/-- Source: Section `hand:var:set`; normalized AC at a polygon point `(r,J)`. -/
noncomputable def vertexA (c : Band) (lam Y r J : ℝ) : ℝ :=
  alpha c lam * parentE lam Y + nTerm c lam Y / Y + alpha c lam * r -
    J * hHat c lam Y ^ 2 / zBar c lam Y J

/-- Source: Section `hand:var:set`; the expression replacing `Z̄` by `γ`. -/
noncomputable def vertexAgamma (c : Band) (lam Y r J : ℝ) : ℝ :=
  alpha c lam * parentE lam Y + nTerm c lam Y / Y + alpha c lam * r -
    J * hHat c lam Y ^ 2 / gamma c lam

/-- Source: Section `hand:var:set`; the exponential and message reciprocal
forms of `e_λ` agree at a positive activity. -/
theorem parentE_eq_inv {lam : ℝ} (hlam : 0 < lam) (Y : ℝ) :
    parentE lam Y = 1 / (lam * exp (-Y)) := by
  unfold parentE
  rw [Real.exp_neg]
  field_simp [hlam.ne', Real.exp_ne_zero]

/-- Source: Section `hand:var:set`; `(1-p)/p = e_λ`, in multiplicative form. -/
theorem msg_mul_parentE {lam : ℝ} (hlam : 0 < lam) (Y : ℝ) :
    msg lam Y * parentE lam Y = 1 - msg lam Y := by
  rw [parentE_eq_inv hlam]
  simpa only [div_eq_mul_inv, one_mul] using
    Reserve.Cert.msg_div_R lam Y hlam

/-- Source: Section `hand:var:set`; the parent coordinate `k` is positive. -/
theorem parentK_pos {lam : ℝ} (hlam : 0 < lam) (Y : ℝ) :
    0 < parentK lam Y :=
  div_pos (Reserve.Cert.msg_pos (X := Y) hlam) (Reserve.Cert.lmass_pos (X := Y) hlam)

/-- Source: Section `hand:var:set`; `L̄` is the existing normalized reserve
coefficient, with its exponential notation made explicit. -/
theorem lBar_eq_LpF (c : Band) {lam : ℝ} (hlam : 0 < lam) (Y : ℝ) :
    lBar c lam Y = Reserve.Cert.LpF c lam Y := by
  unfold lBar Reserve.Cert.LpF hHat
  rw [parentE_eq_inv hlam]
  ring

/-- Source: Section `hand:var:set`; at the actual child coordinate,
`Z̄` agrees with the existing normalized reserve coefficient. -/
theorem zBar_eq_ZbF (c : Band) {lam : ℝ} (hlam : 0 < lam) (T Y : ℝ) :
    zBar c lam Y (coefJ lam T) = Reserve.Cert.ZbF c lam T Y := by
  unfold zBar Reserve.Cert.ZbF
  rw [lBar_eq_LpF c hlam]

/-- Source: Section `hand:var:set`; `H = p ĥ`. -/
theorem coefH_eq_msg_hHat (c : Band) (lam Y : ℝ) :
    coefH c lam Y = msg lam Y * hHat c lam Y :=
  Reserve.Cert.coefH_eq c lam Y

/-- Source: Section `hand:var:set`; `L = p L̄`. -/
theorem coefL_eq_msg_lBar (c : Band) {lam : ℝ} (hlam : 0 < lam) (Y : ℝ) :
    coefL c lam Y = msg lam Y * lBar c lam Y := by
  rw [lBar_eq_LpF c hlam]
  exact Reserve.Cert.coefL_eq c lam Y hlam

/-- Source: Section `hand:var:set`; `Z = p Z̄`. -/
theorem coefZ_eq_msg_zBar (c : Band) {lam : ℝ} (hlam : 0 < lam) (T Y : ℝ) :
    coefZ c lam T Y = msg lam Y * zBar c lam Y (coefJ lam T) := by
  rw [zBar_eq_ZbF c hlam]
  exact Reserve.Cert.coefZ_eq c lam T Y hlam

/-- Source: Section `hand:var:set`; the exact parent/child entropy
normalization. The positive parent mass is retained as an explicit hypothesis. -/
theorem coefE_eq_msg_normalized {lam : ℝ} (hlam : 0 < lam) (T : ℝ)
    {Y : ℝ} (hY : 0 < Y) :
    coefE lam T Y = msg lam Y *
      (parentE lam Y + childR lam T - 1 / (parentK lam Y * Y)) := by
  have hp : msg lam Y ≠ 0 := (Reserve.Cert.msg_pos (X := Y) hlam).ne'
  have hy : lmass lam Y ≠ 0 := (Reserve.Cert.lmass_pos (X := Y) hlam).ne'
  have hcancel : lmass lam Y / Y =
      msg lam Y * (1 / (parentK lam Y * Y)) := by
    unfold parentK
    field_simp [hp, hy, hY.ne']
  rw [Reserve.Cert.coefE_eq, ← msg_mul_parentE hlam Y, hcancel]
  unfold childR
  ring

/-- Source: Section `hand:var:set`; `E/p = e_λ+r-1/(kY)`. -/
theorem coefE_div_msg {lam : ℝ} (hlam : 0 < lam) (T : ℝ)
    {Y : ℝ} (hY : 0 < Y) :
    coefE lam T Y / msg lam Y =
      parentE lam Y + childR lam T - 1 / (parentK lam Y * Y) := by
  rw [coefE_eq_msg_normalized hlam T hY]
  exact mul_div_cancel_left₀ _ (Reserve.Cert.msg_pos (X := Y) hlam).ne'

/-- Source: Section `hand:var:set`; the normalized AC comparison equals
`A` evaluated at the actual child point. -/
theorem compB_div_msg (c : Band) {lam : ℝ} (hlam : 0 < lam) (T : ℝ)
    {Y : ℝ} (hY : 0 < Y)
    (hZ : zBar c lam Y (coefJ lam T) ≠ 0) :
    compB c lam T Y / msg lam Y =
      vertexA c lam Y (childR lam T) (coefJ lam T) := by
  have hp : msg lam Y ≠ 0 := (Reserve.Cert.msg_pos (X := Y) hlam).ne'
  have hk : parentK lam Y ≠ 0 := (parentK_pos hlam Y).ne'
  unfold compB
  rw [coefE_eq_msg_normalized hlam T hY, coefH_eq_msg_hHat,
    coefZ_eq_msg_zBar c hlam]
  unfold vertexA nTerm
  field_simp [hp, hk, hY.ne', hZ]
  ring

/-- Source: Section `hand:var:set`; the normalized CA comparison retains
the actual child message and mass. -/
theorem compC_div_msg (c : Band) {lam : ℝ} (hlam : 0 < lam) (T : ℝ)
    {Y : ℝ} (hY : 0 < Y)
    (hZ : zBar c lam Y (coefJ lam T) ≠ 0) :
    compC c lam T Y / msg lam Y =
      alpha c lam * (parentE lam Y + childR lam T - 1 / (parentK lam Y * Y)) +
        gamma c lam * lBar c lam Y * (msg lam T / lmass lam T) ^ 2 /
          zBar c lam Y (coefJ lam T) := by
  have hp : msg lam Y ≠ 0 := (Reserve.Cert.msg_pos (X := Y) hlam).ne'
  unfold compC
  rw [coefE_eq_msg_normalized hlam T hY, coefL_eq_msg_lBar c hlam,
    coefZ_eq_msg_zBar c hlam]
  field_simp [hp, hZ]

/-- Source: equation `arc:eq:maj`; exact difference between the rational
vertex expression and its denominator-γ expression. -/
theorem vertexA_sub_vertexAgamma (c : Band) (lam Y r J : ℝ)
    (hγ : gamma c lam ≠ 0) (hZ : zBar c lam Y J ≠ 0) :
    vertexA c lam Y r J - vertexAgamma c lam Y r J =
      hHat c lam Y ^ 2 * lBar c lam Y * J ^ 2 /
        (gamma c lam * zBar c lam Y J) := by
  have hden : gamma c lam + J * lBar c lam Y ≠ 0 := hZ
  unfold vertexA vertexAgamma zBar
  field_simp [hγ, hden]
  ring

end Erdos993Lean.Analytic.HandVariance
