import Erdos993Lean.Analytic.V22.Checks.LateStatements

/-!
# The all-N wing minimum argument

The point of this module is the half-line statement, not an endpoint-only
substitute. It proves the two closed-form certificates used by `wing_cell`:
the starting value under a nonnegative starting slope, and the minimum of a
quadratic obtained from a retained square-root tangent at N1>0.
-/

namespace Erdos993Lean.Analytic.V22.WingQuadratic

noncomputable section

def quadratic (a b c d N : ℝ) : ℝ := a*N^2 + b*N - c*Real.sqrt N + d
def startingSlope (a b c N0 : ℝ) : ℝ := 2*a*N0 + b - c/(2*Real.sqrt N0)
def tangentBound (a b c d N1 : ℝ) : ℝ :=
  d - c*Real.sqrt N1/2 - (b-c/(2*Real.sqrt N1))^2/(4*a)

/-- The exact tangent bound used by the source, at any retained N1>0. -/
theorem sqrt_tangent {N N1 : ℝ} (hN : 0 ≤ N) (hN1 : 0 < N1) :
    Real.sqrt N ≤ Real.sqrt N1/2 + N/(2*Real.sqrt N1) := by
  have hs : 0 < Real.sqrt N1 := Real.sqrt_pos.2 hN1
  have hsq := Real.sq_sqrt hN
  have hsq1 := Real.sq_sqrt hN1.le
  have hm : 2*Real.sqrt N1*Real.sqrt N ≤ N1+N := by
    nlinarith [sq_nonneg (Real.sqrt N - Real.sqrt N1)]
  have heq : Real.sqrt N1/2 + N/(2*Real.sqrt N1) = (N1+N)/(2*Real.sqrt N1) := by
    field_simp [hs.ne']
    nlinarith
  rw [heq]
  apply (le_div_iff₀ (by positivity : 0 < 2*Real.sqrt N1)).mpr
  nlinarith

theorem tangent_quadratic_le {a b c d N N1 : ℝ}
    (hc : 0 ≤ c) (hN : 0 ≤ N) (hN1 : 0 < N1) :
    a*N^2 + (b-c/(2*Real.sqrt N1))*N + (d-c*Real.sqrt N1/2) ≤
      quadratic a b c d N := by
  have ht := mul_le_mul_of_nonneg_left (sqrt_tangent hN hN1) hc
  have heq : a*N^2 + (b-c/(2*Real.sqrt N1))*N + (d-c*Real.sqrt N1/2) =
      a*N^2 + b*N - c*(Real.sqrt N1/2 + N/(2*Real.sqrt N1)) + d := by ring
  rw [heq]
  unfold quadratic
  linarith

/-- A nonnegative starting slope licenses the actual half-line minimum. -/
theorem endpoint_minimum {a b c d N0 N : ℝ}
    (ha : 0 < a) (hc : 0 ≤ c) (hN0 : 0 < N0) (hN : N0 ≤ N)
    (hslope : 0 ≤ startingSlope a b c N0) :
    quadratic a b c d N0 ≤ quadratic a b c d N := by
  have hs : 0 < Real.sqrt N0 := Real.sqrt_pos.2 hN0
  have hsquare := Real.sq_sqrt hN0.le
  have hz : c/(2*Real.sqrt N0)*N0 = c*Real.sqrt N0/2 := by
    calc
      c/(2*Real.sqrt N0)*N0 = c/(2*Real.sqrt N0)*(Real.sqrt N0)^2 := by rw [hsquare]
      _ = c*Real.sqrt N0/2 := by field_simp [hs.ne'] <;> ring
  have hstart : a*N0^2 + (b-c/(2*Real.sqrt N0))*N0 + (d-c*Real.sqrt N0/2) =
      quadratic a b c d N0 := by
    unfold quadratic
    nlinarith [hz]
  have hdiff : 0 ≤ a*(N-N0)^2 + startingSlope a b c N0*(N-N0) :=
    add_nonneg (mul_nonneg ha.le (sq_nonneg _)) (mul_nonneg hslope (sub_nonneg.mpr hN))
  have hpoly : a*N0^2 + (b-c/(2*Real.sqrt N0))*N0 + (d-c*Real.sqrt N0/2) ≤
      a*N^2 + (b-c/(2*Real.sqrt N0))*N + (d-c*Real.sqrt N0/2) := by
    unfold startingSlope at hdiff
    nlinarith [hdiff]
  rw [← hstart]
  exact hpoly.trans (tangent_quadratic_le hc (hN0.le.trans hN) hN0)

/-- The global quadratic minimum after the square-root tangent. This
bound is valid independently of the sign of the starting slope. -/
theorem tangent_lower_bound {a b c d N N1 : ℝ}
    (ha : 0 < a) (hc : 0 ≤ c) (hN : 0 ≤ N) (hN1 : 0 < N1) :
    tangentBound a b c d N1 ≤ quadratic a b c d N := by
  have hs : 0 < Real.sqrt N1 := Real.sqrt_pos.2 hN1
  have hsq : 0 ≤ a*(N+(b-c/(2*Real.sqrt N1))/(2*a))^2 :=
    mul_nonneg ha.le (sq_nonneg _)
  have heq : a*N^2 + (b-c/(2*Real.sqrt N1))*N + (d-c*Real.sqrt N1/2)
      - tangentBound a b c d N1 = a*(N+(b-c/(2*Real.sqrt N1))/(2*a))^2 := by
    unfold tangentBound
    field_simp [ha.ne', hs.ne']
    ring
  have hp : tangentBound a b c d N1 ≤
      a*N^2 + (b-c/(2*Real.sqrt N1))*N + (d-c*Real.sqrt N1/2) := by
    linarith [heq, hsq]
  exact hp.trans (tangent_quadratic_le hc hN hN1)

/-- The source's endpoint-or-tangent certificate proves every N≥N0. -/
theorem nonnegative_allN {a b c d N0 : ℝ}
    (ha : 0 < a) (hc : 0 ≤ c) (hN0 : 0 < N0)
    (hcert : (0 ≤ startingSlope a b c N0 ∧ 0 ≤ quadratic a b c d N0) ∨
      ∃ N1 : ℝ, 0 < N1 ∧ 0 ≤ tangentBound a b c d N1) :
    ∀ N : ℝ, N0 ≤ N → 0 ≤ quadratic a b c d N := by
  intro N hN
  rcases hcert with hstart | ⟨N1, hN1, ht⟩
  · exact hstart.2.trans (endpoint_minimum ha hc hN0 hN hstart.1)
  · exact ht.trans (tangent_lower_bound ha hc (hN0.le.trans hN) hN1)

def wingA (c : V22WingClass) : ℝ := (c.ra : ℝ)^2/(1-(c.ra : ℝ)^2)
def wingB (c : V22WingClass) (cell : V22Cell) (t : ℝ) : ℝ :=
  gaussianSlack t - wingA c - Checks.wingKPrime c cell t*(c.ra : ℝ)^2
def wingSlope (c : V22WingClass) (cell : V22Cell) (t : ℝ) : ℝ :=
  Checks.wingBPrime c cell t*(c.ra : ℝ)
def wingD (c : V22WingClass) (cell : V22Cell) (t : ℝ) : ℝ :=
  Checks.wingTau1 c cell t - 2*gaussianSlack t - |G1 (lambdaT t)| * Checks.wingDe c cell

/-- Exact polynomial decomposition with the original cell start frozen. -/
theorem wingW_eq_quadratic (c : V22WingClass) (cell : V22Cell) (t N : ℝ) :
    Checks.wingW c cell t N = quadratic (wingA c) (wingB c cell t)
      (wingSlope c cell t) (wingD c cell t) N := by
  unfold Checks.wingW Checks.wingC quadratic wingA wingB wingSlope wingD
  dsimp [wingA]
  ring

/-- This consumer retains all four source hypotheses and the exact all-N
conclusion; the additional algebraic conditions license the minimum proof. -/
theorem wing_conditions_and_allN (c : V22WingClass) (cell : V22Cell) (t : ℝ)
    (hc0 : 0 < Checks.wingC c cell t (Checks.wingN0 c cell))
    (hnu : Checks.wingBPrime c cell t/(2*Checks.wingC c cell t (Checks.wingN0 c cell)) ≤
      (c.ra : ℝ)*Real.sqrt (Checks.wingN0 c cell))
    (hrs : 0 < rhoStar (Checks.wingN0 c cell) c.rb)
    (hbe : 0 < betaE (Checks.wingN0 c cell) c.rb (Checks.wingNuMax c cell))
    (ha : 0 < wingA c) (hcs : 0 ≤ wingSlope c cell t) (hN0 : 0 < Checks.wingN0 c cell)
    (hcert : (0 ≤ startingSlope (wingA c) (wingB c cell t) (wingSlope c cell t) (Checks.wingN0 c cell) ∧
      0 ≤ quadratic (wingA c) (wingB c cell t) (wingSlope c cell t) (wingD c cell t) (Checks.wingN0 c cell)) ∨
      ∃ N1 : ℝ, 0 < N1 ∧ 0 ≤ tangentBound (wingA c) (wingB c cell t) (wingSlope c cell t) (wingD c cell t) N1) :
    0 < Checks.wingC c cell t (Checks.wingN0 c cell) ∧
    Checks.wingBPrime c cell t/(2*Checks.wingC c cell t (Checks.wingN0 c cell)) ≤
      (c.ra : ℝ)*Real.sqrt (Checks.wingN0 c cell) ∧
    0 < rhoStar (Checks.wingN0 c cell) c.rb ∧
    0 < betaE (Checks.wingN0 c cell) c.rb (Checks.wingNuMax c cell) ∧
    ∀ N : ℝ, Checks.wingN0 c cell ≤ N → 0 ≤ Checks.wingW c cell t N := by
  refine ⟨hc0, hnu, hrs, hbe, ?_⟩
  intro N hN
  rw [wingW_eq_quadratic]
  exact nonnegative_allN ha hcs hN0 hcert N hN

end

end Erdos993Lean.Analytic.V22.WingQuadratic
