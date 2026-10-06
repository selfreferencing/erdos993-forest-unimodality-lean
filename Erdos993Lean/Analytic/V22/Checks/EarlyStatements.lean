import Erdos993Lean.Analytic.V22.Defs

/-! Real-arithmetic statements of repaired note Lemmas 7.1–7.14.
These are propositions, not certificates or claims that the checks passed. -/

namespace Erdos993Lean.Analytic.V22.Checks

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Exact closed cell, including both nominal rational endpoints. -/
def inCell (lo hi x : ℝ) : Prop := lo ≤ x ∧ x ≤ hi

/-- Lemma 7.1 (A0): the endpoint values and the uniform concavity consequence. -/
def lemma_7_1 : Prop :=
  phi 0 = 22 / 25 ∧ 798 / 1000 ≤ phi (67 / 100) ∧
  ∀ s : ℝ, inCell 0 (67 / 100) s → 798 / 1000 ≤ phi s

/-- Lemma 7.2 (A1), using the polynomial extension at zero. -/
def lemma_7_2 : Prop := ∀ a : ℝ, inCell 0 (66 / 125) a → 53 / 10000 ≤ Q a

/-- The nine exact `s` cells of Lemma 7.3. -/
def envelopeCells : List (ℚ × ℚ) :=
  [(-66/125,-373/1000),(-373/1000,-13/125),(-13/125,0),
   (0,31/200),(31/200,47/200),(47/200,317/1000),
   (317/1000,53/125),(53/125,117/200),(117/200,67/100)]

/-- The envelope expression in the proof of Theorem 4.15 (`thm:env`), with the
upper-range remainder omitted precisely when `s≥0`. -/
def envelopeExpression (s M0 k : ℝ) : ℝ :=
  let N0 := M0 + 2
  let nm := (1/4) * Real.sqrt N0
  let t := tOfS s
  (if 0 ≤ s then M0 * s^2 * phi s else 0) + 2 - 6*s^2/(1+s)
    - 2*k*s/(1+s) - k^2/((1+s)*(2+s)*(M0+3))
    - max (dLbar t N0 M0 (1/4) nm)
      (if s < 0 then dUbar t N0 M0 (1/4) nm else 0)

/-- Lemma 7.3 (A2): denominator hypotheses and both endpoint envelope
inequalities on all nine closed cells. -/
def lemma_7_3 : Prop := ∀ c ∈ envelopeCells, ∀ s : ℝ, inCell c.1 c.2 s →
  let M0 := 19 * tOfS c.1
  let N0 := M0 + 2
  let nm := (1/4) * Real.sqrt N0
  let t := tOfS s
  0 < betaL t N0 M0 (1/4) nm ∧ ebar N0 (1/4) nm < 1 ∧
  (s < 0 → 0 < rhoStar N0 (1/4) ∧ 0 < betaE N0 (1/4) nm ∧
    0 < N0-1-kappaA N0 (1/4)*Ghat t M0/rhoStar N0 (1/4)) ∧
  Ghat t M0 ≤ max (G (lambdaT t)) (positivePart (lambdaT t + hbar M0)^2/4) ∧
  sigma0 t M0 ≤ positivePart (s + hbar M0) ∧
  ∀ k ∈ ([71/20, kbar M0] : List ℝ), 0 ≤ envelopeExpression s M0 k

/-- The explicit termwise derivative bound of Lemmas 7.4–7.7. -/
def e2DerivativeBound (rm Nlo : ℝ) : ℝ :=
  e3 rm*rm/(2*Real.sqrt Nlo) + e4 Nlo rm*rm^2
    + (3/2)*e5 rm*rm^3*Real.sqrt ((6/rm)^2)

def betaDerivativeBound (rm Nlo : ℝ) : ℝ := 1 - 2/rhoStar Nlo rm*e2DerivativeBound rm Nlo

/-- The capped denominator used by the note. -/
def cappedBeta (rm N : ℝ) : ℝ := betaE N rm (min 6 (rm*Real.sqrt N))

/-- Within-regime derivative: at the cap this is the pre-cap derivative
on the closed interval, where the paper specifies `ν_m=r_m√N`. -/
def betaDerivativeOn (rm Nlo N : ℝ) : ℝ :=
  derivWithin (cappedBeta rm) (Set.Icc Nlo ((6/rm)^2)) N

/-- Lemma 7.4 (A3): numerical bound and the derivative inequality over
the entire pre-cap regime, together with the stated termwise tail. -/
def lemma_7_4 : Prop :=
  744/1000 ≤ betaDerivativeBound (1/4) (67/5) ∧
  (∀ N : ℝ, inCell (67/5) 576 N →
    betaDerivativeBound (1/4) (67/5) ≤ betaDerivativeOn (1/4) (67/5) N) ∧
  MonotoneOn (cappedBeta (1/4)) (Set.Ici 576)

/-- A3′ retains the derivative comparison and its all-`N` monotonic
consumer; no rounded first-cell starting point is substituted. -/
def betaRange (rm Nlo : ℝ) : Prop :=
  MonotoneOn (cappedBeta rm) (Set.Ici Nlo) ∧
  (Nlo < (6/rm)^2 → 0 < betaDerivativeBound rm Nlo ∧
    ∀ N : ℝ, inCell Nlo ((6/rm)^2) N → betaDerivativeBound rm Nlo ≤ betaDerivativeOn rm Nlo N)

/-- Lemma 7.5 (A3′): three wings, two exact envelope starts, and each
last outer spike block, including the already-capped C1 regime. -/
def lemma_7_5 : Prop :=
  betaRange (741/10000) (651/50) ∧ betaRange (139/1250) 13 ∧
  betaRange (1667/10000) (388/25) ∧
  betaRange (1/4) (19*tOfS (-66/125)+2) ∧
  betaRange (7/25) (30*tOfS (-66/125)+2) ∧
  ∀ c ∈ spikeCells, c.classId ≠ 0 →
    betaRange (spikeRm c) (16*(c.ma : ℚ)+2) ∧
    (c.classId = 1 → (6/spikeRm c)^2+46/5 ≤ 16*(c.ma : ℚ)+2)

/-- The fixed-coefficient tail polynomial in the proof of Lemma 4.13. -/
def bonusTail (rm N : ℝ) : ℝ :=
  let Nc := (6/rm)^2
  N*(N-1)*rhoStar Nc rm/2 - N*E2 Nc rm 6 - (N+1)/(71/20)

/-- All three A4 conditions, with the derivative on its closed pre-cap
regime and the fixed-coefficient quadratic tail kept explicitly. -/
def bonusConditions (rm Nlo : ℝ) : Prop :=
  0 < lambdaBonusF Nlo rm ∧
  0 < rhoStar Nlo rm/2-e2DerivativeBound rm Nlo ∧
  (∀ N : ℝ, inCell Nlo ((6/rm)^2) N →
    rhoStar Nlo rm/2-e2DerivativeBound rm Nlo ≤
      derivWithin (fun n => lambdaBonusF n rm) (Set.Icc Nlo ((6/rm)^2)) N) ∧
  0 < bonusTail rm ((6/rm)^2) ∧ 0 < deriv (bonusTail rm) ((6/rm)^2) ∧
  (∀ N : ℝ, (6/rm)^2 ≤ N → 0 < bonusTail rm N) ∧
  MonotoneOn (bonusTail rm) (Set.Ici ((6/rm)^2))

/-- Lemma 7.6 (A4): the three conditions at `r_m=1/4,N_min=13.4`. -/
def lemma_7_6 : Prop := bonusConditions (1/4) (67/5)

/-- The six exact pairs of Lemma 7.7. -/
def bonusPairs : List (ℚ × ℚ) :=
  [(1/4,10),(7/25,10),(194/625,10),(861/2500,10),(3847/10000,12),(2/5,12)]

/-- Lemma 7.7 (A4′): the same three conditions at each listed pair. -/
def lemma_7_7 : Prop := ∀ p ∈ bonusPairs, bonusConditions p.1 p.2

/-- Exact subdivisions inside the seven A4d log groups. -/
def phiRBlocks : List (ℚ × ℚ × ℚ × ℚ) :=
  ([3793/10000,2/5,21/50,11/25,23/50,12/25] : List ℚ).zip
    [2/5,21/50,11/25,23/50,12/25,1/2] |>.flatMap fun r =>
      (([229/20,25/2,14,16,18] : List ℚ).zip [25/2,14,16,18,20]).map
        (fun n => (r.1,r.2,n.1,n.2))

def phiRTailBlocks : List (ℚ × ℚ × ℚ × ℚ) :=
  [(3793/10000,1/2,20,23),(3793/10000,1/2,23,26),(3793/10000,1/2,26,291/10)]

/-- Lemma 7.8 (A4d): each worst-end block lower bound is nonnegative. -/
def lemma_7_8 : Prop := ∀ c ∈ phiRBlocks ++ phiRTailBlocks,
  0 ≤ phiRBlockLower c.1 c.2.1 c.2.2.1 c.2.2.2

/-- Lemma 7.9 (A4m), retaining every actual `r` in its range. -/
def lemma_7_9 : Prop := ∀ r : ℝ, inCell (3793/10000) (1/2) r → 58/1000 ≤ windowH r (229/20)

def largeTConstant (N : ℝ) : ℝ :=
  2*Real.exp (-(1/2 : ℝ))*Real.rpow (8/5 : ℝ) (-(3/2 : ℝ))
    *Real.exp (3/(4*N)+(11/10)/N^2)

/-- The three inequalities, with the split at the exact radical. -/
def largeTConditions (rm Nstar : ℝ) : Prop :=
  (∀ nu : ℝ, inCell 0 (rm*Real.sqrt Nstar) nu → Xbar nu Nstar rm ≤ Real.log ((257/100)*rhoStar Nstar rm)) ∧
  (∀ nu : ℝ, inCell (rm*Real.sqrt Nstar) 6 nu →
    Xbar nu (nu^2/rm^2) rm ≤ Real.log ((257/100)*rhoStar (nu^2/rm^2) rm)) ∧
  ∀ N : ℝ, Nstar ≤ N → largeTConstant N ≤ 249/400

/-- Lemma 7.10 (A5), exact `N*=32.4` and radical split. -/
def lemma_7_10 : Prop := largeTConditions (1/4) (162/5)

/-- Lemma 7.11 (D4), exact `N*=66` and split `√66/2`. -/
def lemma_7_11 : Prop := largeTConditions (1/2) 66

/-- Lemma 7.12 (B1): all eight fibers, all listed atoms, all activities;
the vanishing kernel outside that atom range is also retained. -/
def lemma_7_12 : Prop := ∀ M : ℕ, M ≤ 7 → ∀ j : ℤ, ∀ q : ℝ, inCell (1/4) (3/4) q →
  (-1 ≤ j ∧ j ≤ (M : ℤ)+1 →
    (smallMargins.getD M 0 : ℚ) ≤ Erdos993Lean.Analytic.kernel2 q (weightL q) (weightR q) M j + (smallK.getD M 0 : ℚ)) ∧
  (j < -1 ∨ (M : ℤ)+1 < j → Erdos993Lean.Analytic.kernel2 q (weightL q) (weightR q) M j = 0)

def spikeLowerSlack (rm t N : ℝ) : ℝ :=
  let nm := rm*Real.sqrt N
  (9/2)*(1-t)^2-2*t*(alpha1 N rm*nm+alpha2 N rm*nm^2)/(N-2)

/-- Lemma 7.13 (B2): central entry and every outer spike cell, with
the stated monotonicity of the subtracted term. -/
def lemma_7_13 : Prop :=
  0 < spikeLowerSlack (1/4) (3/5) 10 ∧
  (∀ c ∈ spikeCells, c.classId ≠ 0 →
    0 < spikeLowerSlack (spikeRm c) c.hi (max 10 (spikeMean c*c.lo+2))) ∧
  (∀ rm : ℝ, inCell 0 (1/2) rm → ∀ N : ℝ, 10 ≤ N →
    MonotoneOn (fun t => (9/2)*(1-t)^2-spikeLowerSlack rm t N) (Set.Ici 0)) ∧
  (∀ rm : ℝ, inCell 0 (1/2) rm → ∀ t : ℝ, 0 ≤ t →
    AntitoneOn (fun N => (9/2)*(1-t)^2-spikeLowerSlack rm t N) (Set.Ici 10))

/-- Lemma 7.14(a) (B3): each displayed Table 4 value bounds `Φ` on
every unmarked cell and every point of its corresponding `M` block. -/
def spikePhi (c : V22SpikeCell) (i : Nat) (t M : ℝ) : ℝ :=
  let M1 := (blockMultipliers.getD i 0 : ℝ)*(c.ma : ℝ)
  if i = 4 then phiInfiniteBlock t M M1 (spikeRm c)
  else phiBlock t M M1 (2*M1) (spikeRm c)

/-- Validity conditions of the exact block coefficients from Lemma 5.4,
retained alongside the numerical bound, rather than assumed by its evaluator. -/
def spikePhiCoefficientsValid (c : V22SpikeCell) (i : Nat) (t : ℝ) : Prop :=
  let M1 := (blockMultipliers.getD i 0 : ℝ)*(c.ma : ℝ)
  if i = 4 then phiInfiniteBlockCoefficientsValid t M1 (spikeRm c)
  else phiBlockCoefficientsValid M1 (2*M1) (spikeRm c)

/-- Lemma 7.14(a), instantiated with the source's refined block forms. -/
def lemma_7_14_nonwindow : Prop := ∀ c ∈ spikeCells, c.window = false →
  ∀ i : ℕ, i < 5 → ∀ t M : ℝ, inCell c.lo c.hi t → inSpikeBlock c i M →
    spikePhiCoefficientsValid c i t ∧ spikePhi c i t M ≤ (c.bounds.getD i 0 : ℚ)

/-- Lemma 7.14(b) (B3), repaired: window cells bound the minimum,
retaining the class, integer fiber, and starting-mean hypotheses. -/
def lemma_7_14_window : Prop := ∀ c ∈ spikeCells, c.window = true →
  ∀ k ∈ classes, k.classId = c.classId → ∀ i : ℕ, i < 5 →
  ∀ (t q : ℝ) (M : ℕ), inCell c.lo c.hi t → inCell k.ra k.rb |2*q-1| →
    inCell (1/4) (3/4) q → inSpikeBlock c i M → (k.muD : ℚ) ≤ (M : ℝ)/t →
    spikePhiCoefficientsValid c i t ∧
    min (spikePhi c i t M) (deficitG q ((M : ℝ)/t) k.b k.beta M) ≤ (c.bounds.getD i 0 : ℚ)

/-- Lemma 7.14's certified six-digit upward exports used by Lemma 7.21.
These retain the same real objects and domains as the displayed bounds;
the rounded Table 4 values are checked separately as larger exports. -/
def lemma_7_14_certified : Prop :=
  (∀ c ∈ spikeCells, c.window = false → ∀ i : ℕ, i < 5 →
    ∀ t M : ℝ, inCell c.lo c.hi t → inSpikeBlock c i M →
      spikePhiCoefficientsValid c i t ∧ spikePhi c i t M ≤ (c.logBounds.getD i 0 : ℚ)) ∧
  (∀ c ∈ spikeCells, c.window = true → ∀ k ∈ classes, k.classId = c.classId →
    ∀ i : ℕ, i < 5 → ∀ (t q : ℝ) (M : ℕ), inCell c.lo c.hi t →
      inCell k.ra k.rb |2*q-1| → inCell (1/4) (3/4) q → inSpikeBlock c i M →
      (k.muD : ℚ) ≤ (M : ℝ)/t → spikePhiCoefficientsValid c i t ∧
      min (spikePhi c i t M) (deficitG q ((M : ℝ)/t) k.b k.beta M) ≤ (c.logBounds.getD i 0 : ℚ)) ∧
  ∀ c ∈ spikeCells, ∀ i : ℕ, i < 5 → c.logBounds.getD i 0 ≤ c.bounds.getD i 0

/-- Lemma 7.14: both bound forms, and the shape and derivative
conditions that license every marked window cell. -/
def lemma_7_14 : Prop := lemma_7_14_nonwindow ∧ lemma_7_14_window ∧
  ∀ c ∈ spikeCells, c.window = true → ∀ k ∈ classes, k.classId = c.classId →
  ∀ r : ℝ, inCell k.ra k.rb r →
    windowConditions r ((k.muD : ℚ)*c.lo+2) ∧ 0 < uMonoDerivative r ((k.muD : ℚ)*c.lo+2)

end
end Erdos993Lean.Analytic.V22.Checks
