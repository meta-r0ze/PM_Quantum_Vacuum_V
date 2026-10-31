import PMDynamics.PMNS
import PMDecay.MuonRate

/-! Inclusive widths for unresolved, orthogonal neutrino mass channels.
The exclusive width is assumed to factor into two mixing probabilities times
its kinematic width. Equal kinematics (in particular the massless limit) makes
unitary mixing cancel. This is an incoherent inclusive sum, not an oscillation
amplitude and not a derivation of the decay vertex or the Born rule. -/
noncomputable section
namespace PMDecay.InclusiveMixing
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Each complete row of a unitary mixing matrix has total weight one. -/
theorem row_normalized (U : Matrix n n ℂ) (hU : U * Uᴴ = 1) (a : n) :
    ∑ i, Complex.normSq (U a i) = 1 := by
  have h := congrArg (fun M : Matrix n n ℂ => (M a a).re) hU
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.mul_conj] using h

def weight (U : Matrix n n ℂ) (a b i j : n) : ℝ :=
  Complex.normSq (U a i) * Complex.normSq (U b j)

omit [Fintype n] [DecidableEq n] in
theorem weight_nonnegative (U : Matrix n n ℂ) (a b i j : n) :
    0 ≤ weight U a b i j := mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

omit [Fintype n] [DecidableEq n] in
/-- Actual exclusive amplitudes with the usual two current coefficients give
exactly these weights when squared; conjugating either coefficient is harmless. -/
theorem amplitude_weight (U : Matrix n n ℂ) (a b i j : n) (amplitude : ℂ) :
    Complex.normSq (U a i * star (U b j) * amplitude) =
      weight U a b i j * Complex.normSq amplitude := by
  simp [weight, Complex.normSq_mul]

theorem weights_normalized (U : Matrix n n ℂ) (hU : U * Uᴴ = 1) (a b : n) :
    ∑ i, ∑ j, weight U a b i j = 1 := by
  simp only [weight, ← Finset.mul_sum, row_normalized U hU b, mul_one,
    row_normalized U hU a]

/-- This definition states the exclusive-channel factorization contract. -/
def inclusive (U : Matrix n n ℂ) (a b : n) (kinematic : n → n → ℝ) : ℝ :=
  ∑ i, ∑ j, weight U a b i j * kinematic i j

/-- No angle or CP phase survives the complete equal-kinematics sum. -/
theorem equal_kinematics (U : Matrix n n ℂ) (hU : U * Uᴴ = 1) (a b : n) (width : ℝ) :
    inclusive U a b (fun _ _ => width) = width := by
  simp only [inclusive, ← Finset.sum_mul, weights_normalized U hU, one_mul]

/-- With channel-dependent thresholds, unitarity gives bounds, not cancellation. -/
theorem kinematic_bounds (U : Matrix n n ℂ) (hU : U * Uᴴ = 1) (a b : n)
    (f : n → n → ℝ) (lo hi : ℝ) (hf : ∀ i j, lo ≤ f i j ∧ f i j ≤ hi) :
    lo ≤ inclusive U a b f ∧ inclusive U a b f ≤ hi := by
  have hl : inclusive U a b (fun _ _ => lo) ≤ inclusive U a b f := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (hf i j).1 (weight_nonnegative U a b i j)
  have hh : inclusive U a b f ≤ inclusive U a b (fun _ _ => hi) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (hf i j).2 (weight_nonnegative U a b i j)
  simpa only [equal_kinematics U hU] using And.intro hl hh

/-- Apply Paper IV's complete proposed PMNS matrix to Paper V's width.
The result uses unitarity only; the numerical angle formulas play no role. -/
theorem pmns_muon_width (G m : ℝ) (electron muon : Fin 3) :
    inclusive PMDynamics.PMNS.matrix electron muon
      (fun _ _ => G ^ 2 * m ^ 5 / (192 * Real.pi ^ 3)) =
      ∫ E in (0 : ℝ)..m/2, MuonRate.rate G m E := by
  rw [MuonRate.muon_rate]
  exact equal_kinematics _ PMDynamics.PMNS.rows _ _ _

end PMDecay.InclusiveMixing
