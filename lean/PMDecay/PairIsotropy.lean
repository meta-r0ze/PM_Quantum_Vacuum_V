import PMDecay.MuonRate

/-! Derive the rest-frame pair moments from an explicitly invariant angular
average, rather than assuming the tensor coefficients. Only sign flips and
axis interchanges are needed. This linear moment-functional interface can model
a finite angular quadrature. A continuum integral needs an appropriate integrable
test-function domain; that construction is not included. Existence, positivity,
Lorentz covariance and physical measure normalization are not asserted here. -/
noncomputable section
namespace PMDecay.PairIsotropy

/-- A linear angular average of unit spatial directions. Symmetries act on
samples, and the average is invariant under those actions. -/
structure AngularAverage (Ω : Type*) where
  average : (Ω → ℝ) →ₗ[ℝ] ℝ
  direction : Fin 3 → Ω → ℝ
  unit_length : ∀ ω, ∑ i, direction i ω ^ 2 = 1
  flip : Fin 3 → Ω → Ω
  flip_invariant : ∀ i f, average (fun ω => f (flip i ω)) = average f
  flip_direction : ∀ i j ω,
    direction j (flip i ω) = if i = j then -direction j ω else direction j ω
  swap : Fin 3 → Fin 3 → Ω → Ω
  swap_invariant : ∀ i j f, average (fun ω => f (swap i j ω)) = average f
  swap_direction : ∀ i j ω, direction i (swap i j ω) = direction j ω

namespace AngularAverage

variable {Ω : Type*} (A : AngularAverage Ω)

def volume : ℝ := A.average (fun _ => 1)

theorem first_moment (i : Fin 3) : A.average (A.direction i) = 0 := by
  have h := A.flip_invariant i (A.direction i)
  simp [A.flip_direction] at h
  change A.average (-A.direction i) = A.average (A.direction i) at h
  rw [map_neg] at h
  linarith

theorem off_diagonal (i j : Fin 3) (hij : i ≠ j) :
    A.average (fun ω => A.direction i ω * A.direction j ω) = 0 := by
  have h := A.flip_invariant i (fun ω => A.direction i ω * A.direction j ω)
  simp [A.flip_direction, hij, neg_mul] at h
  change A.average (-(fun ω => A.direction i ω * A.direction j ω)) = _ at h
  rw [map_neg] at h
  linarith

theorem diagonal_equal (i j : Fin 3) :
    A.average (fun ω => A.direction i ω ^ 2) =
      A.average (fun ω => A.direction j ω ^ 2) := by
  have h := A.swap_invariant i j (fun ω => A.direction i ω ^ 2)
  simpa only [A.swap_direction] using h.symm

theorem diagonal (i : Fin 3) :
    A.average (fun ω => A.direction i ω ^ 2) = A.volume / 3 := by
  have h := congrArg A.average (funext A.unit_length)
  have hf : (fun ω => ∑ j, A.direction j ω ^ 2) =
      (fun ω => A.direction 0 ω ^ 2) + (fun ω => A.direction 1 ω ^ 2) +
        (fun ω => A.direction 2 ω ^ 2) := by
    funext ω; simp [Fin.sum_univ_three]
  rw [hf, map_add, map_add] at h
  rw [← A.diagonal_equal i 0, ← A.diagonal_equal i 1, ← A.diagonal_equal i 2] at h
  change _ = A.volume at h
  linarith

theorem second_moment (i j : Fin 3) :
    A.average (fun ω => A.direction i ω * A.direction j ω) =
      if i = j then A.volume / 3 else 0 := by
  split_ifs with h
  · subst j
    simpa only [← pow_two] using A.diagonal i
  · exact A.off_diagonal i j h

/-- Massless pair in its rest frame, each member with energy Q/2. -/
def leftMomentum (Q : ℝ) (ω : Ω) : Fin 4 → ℝ :=
  ![Q/2, Q/2*A.direction 0 ω, Q/2*A.direction 1 ω, Q/2*A.direction 2 ω]

def rightMomentum (Q : ℝ) (ω : Ω) : Fin 4 → ℝ :=
  ![Q/2, -Q/2*A.direction 0 ω, -Q/2*A.direction 1 ω, -Q/2*A.direction 2 ω]

/-- The complete rest-frame tensor. For q=(Q,0,0,0), this is exactly
(Φ/12) g^{μν} Q² + (Φ/6) q^μ q^ν. No tensor ansatz is assumed. -/
theorem rest_tensor (Q : ℝ) (μ ν : Fin 4) :
    A.average (fun ω => A.leftMomentum Q ω μ * A.rightMomentum Q ω ν) =
      if μ = 0 ∧ ν = 0 then A.volume * Q ^ 2 / 4
      else if μ = ν then -A.volume * Q ^ 2 / 12 else 0 := by
  have hc (c : ℝ) (f : Ω → ℝ) :
      A.average (fun ω => c * f ω) = c * A.average f := A.average.map_smul c f
  have hconst (c : ℝ) : A.average (fun _ => c) = c * A.volume := by
    simpa only [mul_one, volume] using hc c (fun _ => 1)
  have hl (c : ℝ) (i : Fin 3) :
      A.average (fun ω => c * A.direction i ω) = 0 := by
    rw [hc, A.first_moment, mul_zero]
  have hp (c : ℝ) (i j : Fin 3) :
      A.average (fun ω => c * (A.direction i ω * A.direction j ω)) =
        c * (if i = j then A.volume / 3 else 0) := by
    rw [hc, A.second_moment]
  have hll (a b : ℝ) (i j : Fin 3) :
      A.average (fun ω => (a * A.direction i ω) * (b * A.direction j ω)) =
        (a*b) * (if i = j then A.volume / 3 else 0) := by
    calc
      _ = A.average (fun ω => (a*b) * (A.direction i ω * A.direction j ω)) := by
        congr 1; funext ω; ring
      _ = _ := hp (a*b) i j
  have hcl (a b : ℝ) (i : Fin 3) :
      A.average (fun ω => a * (b * A.direction i ω)) = 0 := by
    simpa only [← mul_assoc] using hl (a*b) i
  have hlc (a b : ℝ) (i : Fin 3) :
      A.average (fun ω => (a * A.direction i ω) * b) = 0 := by
    calc
      _ = A.average (fun ω => (a*b) * A.direction i ω) := by
        congr 1; funext ω; ring
      _ = 0 := hl (a*b) i
  fin_cases μ <;> fin_cases ν <;>
    simp [leftMomentum, rightMomentum, hconst, hcl, hlc, hll] <;> ring

/-- Signature (+---) and the total momentum of the rest-frame pair. -/
def metric : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1, -1, -1, -1]
def restMomentum (Q : ℝ) : Fin 4 → ℝ := ![Q, 0, 0, 0]

/-- Both members of the pair are on the massless shell. Positive energy
additionally requires Q>0; no positivity is needed for this identity. -/
theorem massless_pair (Q : ℝ) (ω : Ω) :
    MuonRate.mdot (A.leftMomentum Q ω) (A.leftMomentum Q ω) = 0 ∧
    MuonRate.mdot (A.rightMomentum Q ω) (A.rightMomentum Q ω) = 0 := by
  have hn := A.unit_length ω
  simp only [Fin.sum_univ_three] at hn
  have hl : MuonRate.mdot (A.leftMomentum Q ω) (A.leftMomentum Q ω) =
      Q^2/4 * (1 - (A.direction 0 ω^2 + A.direction 1 ω^2 + A.direction 2 ω^2)) := by
    simp [MuonRate.mdot, leftMomentum]; ring
  have hr : MuonRate.mdot (A.rightMomentum Q ω) (A.rightMomentum Q ω) =
      Q^2/4 * (1 - (A.direction 0 ω^2 + A.direction 1 ω^2 + A.direction 2 ω^2)) := by
    simp [MuonRate.mdot, rightMomentum]; ring
  rw [hl, hr, hn]
  simp

theorem pair_sum (Q : ℝ) (ω : Ω) :
    A.leftMomentum Q ω + A.rightMomentum Q ω = restMomentum Q := by
  ext μ; fin_cases μ <;> simp [leftMomentum, rightMomentum, restMomentum] <;> ring

/-- The tensor form and its two coefficients follow in the rest frame from
angular symmetry and unit length. No division by Q is needed. -/
theorem rest_covariant (Q : ℝ) (μ ν : Fin 4) :
    A.average (fun ω => A.leftMomentum Q ω μ * A.rightMomentum Q ω ν) =
      A.volume/12 * metric μ ν * Q^2 +
        A.volume/6 * restMomentum Q μ * restMomentum Q ν := by
  rw [A.rest_tensor]
  fin_cases μ <;> fin_cases ν <;> norm_num [metric, restMomentum, Matrix.diagonal] <;> ring

/-- The coefficients consumed by `MuonRate` follow if the supplied measure
has the stated two-body volume. Its physical normalization remains a premise. -/
theorem normalized_rest (Q : ℝ) (hΦ : A.volume = 1/(8*Real.pi)) (μ ν : Fin 4) :
    A.average (fun ω => A.leftMomentum Q ω μ * A.rightMomentum Q ω ν) =
      1/(96*Real.pi) * metric μ ν * Q^2 +
        2*(1/(96*Real.pi)) * restMomentum Q μ * restMomentum Q ν := by
  rw [A.rest_covariant, hΦ, MuonRate.pair_coeffs.1, MuonRate.pair_coeffs.2]

end AngularAverage
end PMDecay.PairIsotropy
