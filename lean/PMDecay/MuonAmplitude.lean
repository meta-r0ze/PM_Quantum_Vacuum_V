import PMAction.VATrace
import PMDecay.MuonRate

/-!
# The muon amplitude from the V−A trace

`MuonRate` took the spin-averaged amplitude `64 G_F² (p·k̄)(pₑ·k)` as its first input. Paper II's
`VATrace.muon_amplitude` derives it from the trace algebra of the actual Dirac matrices. This
module states the match for real momenta in `MuonRate`'s conventions.

* `amplitude_matches`: for real four-momenta, the spin-averaged trace product of
  `VATrace.muon_amplitude` equals `64 G² (p·k̄)(pₑ·k)` computed with `MuonRate.mdot`.

**Spin sums.** `Σ_s u_s ū_s = p̸`, or equivalently `Σ_s u_s u_s† = p̸ γ⁰`, says that for a
massless momentum the operator `p̸γ⁰` is `2p⁰` times the orthogonal projector onto the solutions
of `p̸ u = 0`. Proved here for real `p` with `p² = 0`:
* `spin_hermitian`: `p̸γ⁰` is Hermitian.
* `spin_projector`: `(p̸γ⁰)² = 2p⁰ · p̸γ⁰`.
* `spin_solutions`: `p̸ (p̸γ⁰) = 0`, so its range consists of massless solutions.
* `spin_trace`: `Tr(p̸γ⁰) = 4p⁰`, so the projector has rank `2`, the two spin states.
So `p̸γ⁰/(2p⁰)` is a rank-2 orthogonal projector onto the massless solutions. Summing `u u†` over
any orthonormal pair of solutions normalized to `u†u = 2p⁰` gives `p̸γ⁰`; that last step is
standard linear algebra and is not formalized.

Remaining input: the identification of the vertex with the charged current.
-/

noncomputable section
namespace PMDecay.MuonAmplitude
open PMAction Matrix

lemma mdot_cast (a b : Fin 4 → ℝ) :
    VATrace.mdot (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) = (MuonRate.mdot a b : ℂ) := by
  simp [VATrace.mdot, MuonRate.mdot]

/-- **The `64 G²` input of `MuonRate`, from the trace.** -/
theorem amplitude_matches (G : ℝ) (p pe k kbar : Fin 4 → ℝ) :
    (G : ℂ) ^ 2 / 2 * (∑ μ, ∑ ν, VATrace.η μ * VATrace.η ν *
        VATrace.W (fun i => (k i : ℂ)) (fun i => (p i : ℂ)) μ ν *
        VATrace.W (fun i => (pe i : ℂ)) (fun i => (kbar i : ℂ)) μ ν) / 2 =
      ((64 * G ^ 2 * MuonRate.mdot p kbar * MuonRate.mdot pe k : ℝ) : ℂ) := by
  rw [(VATrace.muon_amplitude _ _ _ _ _).2, mdot_cast, mdot_cast]
  push_cast; ring

/-- A real four-momentum as complex components. -/
def cplx (p : Fin 4 → ℝ) : Fin 4 → ℂ := fun i => (p i : ℂ)

theorem spin_hermitian (p : Fin 4 → ℝ) :
    (VATrace.sl (cplx p) * VATrace.g 0)ᴴ = VATrace.sl (cplx p) * VATrace.g 0 := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [VATrace.sl, VATrace.g, cplx, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem spin_projector (p : Fin 4 → ℝ) (h : p 0 ^ 2 = p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2) :
    (VATrace.sl (cplx p) * VATrace.g 0) * (VATrace.sl (cplx p) * VATrace.g 0) =
      (2 * (p 0 : ℂ)) • (VATrace.sl (cplx p) * VATrace.g 0) := by
  have hc : (p 0 : ℂ) ^ 2 = (p 1 : ℂ) ^ 2 + (p 2 : ℂ) ^ 2 + (p 3 : ℂ) ^ 2 := by exact_mod_cast h
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [VATrace.sl, VATrace.g, cplx, Matrix.mul_apply, Fin.sum_univ_four] <;>
    ring_nf <;> simp only [Complex.I_sq] <;>
    first | ring1 | linear_combination hc | linear_combination -hc

theorem spin_solutions (p : Fin 4 → ℝ) (h : p 0 ^ 2 = p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2) :
    VATrace.sl (cplx p) * (VATrace.sl (cplx p) * VATrace.g 0) = 0 := by
  have hc : (p 0 : ℂ) ^ 2 = (p 1 : ℂ) ^ 2 + (p 2 : ℂ) ^ 2 + (p 3 : ℂ) ^ 2 := by exact_mod_cast h
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [VATrace.sl, VATrace.g, cplx, Matrix.mul_apply, Fin.sum_univ_four] <;>
    ring_nf <;> simp only [Complex.I_sq] <;>
    first | ring1 | linear_combination hc

theorem spin_trace (p : Fin 4 → ℝ) : (VATrace.sl (cplx p) * VATrace.g 0).trace = 4 * (p 0 : ℂ) := by
  simp [VATrace.sl, VATrace.g, cplx, Matrix.trace, Fin.sum_univ_four]; ring

end PMDecay.MuonAmplitude
