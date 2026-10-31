import PMDynamics.ReferenceFlavour
import PMDynamics.WallSpectrumLink

/-!
# External states are on-shell mass eigenstates, from persistence

`REVIEW-AND-NEXT` item 1 keeps "positive on-shell energies" of the external states as a
hypothesis. Part of it follows from persistence.

Write a state in an energy eigenbasis of its Hamiltonian, with energies `E j` and
`E j² = p² + m j²` (for the two-wall fermion, `WallSpectrumLink.wall_energies`). It evolves by
diagonal phases. A state that persists, staying on its ray for all times, has one frequency on its
support (`ReferenceFlavour.persistent_single_frequency`, the beats argument). So:

* `persistent_on_shell`: every component of a persisting state has the same energy and the same
  mass. It is on shell with a definite mass: superpositions across mass branches beat, and
  superpositions of `+E` and `−E` beat. A persisting external particle has one sign of energy and
  one mass.

Still inputs: which sign is called the particle (positive energy is a convention once the sign is
single), and the identification of the external particle with a persisting state of the
substrate.
-/

noncomputable section
namespace PMDecay.ExternalStates
open Complex

/-- **Persisting states are on shell with one mass and one energy.** -/
theorem persistent_on_shell {n : Type*} (E : n → ℝ) (msq : n → ℝ) (p : ℝ)
    (hshell : ∀ j, E j ^ 2 = p ^ 2 + msq j) (c : n → ℂ)
    (hpersist : ∀ t : ℝ, ∃ k : ℂ, ∀ j, c j * exp (-((E j * t : ℝ) : ℂ) * I) = k * c j)
    (i j : n) (hi : c i ≠ 0) (hj : c j ≠ 0) : E i = E j ∧ msq i = msq j := by
  have hE := PMDynamics.ReferenceFlavour.persistent_single_frequency E c hpersist i j hi hj
  refine ⟨hE, ?_⟩
  have := hshell i
  rw [hE, hshell j] at this
  linarith

/-- **Two wall branches with different masses do not form a persisting state.** -/
theorem branches_do_not_persist (E1 E2 : ℝ) (c1 c2 : ℂ) (h1 : c1 ≠ 0) (h2 : c2 ≠ 0)
    (hne : E1 ≠ E2) :
    ¬ ∀ t : ℝ, ∃ k : ℂ, c1 * exp (-((E1 * t : ℝ) : ℂ) * I) = k * c1 ∧
      c2 * exp (-((E2 * t : ℝ) : ℂ) * I) = k * c2 := by
  rw [PMNested.OnShell.beats c1 c2 E1 E2 hne]
  tauto

end PMDecay.ExternalStates
