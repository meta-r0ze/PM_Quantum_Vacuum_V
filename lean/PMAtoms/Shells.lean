import Mathlib.Tactic
import PMAction.WeakVertex

/-!
# Atomic shell capacities from spin-1/2 and angular-momentum degeneracy

An orbital with angular momentum `ℓ` has `2ℓ+1` magnetic states and two spin
states, hence `2(2ℓ+1)` slots. Summing `ℓ = 0..n-1` gives the shell capacity
`2n²`. This is combinatorics, not a fitted atomic model.
-/

namespace PMAtoms

/-- The spin factor is the rank of the PM-2 chiral projector, not an extra
assumption: `PL.trace = 2`. -/
def spinStates : ℕ := 2

theorem spinStates_eq_trace : (spinStates : ℂ) = PMAction.WeakVertex.PL.trace := by
  rw [PMAction.WeakVertex.PL_trace]
  norm_num [spinStates]

/-- Number of states in an orbital with angular momentum `l`. The spin factor
is derived from `PL.trace`; the `2l+1` magnetic degeneracy is the supplied
angular-momentum representation (not derived from E8 here). -/
def orbitalCapacity (l : ℕ) : ℕ := spinStates * (2 * l + 1)

/-- Number of states in shell `n`, accumulated over `l = 0..n-1`. -/
def shellCapacity : ℕ → ℕ
  | 0 => 0
  | n + 1 => shellCapacity n + orbitalCapacity n

theorem orbitalCapacity_eq (l : ℕ) : orbitalCapacity l = 4 * l + 2 := by
  unfold orbitalCapacity spinStates
  ring

/-- The shell capacity is `2n²`. -/
theorem shellCapacity_eq : ∀ n : ℕ, shellCapacity n = 2 * n ^ 2
  | 0 => by simp [shellCapacity]
  | n + 1 => by
      simp [shellCapacity, shellCapacity_eq n, orbitalCapacity, spinStates]
      ring

/-- The first four shell capacities: 2, 8, 18, 32. -/
theorem shell_capacities :
    shellCapacity 1 = 2 ∧ shellCapacity 2 = 8 ∧
      shellCapacity 3 = 18 ∧ shellCapacity 4 = 32 := by
  decide

end PMAtoms
