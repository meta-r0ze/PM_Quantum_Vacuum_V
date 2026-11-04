import PMAtoms.NuclearFolding
import PMAction.CoulombKernel
import Mathlib.Tactic

/-!
# Lattice Green function on the folded line

The general path Green function on `N` interior sites (Dirichlet ends) is

`G(i,j) = min(i,j)(N+1−max(i,j))/(N+1)`.

Its diagonal is the definite lattice self-energy
`G(i,i) = (i+1)(N−i)/(N+1)`. This removes the continuum `1/a` ambiguity.
-/

noncomputable section
namespace PMAtoms

/-- General path Green function, indices `1..N`. -/
def pathGreen (N : Nat) (i j : Fin N) : ℝ :=
  let a := min (i.val + 1) (j.val + 1)
  let b := max (i.val + 1) (j.val + 1)
  (a : ℝ) * ((N + 1 - b : Nat) : ℝ) / (N + 1)

/-- **Definite lattice self-energy** at site `i`. -/
theorem pathGreen_diag (N : Nat) (i : Fin N) :
    pathGreen N i i =
      ((i.val + 1 : Nat) : ℝ) * ((N - i.val : Nat) : ℝ) / (N + 1) := by
  dsimp [pathGreen]
  rw [min_self, max_self]
  have hsub : N + 1 - (i.val + 1) = N - i.val := by omega
  rw [hsub]

/-- The lattice kernel is symmetric. -/
theorem pathGreen_symm (N : Nat) (i j : Fin N) :
    pathGreen N i j = pathGreen N j i := by
  simp [pathGreen, min_comm, max_comm]

/-- The proved 3-site kernel is the general path Green function at `N=3`. -/
theorem green3_eq_pathGreen :
    PMAction.CoulombKernel.green3 = pathGreen 3 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [PMAction.CoulombKernel.green3, pathGreen] <;> norm_num

/-- The proved 4-site kernel is the general path Green function at `N=4`. -/
theorem green4_eq_pathGreen :
    PMAction.CoulombKernel.green4 = pathGreen 4 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [PMAction.CoulombKernel.green4, pathGreen] <;> norm_num

end PMAtoms
