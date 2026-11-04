import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# 3D lattice Green function

The Dirichlet Laplacian on the `2×2×2` interior of a `4×4×4` cube has the
rational inverse below. Diagonal entries are `58/315`; off-diagonals are
`11/315`, `4/315`, or `2/315` according to the cube geometry.

This is the 3D lattice self-energy (`58/315`), the analogue of the 1D
`pathGreen_diag`.
-/

namespace PMAtoms

/-- `58/315` self-energy, then the off-diagonal rows. -/
def greenRows : List (List Rat) :=
  [ [58/315, 11/315, 11/315,  4/315, 11/315,  4/315,  4/315,  2/315],
    [11/315, 58/315,  4/315, 11/315,  4/315, 11/315,  2/315,  4/315],
    [11/315,  4/315, 58/315, 11/315,  4/315,  2/315, 11/315,  4/315],
    [ 4/315, 11/315, 11/315, 58/315,  2/315,  4/315,  4/315, 11/315],
    [11/315,  4/315,  4/315,  2/315, 58/315, 11/315, 11/315,  4/315],
    [ 4/315, 11/315,  2/315,  4/315, 11/315, 58/315,  4/315, 11/315],
    [ 4/315,  2/315, 11/315,  4/315, 11/315,  4/315, 58/315, 11/315],
    [ 2/315,  4/315,  4/315, 11/315,  4/315, 11/315, 11/315, 58/315] ]

/-- Cube adjacency: sites differing in exactly one coordinate. -/
def adjRows : List (List Bool) :=
  [ [false, true,  true,  false, true,  false, false, false],
    [true,  false, false, true,  false, true,  false, false],
    [true,  false, false, true,  false, false, true,  false],
    [false, true,  true,  false, false, false, false, true ],
    [true,  false, false, false, false, true,  true,  false],
    [false, true,  false, false, true,  false, false, true ],
    [false, false, true,  false, true,  false, false, true ],
    [false, false, false, true,  false, true,  true,  false] ]

def greenCube (i j : Fin 8) : Rat :=
  (greenRows.getD i.val []).getD j.val 0

def cubeAdj (i j : Fin 8) : Bool :=
  (adjRows.getD i.val []).getD j.val false

/-- Dirichlet Laplacian on the cube interior (explicit eight-site sum). -/
def cubeLap (f : Fin 8 → Rat) (v : Fin 8) : Rat :=
  6 * f v
    - (if cubeAdj 0 v then f 0 else 0)
    - (if cubeAdj 1 v then f 1 else 0)
    - (if cubeAdj 2 v then f 2 else 0)
    - (if cubeAdj 3 v then f 3 else 0)
    - (if cubeAdj 4 v then f 4 else 0)
    - (if cubeAdj 5 v then f 5 else 0)
    - (if cubeAdj 6 v then f 6 else 0)
    - (if cubeAdj 7 v then f 7 else 0)

theorem greenCube_symm (i j : Fin 8) : greenCube i j = greenCube j i := by
  fin_cases i <;> fin_cases j <;>
    simp [greenCube, greenRows]

/-- **3D lattice Green identity**: `L G(·,j) = δ_j`. -/
theorem cubeLap_green (j : Fin 8) :
    cubeLap (fun i => greenCube i j) = fun v => if v = j then 1 else 0 := by
  funext v
  fin_cases j <;> fin_cases v <;>
    simp [cubeLap, cubeAdj, greenCube, greenRows, adjRows] <;> norm_num

end PMAtoms
