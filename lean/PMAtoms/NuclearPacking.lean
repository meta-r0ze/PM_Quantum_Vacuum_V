import PMAtoms.NuclearGraph
import Mathlib.Tactic

/-!
# Tetrahedron packing

Two tetrahedra sharing a triangular face: 3 shared vertices, 3 shared edges,
6 + 6 − 3 = 9 union edges. The shared closure is counted once, not twice.
-/

namespace PMAtoms

/-- All edges of a vertex set (lower index first). -/
def cliqueEdges {n : Nat} (s : Finset (Fin n)) : Finset (Fin n × Fin n) :=
  (s.product s).filter (fun p => p.1 < p.2)

theorem tetrahedron_edges :
    (cliqueEdges (Finset.univ : Finset (Fin 4))).card = 6 := by
  decide

/-- First tetrahedron on vertices `{0,1,2,3}`. -/
def tetA : Finset (Fin 5) := {0, 1, 2, 3}

/-- Second tetrahedron on vertices `{0,1,2,4}`, sharing the face `{0,1,2}`. -/
def tetB : Finset (Fin 5) := {0, 1, 2, 4}

theorem tetA_card : tetA.card = 4 := by decide
theorem tetB_card : tetB.card = 4 := by decide

theorem tetA_edges : (cliqueEdges tetA).card = 6 := by decide
theorem tetB_edges : (cliqueEdges tetB).card = 6 := by decide

theorem shared_vertices : (tetA ∩ tetB).card = 3 := by decide
theorem shared_edges : (cliqueEdges tetA ∩ cliqueEdges tetB).card = 3 := by decide

/-- The union of two face-sharing tetrahedra has `6 + 6 − 3 = 9` edges. -/
theorem union_edges : (cliqueEdges tetA ∪ cliqueEdges tetB).card = 9 := by decide

/-- The shared closure is counted once: `2c − c = c`. -/
theorem shared_closure_once (c : ℝ) : 2 * c - c = c := by ring

/-! ## Other tetrahedron joins -/

/-- Vertex-sharing chain on `Fin 7`: `{0,1,2,3}` and `{3,4,5,6}`. -/
def tetA7 : Finset (Fin 7) := {0, 1, 2, 3}
def tetC7 : Finset (Fin 7) := {3, 4, 5, 6}

theorem vertex_shared_vertices : (tetA7 ∩ tetC7).card = 1 := by decide
theorem vertex_shared_edges :
    (cliqueEdges tetA7 ∪ cliqueEdges tetC7).card = 12 := by decide

/-- Edge-sharing chain on `Fin 6`: `{0,1,2,3}` and `{0,1,4,5}`. -/
def tetA6 : Finset (Fin 6) := {0, 1, 2, 3}
def tetB6 : Finset (Fin 6) := {0, 1, 4, 5}

theorem edge_shared_vertices : (tetA6 ∩ tetB6).card = 2 := by decide
theorem edge_shared_edges :
    (cliqueEdges tetA6 ∪ cliqueEdges tetB6).card = 11 := by decide

/-- Packing laws: face `(5 vertices, 9 edges)`, vertex `(7, 12)`, edge `(6, 11)`. -/
theorem packing_laws :
    (cliqueEdges tetA ∪ cliqueEdges tetB).card = 9 ∧
      (cliqueEdges tetA7 ∪ cliqueEdges tetC7).card = 12 ∧
      (cliqueEdges tetA6 ∪ cliqueEdges tetB6).card = 11 := by
  decide

end PMAtoms
