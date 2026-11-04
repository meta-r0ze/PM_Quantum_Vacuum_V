import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# Typed nuclear graphs

Nucleons are vertices labelled `p/n`; links are typed `pp/pn/nn`. The substrate
link capacity is 4 (`linkOverlap` row sum / `D=4`). A closed 4-vertex graph is
the tetrahedron (the first closed 3D cell), the He-4 closure.

This file fixes the types, the complete-graph counts for H-3/He-3/He-4, and the
degree cap. Binding and packing build on it.
-/

namespace PMAtoms

/-- Nucleon labels. -/
inductive NucleonLabel
  | proton | neutron
  deriving DecidableEq, Repr

/-- Inter-nucleon link types. -/
inductive LinkType
  | pp | pn | nn
  deriving DecidableEq, Repr

/-- The type of a link between two labelled nucleons. -/
def edgeType : NucleonLabel → NucleonLabel → LinkType
  | .proton, .proton => .pp
  | .proton, .neutron => .pn
  | .neutron, .proton => .pn
  | .neutron, .neutron => .nn

/-- Unordered pairs of `Fin n`, represented by the lower index first. -/
def pairEdges (n : Nat) : Finset (Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2)

/-- Number of complete-graph edges of a given type for a labelling. -/
def completeEdgeCount {n : Nat} (label : Fin n → NucleonLabel) (t : LinkType) : Nat :=
  ((pairEdges n).filter (fun p => edgeType (label p.1) (label p.2) = t)).card

/-- H-3: one proton, two neutrons. -/
def h3Label : Fin 3 → NucleonLabel := fun i => if i = 0 then .proton else .neutron

/-- He-3: two protons, one neutron. -/
def he3Label : Fin 3 → NucleonLabel := fun i => if i = 0 then .neutron else .proton

/-- He-4: two protons, two neutrons. -/
def he4Label : Fin 4 → NucleonLabel := fun i => if (i : Nat) < 2 then .proton else .neutron

theorem h3_counts :
    completeEdgeCount h3Label .pp = 0 ∧
      completeEdgeCount h3Label .pn = 2 ∧
      completeEdgeCount h3Label .nn = 1 := by
  decide

theorem he3_counts :
    completeEdgeCount he3Label .pp = 1 ∧
      completeEdgeCount he3Label .pn = 2 ∧
      completeEdgeCount he3Label .nn = 0 := by
  decide

theorem he4_counts :
    completeEdgeCount he4Label .pp = 1 ∧
      completeEdgeCount he4Label .pn = 4 ∧
      completeEdgeCount he4Label .nn = 1 := by
  decide

/-- Neighbour count, kept explicit to avoid typeclass noise. -/
noncomputable def neighborCount {n : Nat} (G : SimpleGraph (Fin n)) (v : Fin n) : Nat := by
  classical
  exact (Finset.univ.filter (fun w => G.Adj v w)).card

/-- Substrate link capacity: at most four links per nucleon. -/
def degreeCap {n : Nat} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ v, neighborCount G v ≤ 4

/-- The complete graph on four vertices: the tetrahedron. -/
def tetrahedron : SimpleGraph (Fin 4) := ⊤

theorem tetrahedron_neighbors (v : Fin 4) : neighborCount tetrahedron v = 3 := by
  classical
  fin_cases v <;> simp [neighborCount, tetrahedron] <;> decide

theorem tetrahedron_degreeCap : degreeCap tetrahedron := by
  intro v
  rw [tetrahedron_neighbors]
  norm_num

/-- The tetrahedron is closed: every vertex has all three internal neighbours. -/
theorem tetrahedron_closed (v : Fin 4) : neighborCount tetrahedron v = 3 :=
  tetrahedron_neighbors v

/-- Binding of a complete labelled graph, given link weights and a closure term. -/
def bindingComplete {n : Nat} (w : LinkType → ℝ) (label : Fin n → NucleonLabel)
    (closure : ℝ) : ℝ :=
  (w .pp) * (completeEdgeCount label .pp : ℝ) +
    (w .pn) * (completeEdgeCount label .pn : ℝ) +
    (w .nn) * (completeEdgeCount label .nn : ℝ) + closure

/-- He-4 binding decomposition: `w_pp + 4 w_pn + w_nn + closure`. -/
theorem he4_binding (w : LinkType → ℝ) (closure : ℝ) :
    bindingComplete w he4Label closure = w .pp + 4 * w .pn + w .nn + closure := by
  unfold bindingComplete
  rw [he4_counts.1, he4_counts.2.1, he4_counts.2.2]
  norm_num
  ring

/-- H-3 binding decomposition. -/
theorem h3_binding (w : LinkType → ℝ) (closure : ℝ) :
    bindingComplete w h3Label closure = 2 * w .pn + w .nn + closure := by
  unfold bindingComplete
  rw [h3_counts.1, h3_counts.2.1, h3_counts.2.2]
  norm_num
  ring

/-- He-3 binding decomposition. -/
theorem he3_binding (w : LinkType → ℝ) (closure : ℝ) :
    bindingComplete w he3Label closure = w .pp + 2 * w .pn + closure := by
  unfold bindingComplete
  rw [he3_counts.1, he3_counts.2.1, he3_counts.2.2]
  norm_num
  ring

end PMAtoms
