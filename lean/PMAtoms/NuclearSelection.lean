import PMAtoms.NuclearGraph
import PMAtoms.NuclearPacking
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Persistence selection over nuclear graphs

A finite family of labelled graphs has a least-cost member; that member is the
persistent configuration. The enumeration of all degree-≤4 graphs on four
vertices shows the tetrahedron (K4) is in the candidate set.
-/

noncomputable section
namespace PMAtoms

/-- A finite graph candidate with its binding cost. -/
structure GraphCandidate where
  name : Nat
  cost : ℝ

/-- A finite family has a least-cost graph. -/
theorem exists_least_graph_cost (cands : Finset GraphCandidate) (h : cands.Nonempty) :
    ∃ best ∈ cands, ∀ c ∈ cands, best.cost ≤ c.cost :=
  cands.exists_min_image GraphCandidate.cost h

/-- The persistence-selected graph. -/
def selectedGraph (cands : Finset GraphCandidate) (h : cands.Nonempty) : GraphCandidate :=
  Classical.choose (exists_least_graph_cost cands h)

theorem selectedGraph_min (cands : Finset GraphCandidate) (h : cands.Nonempty) :
    ∀ c ∈ cands, (selectedGraph cands h).cost ≤ c.cost :=
  (Classical.choose_spec (exists_least_graph_cost cands h)).2

/-- Local persistence: no candidate has lower cost. -/
def GraphPersists (cands : Finset GraphCandidate) (c : GraphCandidate) : Prop :=
  c ∈ cands ∧ ∀ d ∈ cands, c.cost ≤ d.cost

theorem selectedGraph_persists (cands : Finset GraphCandidate) (h : cands.Nonempty) :
    GraphPersists cands (selectedGraph cands h) :=
  ⟨Classical.choose_spec (exists_least_graph_cost cands h) |>.1,
    selectedGraph_min cands h⟩

/-- Incident edges of vertex `v` in an edge set. -/
def incidentCount (E : Finset (Fin 4 × Fin 4)) (v : Fin 4) : Nat :=
  (E.filter (fun p => p.1 = v ∨ p.2 = v)).card

/-- All degree-≤4 graphs on four vertices. -/
def graphs4 : Finset (Finset (Fin 4 × Fin 4)) :=
  (pairEdges 4).powerset.filter (fun E => ∀ v, incidentCount E v ≤ 4)

/-- The tetrahedron (K4) is a degree-≤4 candidate. -/
theorem tetrahedron_mem_graphs4 : pairEdges 4 ∈ graphs4 := by
  decide

end PMAtoms
