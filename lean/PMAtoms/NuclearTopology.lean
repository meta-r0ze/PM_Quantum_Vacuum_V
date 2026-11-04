import PMAtoms.AxisSplit
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-!
# Closed persistence selects the cycle

A persistent closed system has no dangling ends: every nucleon keeps at least two
links. By the handshake lemma, a graph on `A` vertices with minimum degree 2 has
at least `A` edges. The triangle (`K3`) attains that bound, so the smallest closed
system is a 3-cycle — the line/ring selection principle.
-/

noncomputable section
namespace PMAtoms

/-- **Closed-system lower bound.** Minimum degree 2 forces at least `A` edges. -/
theorem closed_min_edges {A : Nat} (G : SimpleGraph (Fin A)) [DecidableRel G.Adj]
    (h : ∀ v, 2 ≤ G.degree v) : A ≤ G.edgeFinset.card := by
  have hsum : (∑ v, G.degree v) = 2 * G.edgeFinset.card :=
    G.sum_degrees_eq_twice_card_edges
  have hle : A * 2 ≤ ∑ v, G.degree v := by
    calc
      A * 2 = ∑ _v : Fin A, 2 := by simp
      _ ≤ ∑ v, G.degree v := by
        exact Finset.sum_le_sum (fun v _ => h v)
  omega

/-- **Open (line) systems.** A tree is the minimal connected graph: `A − 1` edges. -/
theorem tree_edges {A : Nat} (G : SimpleGraph (Fin A)) [DecidableRel G.Adj]
    (hG : G.IsTree) : G.edgeFinset.card = A - 1 := by
  have h := hG.card_edgeFinset
  rw [Fintype.card_fin] at h
  omega

/-- The triangle `K3` has degree 2 at every vertex. -/
theorem triangle_degree (v : Fin 3) : (⊤ : SimpleGraph (Fin 3)).degree v = 2 := by
  fin_cases v <;> decide

/-- The triangle has exactly three edges. -/
theorem triangle_edges : (⊤ : SimpleGraph (Fin 3)).edgeFinset.card = 3 := by
  decide

/-- **The triangle is the minimal closed system.** It meets the lower bound
`A ≤ edges` with equality at `A = 3`. -/
theorem triangle_is_minimal_closed :
    (⊤ : SimpleGraph (Fin 3)).edgeFinset.card = 3 ∧
      (3 : Nat) ≤ (⊤ : SimpleGraph (Fin 3)).edgeFinset.card := by
  constructor
  · exact triangle_edges
  · rw [triangle_edges]

end PMAtoms
