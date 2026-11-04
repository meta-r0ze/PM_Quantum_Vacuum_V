import PMElementaryParticles.Routing

/-!
# What the routing assumptions do *not* give

Paper V's §2.2 states two caveats that are easy to assume away:

* "A lower-latency configuration need not be reachable: amplitudes, selection
  rules and thresholds are additional conditions."
* "These routing assumptions alone do not prove absolute electron or proton
  stability."

Both are negative claims, and both are provable by explicit `Routing.Model`
countermodels. They show the routing axioms are not secretly claiming more than
they do.

* `lower_latency_not_reachable` — a model with a strictly lower-latency,
  same-label state that is not a step from the given state.
* `routing_not_terminal` — a model with a non-terminal state, so the routing
  axioms alone do not force every state to be stable.

Together with `Routing.minimum_terminal` (a minimum-latency state *is* terminal)
and `Routing.no_infinite_descent`, these pin down exactly what routing alone
buys.
-/

noncomputable section
namespace PMElementaryParticles.ProtocolCaveats
open PMElementaryParticles.Routing

/-- A three-state routing model: `2 → 1`, with latency the state index. -/
def tauModel : Model (Fin 3) Unit where
  latency := fun j => j.val
  label := fun _ => ()
  step := fun s t => s = 2 ∧ t = 1
  descends := by
    intro s t h
    obtain ⟨rfl, rfl⟩ := h
    decide
  preserves := by
    intro s t _
    rfl

/-- **A lower-latency same-label state need not be reachable.** State `0` has
strictly lower latency than state `2` and the same label, but is not a step from
`2` (only `2 → 1` is allowed). -/
theorem lower_latency_not_reachable :
    ∃ (M : Model (Fin 3) Unit) (s t : Fin 3),
      M.latency t < M.latency s ∧ M.label t = M.label s ∧ ¬ M.step s t := by
  refine ⟨tauModel, 2, 0, ?_, rfl, ?_⟩
  · simp [tauModel]
  · simp [tauModel]

/-- **Routing assumptions alone do not force stability.** `tauModel` has a
non-terminal state (`2 → 1`), so "every state is terminal" is false for the
routing axioms. -/
theorem routing_not_terminal :
    ∃ (M : Model (Fin 3) Unit) (s : Fin 3), ¬ Terminal M s := by
  refine ⟨tauModel, 2, ?_⟩
  intro h
  exact h 1 (by simp [tauModel])

end PMElementaryParticles.ProtocolCaveats
