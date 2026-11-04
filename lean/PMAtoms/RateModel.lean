import PMSubstrate.NetCost
import PMAtoms.MeanLife
import Mathlib.Tactic

/-!
# Per-channel rate from the E8 cost ledger

`PMSubstrate.NetCost` defines the operational cost of persistence as
`toll × expected number of transitions`, with the toll `c₀` set to one by
Closure. This module reads that ledger for a decay channel: a channel is a finite
family of transition events, its cost rate is `c₀ · Σ probability(event)`, and
the persistence hazard makes the decay rate `β · costRate`. The lifetime is then
`MeanLife (β · costRate)`.

This is the bridge the review asked for: `channelRate_eq` proves
`rate = β · costRate` on the actual event families, and the cost comes from the
substrate transition ledger, not from a measured lifetime. What is still a model
choice is **which transition family a given nuclear channel uses**; that is the
remaining binding/rate input, not an outside numerical rate.
-/

noncomputable section
namespace PMAtoms

open PMSubstrate.NetCost

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Cost rate of a channel, read from the toll ledger. -/
def channelCost (c0 : ℝ) {k : ℕ} (E : Fin k → Finset Ω) : ℝ :=
  expectedCost c0 E

/-- The ledger cost is linear in the transition probabilities (the toll is the
only weight). -/
theorem channelCost_eq (c0 : ℝ) {k : ℕ} (E : Fin k → Finset Ω) :
    channelCost c0 E = c0 * ∑ i, prob (E i) :=
  expected_count_linear c0 E

/-- Decay rate of a channel: the persistence hazard coefficient times the
ledger cost rate. -/
def channelRate (β c0 : ℝ) {k : ℕ} (E : Fin k → Finset Ω) : ℝ :=
  β * channelCost c0 E

/-- **`rate = β · costRate` on the actual channel**, with the cost expanded as
toll times expected transition count. -/
theorem channelRate_eq (β c0 : ℝ) {k : ℕ} (E : Fin k → Finset Ω) :
    channelRate β c0 E = β * c0 * ∑ i, prob (E i) := by
  unfold channelRate
  rw [channelCost_eq]
  ring

/-- Mean life of a channel from its ledger cost. -/
def channelMeanLife (β c0 : ℝ) {k : ℕ} (E : Fin k → Finset Ω) : ℝ :=
  MeanLife (channelRate β c0 E)

theorem channelMeanLife_eq (β c0 : ℝ) {k : ℕ} (E : Fin k → Finset Ω)
    (_h : 0 < channelRate β c0 E) :
    channelMeanLife β c0 E = 1 / (β * c0 * ∑ i, prob (E i)) := by
  unfold channelMeanLife
  rw [MeanLife, channelRate_eq]

/-- No realized transitions ⇒ zero cost, hence zero rate. -/
theorem channelCost_zero (c0 : ℝ) {k : ℕ} (E : Fin k → Finset Ω)
    (h : ∀ i, prob (E i) = 0) : channelCost c0 E = 0 := by
  rw [channelCost_eq]
  simp [h]

theorem channelRate_zero (β c0 : ℝ) {k : ℕ} (E : Fin k → Finset Ω)
    (h : ∀ i, prob (E i) = 0) : channelRate β c0 E = 0 := by
  unfold channelRate
  rw [channelCost_zero c0 E h]
  ring

/-- **The rate is the persistence hazard of the ledger cost.** This restates the
`MeanLife` bridge for a concrete channel: a positive toll, positive hazard
coefficient and positive expected transition count give a positive lifetime. -/
theorem channelMeanLife_pos (β c0 : ℝ) {k : ℕ} (E : Fin k → Finset Ω)
    (hβ : 0 < β) (hc0 : 0 < c0) (hE : 0 < ∑ i, prob (E i)) :
    0 < channelMeanLife β c0 E := by
  unfold channelMeanLife
  rw [MeanLife]
  apply one_div_pos.mpr
  rw [channelRate_eq]
  positivity

end PMAtoms
