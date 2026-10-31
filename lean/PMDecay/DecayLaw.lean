import PMDecay.Survival
import PMArch.NetCost
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# The exponential decay law from Paper I's survival law

`REVIEW-AND-NEXT` item 3 asks for the decay law from the dynamics, distinguishing exact finite
updates from a continuum limit. `Survival` proves consequences of a supplied exponential law.

**Exact on the tick lattice.** Paper I prices persistence per cycle: surviving a cycle of net cost
`c` has probability `exp(−β c)`, and survival factorizes over pillars and cycles
(`PMArch.NetCost.survival_factorizes`).

* `ticks_exact`: with the same per-tick cost `c` on every tick (a time-homogeneous update),
  survival after `n` ticks is exactly `exp(−β c n)`. This is `Survival.survive Γ (n τ)` with
  `Γ = β c / τ` (`ticks_are_survive`). No limit is taken.
* `hazard_pos_iff`: the hazard is nonzero exactly when the open decay channel has positive cost
  (`c > 0`). A cost-free channel never decays, as in `Survival.deterministic_state_can_remain`.

**Continuum limit.** If instead a per-tick decay probability `Γ t / n` is compounded over `n`
ticks of total time `t`, survival tends to `exp(−Γ t)` as the tick shrinks (`compounded_limit`).
Exact geometric survival on finite ticks and the exponential law are therefore distinct
statements, related by this limit.

Still inputs: the per-tick cost of the open channel (related to the width by `Γ = width/ħ`), the
tick `τ`, and time homogeneity of the update.
-/

noncomputable section
namespace PMDecay.DecayLaw
open Filter Topology

/-- **Survival over `n` homogeneous ticks is exactly exponential.** -/
theorem ticks_exact (β c : ℝ) (n : ℕ) :
    ∏ _i : Fin n, Real.exp (-β * c) = Real.exp (-β * (c * n)) := by
  have h := (PMArch.NetCost.survival_factorizes β (fun _ : Fin n => c)).symm
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  rw [h]
  ring_nf

/-- The same survival as `Survival.survive` with rate `β c / τ` at time `n τ`. -/
theorem ticks_are_survive (β c τ : ℝ) (hτ : τ ≠ 0) (n : ℕ) :
    ∏ _i : Fin n, Real.exp (-β * c) = Survival.survive (β * c / τ) (n * τ) := by
  rw [ticks_exact, Survival.survive]
  congr 1
  field_simp

/-- **The hazard is nonzero exactly when the channel costs something.** -/
theorem hazard_pos_iff (β c τ : ℝ) (hβ : 0 < β) (hτ : 0 < τ) :
    0 < β * c / τ ↔ 0 < c := by
  constructor
  · intro h
    have := (div_pos_iff_of_pos_right hτ).mp h
    exact (pos_iff_pos_of_mul_pos this).mp hβ
  · intro h
    positivity

/-- **The continuum limit of compounded per-tick decay.** -/
theorem compounded_limit (Γ t : ℝ) :
    Tendsto (fun n : ℕ => (1 - Γ * t / n) ^ n) atTop (𝓝 (Survival.survive Γ t)) := by
  have h := Real.tendsto_one_add_div_pow_exp (-Γ * t)
  rw [Survival.survive]
  convert h using 2 with n
  ring

end PMDecay.DecayLaw
