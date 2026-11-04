import PMAtoms.MeanLife
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Persistence as “the system keeps going”

A system has a finite list of decay-channel hazards. Its total hazard is
`λ = Σᵢ λᵢ`.

* `Persists` means `λ = 0` — no channel contributes a positive rate.
* If `λ > 0`, the mean life is `MeanLife λ = 1/λ`.
* Among a finite family, selection picks a least-total-hazard system.

The channel rates are the E8/persistence quantities from `RateModel`; this module
fixes the “keeps going” rule, not the numerical rates.
-/

noncomputable section
namespace PMAtoms

/-- A system is its list of channel hazards. -/
structure RateSystem where
  rates : List ℝ

namespace RateSystem

def totalRate (s : RateSystem) : ℝ := s.rates.sum

/-- Persistence: total hazard zero. -/
def Persists (s : RateSystem) : Prop := s.totalRate = 0

def meanLife (s : RateSystem) : ℝ := MeanLife s.totalRate

theorem persists_iff_total_zero (s : RateSystem) : s.Persists ↔ s.totalRate = 0 := Iff.rfl

/-- Any positive total hazard means the system does not persist. -/
theorem not_persists_of_pos (s : RateSystem) (h : 0 < s.totalRate) : ¬ s.Persists := by
  intro hp
  unfold Persists at hp
  linarith

theorem meanLife_eq (s : RateSystem) (_h : 0 < s.totalRate) :
    s.meanLife = 1 / s.totalRate := rfl

end RateSystem

/-- A finite family has a least-total-hazard member. -/
theorem exists_least_totalRate (systems : Finset RateSystem) (h : systems.Nonempty) :
    ∃ best ∈ systems, ∀ s ∈ systems, best.totalRate ≤ s.totalRate :=
  systems.exists_min_image RateSystem.totalRate h

/-- The persistence-selected system. -/
def selectedSystem (systems : Finset RateSystem) (h : systems.Nonempty) : RateSystem :=
  Classical.choose (exists_least_totalRate systems h)

theorem selectedSystem_mem (systems : Finset RateSystem) (h : systems.Nonempty) :
    selectedSystem systems h ∈ systems :=
  (Classical.choose_spec (exists_least_totalRate systems h)).1

theorem selectedSystem_min (systems : Finset RateSystem) (h : systems.Nonempty) :
    ∀ s ∈ systems, (selectedSystem systems h).totalRate ≤ s.totalRate :=
  (Classical.choose_spec (exists_least_totalRate systems h)).2

end PMAtoms
