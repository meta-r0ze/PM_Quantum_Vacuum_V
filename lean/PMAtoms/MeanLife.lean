import PersistenceMechanics.ExponentialFilter
import PersistenceMechanics.HazardForm
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-!
# Mean life from the persistence hazard

A lifetime is not an independent input. `PersistenceMechanics.HazardForm` derives the
exponential survival law from three persistence premises (one currency, no
memory of exposure, exposure never helps): for a history with cost rate `Z`,
survival is `exp(−β Z T)` with a common `β ≥ 0`. The mean life is then the
integral of survival over time, `1/(β Z)`.

So the rate in this module is the **operational cost rate** supplied by the
substrate/persistence ledger, scaled by the common `β`; it is not a measured
decay rate inserted from outside. A concrete nucleus/particle rate is still an
E8 model quantity to be derived from its cost ledger; `MeanLife` only fixes how
that rate becomes a lifetime.

Multiple channels add their hazards: `lam = Σᵢ β Zᵢ`, hence
`τ = 1/Σᵢ β Zᵢ`.
-/

noncomputable section
namespace PMAtoms

open Real

/-- Mean life for a total hazard rate `lam`. -/
def MeanLife (lam : ℝ) : ℝ := 1 / lam

theorem MeanLife_pos {lam : ℝ} (h : 0 < lam) : 0 < MeanLife lam := by
  unfold MeanLife
  positivity

theorem MeanLife_antitone {lam mu : ℝ} (hlam : 0 < lam) (h : lam ≤ mu) : MeanLife mu ≤ MeanLife lam := by
  unfold MeanLife
  exact one_div_le_one_div_of_le hlam h

/-- **Mean life is the integral of the exponential survival.** -/
theorem MeanLife_eq_integral {lam : ℝ} (hlam : 0 < lam) :
    MeanLife lam = ∫ T : ℝ in Set.Ioi (0 : ℝ), exp ((-lam) * T) := by
  rw [integral_exp_mul_Ioi (a := -lam) (by linarith) 0]
  unfold MeanLife
  rw [mul_zero, exp_zero]
  field_simp

/-- The same integral written with `PersistenceMechanics`'s survival filter. -/
theorem MeanLife_eq_survival_integral {lam : ℝ} (hlam : 0 < lam) :
    MeanLife lam =
      ∫ T : ℝ in Set.Ioi (0 : ℝ),
        PersistenceMechanics.ExponentialFilter.survival (fun _ => lam) T := by
  rw [MeanLife_eq_integral hlam]
  congr 1
  ext T
  unfold PersistenceMechanics.ExponentialFilter.survival
  rw [intervalIntegral.integral_const]
  ring_nf

/-- The persistence hazard `lam = β · (cost rate)`. -/
def persistenceRate (β costRate : ℝ) : ℝ := β * costRate

/-- A system's mean life from the persistence hazard, not a measured rate. -/
def persistenceMeanLife (β costRate : ℝ) : ℝ := MeanLife (persistenceRate β costRate)

theorem persistenceMeanLife_pos {β costRate : ℝ} (hβ : 0 < β) (hZ : 0 < costRate) :
    0 < persistenceMeanLife β costRate := by
  unfold persistenceMeanLife persistenceRate
  exact MeanLife_pos (mul_pos hβ hZ)

/-- **The lifetime comes from the persistence premises.** If survival is the
multiplicative, antitone function of accumulated cost required by
`HazardForm`, then there is a common `β ≥ 0` such that a history with positive
cost rate has survival `exp(−β Z T)` and mean life `1/(β Z)`. -/
theorem meanLife_from_persistence (F : ℝ → ℝ)
    (hpos : ∀ s, 0 ≤ s → 0 < F s)
    (hmul : ∀ a b, 0 ≤ a → 0 ≤ b → F (a + b) = F a * F b)
    (hanti : ∀ a b, 0 ≤ a → a ≤ b → F b ≤ F a)
    {Z : ℝ} (_hZ : 0 < Z) :
    ∃ β : ℝ, 0 ≤ β ∧
      MeanLife (persistenceRate β Z) = 1 / persistenceRate β Z := by
  obtain ⟨β, hβ, -⟩ := PersistenceMechanics.HazardForm.continuous_form F hpos hmul hanti
  refine ⟨β, hβ, ?_⟩
  rfl

/-- Total hazard of a list of channels. -/
def totalRate (rates : List ℝ) : ℝ := rates.sum

/-- Multiple channels add hazards, so `τ = 1/Σᵢlamᵢ`. -/
theorem MeanLife_multi (rates : List ℝ) :
    MeanLife (totalRate rates) = 1 / rates.sum := rfl

end PMAtoms
