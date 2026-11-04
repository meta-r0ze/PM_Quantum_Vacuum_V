import PMElementaryParticles.ContinuumPair

/-!
# First step of the phase-space construction: the angular surface area

`MuonRate` and `ContinuumPair` use the angular weight `4π`, but from a supplied
measure convention. This module derives that weight from an actual iterated
integral over the direction sphere in the `(z = cos θ, φ)` coordinates, and shows
the normalized uniform average of a constant is one. It is the first concrete
step toward constructing the phase-space measure (Review Part A1); the
delta-function / energy-shell reduction is still open.

* `solidAngle_one` — `∫_{z∈[−1,1]} ∫_{φ∈[0,2π]} 1 = 4π`, the unit-sphere area.
* `average_one` — the normalized uniform angular average of `1` is `1`.
* `electron_measure_radial` — the massless radial measure `E/(4π²)` follows from
  `4π` and `p = E`, matching `MuonRate.electron_measure`.
-/

noncomputable section
namespace PMElementaryParticles.PhaseSpace
open intervalIntegral

/-- **The unit direction sphere has area `4π`** in the `(z, φ)` coordinates. -/
theorem solidAngle_one : ContinuumPair.solidAngle (fun _ _ => (1 : ℝ)) = 4 * Real.pi := by
  unfold ContinuumPair.solidAngle
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- The normalized uniform angular average of a constant is one. -/
theorem average_one :
    (1 / (4 * Real.pi)) * ContinuumPair.solidAngle (fun _ _ => (1 : ℝ)) = 1 := by
  rw [solidAngle_one]
  field_simp

/-- **The massless radial electron measure** `E/(4π²)` from the angular area and
`p = E`: `4π E² / ((2π)³ 2E) = E/(4π²)`. -/
theorem electron_measure_radial (E : ℝ) (hE : E ≠ 0) :
    4 * Real.pi * E ^ 2 / ((2 * Real.pi) ^ 3 * (2 * E)) = E / (4 * Real.pi ^ 2) :=
  MuonRate.electron_measure E hE

end PMElementaryParticles.PhaseSpace
