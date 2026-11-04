import PMSubstrate.Impedance

/-!
# Substrate invariants used by the nuclear model

The numeric factors in the line/ring model are not free: they are the E8
substrate invariants `Δ, ν, σ, χ, D`. This module exposes them and proves the
arithmetic identities used downstream.
-/

namespace PMAtoms

def Δ : Nat := PMSubstrate.baseline.period
def ν : Nat := PMSubstrate.baseline.sectorChannels
def σ : Nat := PMSubstrate.baseline.embeddingDimension
def χ : Nat := PMSubstrate.baseline.eulerCharacteristic
def D : Nat := PMSubstrate.baseline.dimension

theorem invariant_values : Δ = 43 ∧ ν = 16 ∧ σ = 5 ∧ χ = 2 ∧ D = 4 := by
  decide

/-- The 4-channel split is `3 colour + 1 reference`. -/
theorem colour_axes : σ - χ = 3 := by decide
theorem reference_axes : D - (σ - χ) = 1 := by decide
theorem three_plus_one : (σ - χ) + (D - (σ - χ)) = D := by decide

/-- The homo channel pairs two nucleons. -/
theorem homo_pair : χ = 2 := by decide

/-- The folded radius exponent is `1/3`, from the three colour axes. -/
theorem radius_exponent : (1 : ℝ) / (σ - χ) = 1 / 3 := by
  norm_num [σ, χ, PMSubstrate.baseline]

/-- The sphere geometric factor `3/5` is `(σ−χ)/σ`. -/
theorem sphere_factor : ((σ - χ : Nat) : ℝ) / (σ : ℝ) = 3 / 5 := by
  norm_num [σ, χ, PMSubstrate.baseline]

/-- The E8 charge coupling `πD/(2σ)` is the numerical `πD/10`. -/
theorem charge_coupling :
    Real.pi * (D : ℝ) / (2 * (σ : ℝ)) = Real.pi * 4 / 10 := by
  norm_num [D, σ, PMSubstrate.baseline]

end PMAtoms
