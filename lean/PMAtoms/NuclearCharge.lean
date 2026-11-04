import PMAtoms.NuclearLine
import PMAction.CoulombKernel
import Mathlib.Tactic

/-!
# Charge energy on the nuclear line

Paper III gives `Q_p = +1`, `Q_n = 0`; Paper II gives the path Green's function.
The static charge energy is `Σ Q_i Q_j G_{ij}`. The relative values for the light
mirror pair are proved here; the absolute E8 coupling scale remains open.
-/

noncomputable section
namespace PMAtoms
open PMAction.CoulombKernel

def qH3 : Fin 3 → ℝ := ![1, 0, 0]
def qHe3 : Fin 3 → ℝ := ![1, 1, 0]
def qHe4 : Fin 4 → ℝ := ![1, 1, 0, 0]

def chargeEnergy3 (Q : Fin 3 → ℝ) : ℝ :=
  ∑ i, ∑ j, Q i * Q j * green3 i j

def chargeEnergy4 (Q : Fin 4 → ℝ) : ℝ :=
  ∑ i, ∑ j, Q i * Q j * green4 i j

theorem chargeEnergy3_H3 : chargeEnergy3 qH3 = 3/4 := by
  unfold chargeEnergy3 qH3
  simp [green3, Fin.sum_univ_three]

theorem chargeEnergy3_He3 : chargeEnergy3 qHe3 = 11/4 := by
  unfold chargeEnergy3 qHe3
  simp [green3, Fin.sum_univ_three]
  norm_num

theorem chargeEnergy4_He4 : chargeEnergy4 qHe4 = 16/5 := by
  unfold chargeEnergy4 qHe4
  simp [green4, Fin.sum_univ_four]
  norm_num

/-- Mirror charge difference `He-3 − H-3 = 2` in kernel units. -/
theorem mirror_charge_difference :
    chargeEnergy3 qHe3 - chargeEnergy3 qH3 = 2 := by
  rw [chargeEnergy3_He3, chargeEnergy3_H3]
  norm_num

end PMAtoms
