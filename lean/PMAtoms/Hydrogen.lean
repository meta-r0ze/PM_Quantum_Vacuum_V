import PMConstants.CertifiedConstants
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Hydrogen readouts from the certified fine-structure constant

`E_n = -α² m_e c²/(2n²)` and `a₀ = ħc/(α m_e c²)`. The electron rest energy
and `ħc` are supplied unit inputs; the only E8 content is the certified
enclosure of `α`.
-/

noncomputable section
namespace PMAtoms
open PMConstants

/-- Electron rest energy in eV (CODATA 2022), a supplied unit input. -/
def electronMassEV : ℝ := 510998.95

/-- `ħc` in eV·Å, a supplied unit input. -/
def hbarCEVAngstrom : ℝ := 1973.269804

/-- Rydberg energy `α² m_e c²/2` in the same units as `me`. -/
def rydbergEnergy (α me : ℝ) : ℝ := α ^ 2 * me / 2

/-- Bohr radius `ħc/(α m_e c²)` in the same units as `hbarc`/`me`. -/
def bohrRadius (α me hbarc : ℝ) : ℝ := hbarc / (α * me)

/-- Hydrogen level `E_n = -R/n²`. -/
def hydrogenLevel (α me : ℝ) (n : ℕ) : ℝ := -rydbergEnergy α me / (n : ℝ) ^ 2

/-- Rydberg energy in eV. -/
def rydbergEV : ℝ := rydbergEnergy CertifiedConstants.α electronMassEV

/-- Bohr radius in Å. -/
def bohrRadiusAngstrom : ℝ := bohrRadius CertifiedConstants.α electronMassEV hbarCEVAngstrom

theorem rydbergEV_bounds :
    (13.60569309 : ℝ) < rydbergEV ∧ rydbergEV < 13.60569310 := by
  have h := CertifiedConstants.alpha_bounds
  unfold rydbergEV rydbergEnergy electronMassEV
  constructor <;> nlinarith [h.1, h.2]

theorem bohrRadius_bounds :
    (0.5291772110 : ℝ) < bohrRadiusAngstrom ∧ bohrRadiusAngstrom < 0.5291772114 := by
  have h := CertifiedConstants.alpha_bounds
  unfold bohrRadiusAngstrom bohrRadius electronMassEV hbarCEVAngstrom
  have ha : 0 < CertifiedConstants.α := by linarith [h.1]
  have hd : 0 < CertifiedConstants.α * 510998.95 := mul_pos ha (by norm_num)
  constructor
  · rw [lt_div_iff₀ hd]; nlinarith [h.2]
  · rw [div_lt_iff₀ hd]; nlinarith [h.1]

/-- The `n = 1` level is `-R`. -/
theorem hydrogenLevel_one (α me : ℝ) : hydrogenLevel α me 1 = -rydbergEnergy α me := by
  unfold hydrogenLevel
  norm_num

/-- Every level is the ground-state energy divided by `n²`. -/
theorem hydrogenLevel_ratio (α me : ℝ) (n : ℕ) (_hn : 0 < n) :
    hydrogenLevel α me n = hydrogenLevel α me 1 / (n : ℝ) ^ 2 := by
  rw [hydrogenLevel_one]
  rfl

/-- The ground state is the lowest level. -/
theorem ground_is_lowest {α me : ℝ} (hR : 0 ≤ rydbergEnergy α me) {n : ℕ} (hn : 0 < n) :
    hydrogenLevel α me 1 ≤ hydrogenLevel α me n := by
  rw [hydrogenLevel_one]
  unfold hydrogenLevel
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hle : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hdiv : rydbergEnergy α me / (n : ℝ) ^ 2 ≤ rydbergEnergy α me := by
    rw [div_le_iff₀ hn2]
    simpa [mul_one] using mul_le_mul_of_nonneg_left hle hR
  have hneg : -rydbergEnergy α me / (n : ℝ) ^ 2 =
      -(rydbergEnergy α me / (n : ℝ) ^ 2) := by ring
  rw [hneg]
  exact neg_le_neg hdiv

end PMAtoms
