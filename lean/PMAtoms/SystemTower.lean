import PMElementaryParticles.CompositeMasses
import PMAtoms.Nucleon
import Mathlib.Tactic

/-!
# The system tower: each level carries its own six-pillar budget

The mass of a composite is not only the sum of its constituents. Each level —
elementary protocol, nucleon, nucleus, atom — contributes its own CAP/MAP/PRO/
GOV/TOL/MAR budget. The nucleon level is already fixed by
`PMElementaryParticles.CompositeMasses` (`m_p`, `m_n` include all six pillars).

This module makes the tower explicit:

`latticeSum Z N = Z m_p + N m_n + Z m_e`
`boundMass Z N bN bA = latticeSum Z N − bN.contribution − bA.contribution`

so the periodic-table gap is exactly the nucleus-level plus atom-level budget.
The numeric values of those budgets are **not** invented here; they are the
open E8 calculation.
-/

noncomputable section
namespace PMAtoms
open PMElementaryParticles.CompositeMasses

/-- Levels of the persistence tower. -/
inductive Level
  | particle | nucleon | nucleus | atom
  deriving DecidableEq, Repr

/-- A level's six-pillar contribution. For the **mass** ledger, toll, margin and
shared links are positive cost magnitudes and are subtracted from the bound mass.
(The α⁻¹ impedance ledger uses different signs; the sign is system-dependent.) -/
structure LevelBudget where
  level : Level
  toll : ℝ := 0
  margin : ℝ := 0
  sharedLinks : ℝ := 0

def LevelBudget.contribution (b : LevelBudget) : ℝ :=
  b.toll + b.margin + b.sharedLinks

/-- Free-constituent lattice sum. -/
def latticeSum (z n : ℕ) : ℝ :=
  (z : ℝ) * proton + (n : ℝ) * neutron + (z : ℝ) * 1

/-- Bound mass after the nucleus- and atom-level budgets. -/
def boundMass (z n : ℕ) (nucleusBudget atomBudget : LevelBudget) : ℝ :=
  latticeSum z n - nucleusBudget.contribution - atomBudget.contribution

/-- **The periodic-table gap is exactly the nucleus + atom level budget.** -/
theorem gap_eq_level_budgets (z n : ℕ) (bN bA : LevelBudget) :
    latticeSum z n - boundMass z n bN bA = bN.contribution + bA.contribution := by
  unfold boundMass
  ring

/-- A nucleus with no level budget is the free lattice sum. -/
theorem boundMass_zero (z n : ℕ) :
    boundMass z n ⟨.nucleus, 0, 0, 0⟩ ⟨.atom, 0, 0, 0⟩ = latticeSum z n := by
  simp [boundMass, LevelBudget.contribution]

/-- Only the nucleus level is needed when the atom-level mass is negligible. -/
theorem gap_eq_nucleus_budget (z n : ℕ) (bN : LevelBudget) :
    latticeSum z n - boundMass z n bN ⟨.atom, 0, 0, 0⟩ = bN.contribution := by
  rw [gap_eq_level_budgets]
  simp [LevelBudget.contribution]

end PMAtoms
