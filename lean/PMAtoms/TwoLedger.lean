import PMAtoms.LinkWeights
import PMAtoms.NuclearLine
import PMAtoms.NuclearFolding
import PMElementaryParticles.CompositeMasses
import Mathlib.Tactic

/-!
# Two-ledger nuclear mass

`M(Z,N) = free nucleons − link binding + charge repulsion`.

The link weights carry a charge asymmetry `±c/2` around the map weight `πD`, and
the charge ledger carries `c = πD/(2σ)` per proton pair. The asymmetry and the
charge term cancel in the H-3/He-3 mirror, leaving exactly the free
neutron−proton−electron difference. So the mirror is a cancellation, not a
Coulomb measurement.
-/

noncomputable section
namespace PMAtoms
open PMElementaryParticles.CompositeMasses

/-- Charge coupling `c = πD/(2σ)`. -/
def chargeCoupling : ℝ := Real.pi * (D : ℝ) / (2 * (σ : ℝ))

theorem chargeCoupling_eq_e8 : chargeCoupling = e8ChargeCoupling := rfl

theorem chargeCoupling_eq : chargeCoupling = Real.pi * 4 / 10 := by
  simp [chargeCoupling, D, σ, PMSubstrate.baseline]
  norm_num

/-- Link weights for the mass ledger: `pp = πD + c/2`, `pn = πD`, `nn = πD − c/2`. -/
def massLinkWeight : LinkType → ℝ
  | .pp => mapWeight + chargeCoupling / 2
  | .pn => mapWeight
  | .nn => mapWeight - chargeCoupling / 2

/-- Number of proton pairs. -/
def chargePairs (z : Nat) : ℝ := ((z * (z - 1) / 2 : Nat) : ℝ)

/-- Charge ledger: `c` per proton pair. -/
def chargeTerm (z : Nat) : ℝ := chargePairs z * chargeCoupling

/-- Binding from an explicit `(pp,pn,nn)` count triple. -/
def bindingFromCounts (wpp wpn wnn : ℝ) (c : Nat × Nat × Nat) : ℝ :=
  wpp * (c.1 : ℝ) + wpn * (c.2.1 : ℝ) + wnn * (c.2.2 : ℝ)

/-- Link ledger: line/ring binding with the mass link weights. -/
def massBinding (z n : Nat) : ℝ :=
  bindingFromCounts (massLinkWeight .pp) (massLinkWeight .pn) (massLinkWeight .nn)
    (lineCounts z n)

/-- Capped link ledger: homo channels saturate at `Z/2`, `N/2`. -/
def cappedMassBinding (z n : Nat) : ℝ :=
  bindingFromCounts (massLinkWeight .pp) (massLinkWeight .pn) (massLinkWeight .nn)
    (cappedLineCounts z n)

/-- **Two-ledger nuclear mass** in `m_e` units (neutral atom). -/
def nuclearMass (z n : Nat) : ℝ :=
  (z : ℝ) * proton + (n : ℝ) * neutron + (z : ℝ) -
    massBinding z n + chargeTerm z

/-- Capped two-ledger mass, with the homo-channel saturation. -/
def nuclearMassCapped (z n : Nat) : ℝ :=
  (z : ℝ) * proton + (n : ℝ) * neutron + (z : ℝ) -
    cappedMassBinding z n + chargeTerm z

/-- Explicit decomposition into free, link, and charge ledgers. -/
theorem nuclearMass_decomp (z n : Nat) :
    nuclearMass z n =
      ((z : ℝ) * proton + (n : ℝ) * neutron + (z : ℝ)) -
        massBinding z n + chargeTerm z := rfl

theorem chargeTerm_zero : chargeTerm 0 = 0 := by
  simp [chargeTerm, chargePairs]

theorem chargeTerm_one : chargeTerm 1 = 0 := by
  simp [chargeTerm, chargePairs]

theorem chargeTerm_two : chargeTerm 2 = chargeCoupling := by
  simp [chargeTerm, chargePairs, chargeCoupling]

theorem chargeTerm_nonneg (z : Nat) : 0 ≤ chargeTerm z := by
  unfold chargeTerm chargePairs
  have hc : 0 ≤ chargeCoupling := by
    unfold chargeCoupling
    positivity
  positivity

/-- **Mirror cancellation.** The link asymmetry and the charge term cancel, so
`M(H-3) − M(He-3) = m_n − m_p − m_e`. -/
theorem mirror_h3_he3 :
    nuclearMass 1 2 - nuclearMass 2 1 = neutron - proton - 1 := by
  unfold nuclearMass massBinding massLinkWeight bindingFromCounts
  rw [lineCounts_h3, lineCounts_he3]
  simp [chargeTerm_one, chargeTerm_two]
  ring

/-- The mirror difference is exactly the free neutron−proton−electron gap. -/
theorem mirror_is_free :
    nuclearMass 1 2 - nuclearMass 2 1 = neutron - proton - 1 :=
  mirror_h3_he3

/-- The cap is inactive for H-3. -/
theorem cappedLineCounts_h3 : cappedLineCounts 1 2 = lineCounts 1 2 := by
  decide

/-- The cap is inactive for He-3. -/
theorem cappedLineCounts_he3 : cappedLineCounts 2 1 = lineCounts 2 1 := by
  decide

theorem cappedMassBinding_h3 : cappedMassBinding 1 2 = massBinding 1 2 := by
  unfold cappedMassBinding massBinding
  rw [cappedLineCounts_h3]

theorem cappedMassBinding_he3 : cappedMassBinding 2 1 = massBinding 2 1 := by
  unfold cappedMassBinding massBinding
  rw [cappedLineCounts_he3]

theorem nuclearMassCapped_h3 : nuclearMassCapped 1 2 = nuclearMass 1 2 := by
  unfold nuclearMassCapped nuclearMass
  rw [cappedMassBinding_h3]

theorem nuclearMassCapped_he3 : nuclearMassCapped 2 1 = nuclearMass 2 1 := by
  unfold nuclearMassCapped nuclearMass
  rw [cappedMassBinding_he3]

/-- **Capped mirror cancellation**: the saturation does not disturb the H-3/He-3
cancellation. -/
theorem mirror_h3_he3_capped :
    nuclearMassCapped 1 2 - nuclearMassCapped 2 1 = neutron - proton - 1 := by
  rw [nuclearMassCapped_h3, nuclearMassCapped_he3]
  exact mirror_h3_he3

end PMAtoms
