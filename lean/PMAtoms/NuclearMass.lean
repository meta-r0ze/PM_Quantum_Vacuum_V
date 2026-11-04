import PMAtoms.Nucleus
import PMElementaryParticles.CompositeMasses
import Mathlib.Tactic

/-!
# Nuclear persistence from the E8 lattice mass

In this framework "binding" is not a separate SM potential: the mass is the
lattice/information readout, and a nucleus persists when no allowed decay channel
lowers that lattice mass. This module makes that criterion explicit:

`latticeMass (Z,N) = Z m_p + N m_n`,
`PersistsMass n = ∀ ns ls, Decay n ns ls → latticeMass n ≤ Σ latticeMass ns`.

Consequences from the certified masses:

* `latticeMass_betaMinus_lt`: `n → p e ν̄` lowers the lattice mass because
  `m_n > m_p`, so any nuclide with `N > 0` fails `PersistsMass`.
* `alpha_mass_eq`, `fission_mass_eq`: `α` and fission conserve the lattice mass
  (they conserve `A`), so they do not by themselves break persistence.

The full persistence criterion also needs the channel rate/selection; the
mass-only criterion is the first E8 layer, not the whole story.
-/

noncomputable section
namespace PMAtoms

open PMElementaryParticles.CompositeMasses

/-- E8 lattice mass: `Z` proton masses plus `N` neutron masses, in `m_e` units. -/
def latticeMass (n : Nuclide) : ℝ :=
  (n.Z : ℝ) * proton + (n.N : ℝ) * neutron

def totalLatticeMass (ns : List Nuclide) : ℝ := (ns.map latticeMass).sum

/-- A nucleus persists under the mass criterion when no allowed channel lowers
the total E8 lattice mass. -/
def PersistsMass (n : Nuclide) : Prop :=
  ∀ ns ls, Decay n ns ls → latticeMass n ≤ totalLatticeMass ns

/-- **`β⁻` lowers the lattice mass**: a neutron is heavier than a proton, so
`n → p` drops the lattice mass. -/
theorem latticeMass_betaMinus_lt (n : Nuclide) (hN : 0 < n.N) :
    latticeMass (betaMinus n) < latticeMass n := by
  have hp := proton_value
  have hn := neutron_value
  have hcast : ((n.N - 1 : ℕ) : ℝ) = (n.N : ℝ) - 1 := by
    rw [Nat.cast_sub (by exact_mod_cast hN)]; norm_num
  simp [latticeMass, betaMinus, hcast]
  nlinarith [hp.2, hn.1]

/-- Any nuclide with a neutron fails the mass-persistence criterion. -/
theorem not_persistsMass_of_neutron (n : Nuclide) (hN : 0 < n.N) :
    ¬ PersistsMass n := by
  intro h
  have hdec := betaMinus_decay n hN
  have hle := h _ _ hdec
  have hlt := latticeMass_betaMinus_lt n hN
  simp [totalLatticeMass] at hle
  linarith

/-- **`α` decay conserves the lattice mass** (it conserves `A`). -/
theorem alpha_mass_eq (n : Nuclide) (hZ : 2 ≤ n.Z) (hN : 2 ≤ n.N) :
    latticeMass n = latticeMass (alphaDaughter n) + latticeMass alpha := by
  have hZ' : ((n.Z - 2 : ℕ) : ℝ) = (n.Z : ℝ) - 2 := by
    rw [Nat.cast_sub hZ]; norm_num
  have hN' : ((n.N - 2 : ℕ) : ℝ) = (n.N : ℝ) - 2 := by
    rw [Nat.cast_sub hN]; norm_num
  simp [latticeMass, alphaDaughter, alpha, hZ', hN']
  ring

/-- **Fission conserves the lattice mass** (it conserves `Z` and `N`). -/
theorem fission_mass_eq (n n₁ n₂ : Nuclide)
    (hZ : n₁.Z + n₂.Z = n.Z) (hN : n₁.N + n₂.N = n.N) :
    latticeMass n = latticeMass n₁ + latticeMass n₂ := by
  have hZ' : (n.Z : ℝ) = (n₁.Z : ℝ) + (n₂.Z : ℝ) := by
    rw [← hZ]; push_cast; ring
  have hN' : (n.N : ℝ) = (n₁.N : ℝ) + (n₂.N : ℝ) := by
    rw [← hN]; push_cast; ring
  simp [latticeMass, hZ', hN']
  ring

end PMAtoms
