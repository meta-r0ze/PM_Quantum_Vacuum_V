import PMAtoms.NuclearGraph
import PMAtoms.Invariants
import Mathlib.Tactic

/-!
# Nucleon coordination: 3 hetero + 1 homo channel

The substrate link capacity is 4. Split it as

* 3 **hetero** channels (connect to the other species),
* 1 **homo** channel (connect to the same species).

So a proton has at most `3 pn` links plus `1 pp` link; a neutron has at most
`3 pn` links plus `1 nn` link. This yields:

* one proton → at most 3 neutrons;
* two protons → one `pp` link plus at most 6 neutrons.

The light-nucleus data (H-2, H-3, He-3, He-4) sit inside these bounds and He-4 is
the first to use 3 of the 4 channels on every nucleon.
-/

namespace PMAtoms

/-- Total hetero (pn) capacity for `z` protons. -/
def pnCapacity (z : Nat) : Nat := 3 * z

/-- Total homo (pp or nn) capacity for `z` like nucleons. -/
def homoCapacity (z : Nat) : Nat := z / 2

/-- E8 form of the hetero capacity: `(σ−χ) pn` channels per proton. -/
def pnCapacityE8 (z : Nat) : Nat := (σ - χ) * z

/-- E8 form of the homo capacity: one `pp`/`nn` link per `χ` nucleons. -/
def homoCapacityE8 (z : Nat) : Nat := z / χ

theorem pnCapacityE8_eq (z : Nat) : pnCapacityE8 z = pnCapacity z := by
  simp [pnCapacityE8, pnCapacity, colour_axes]

theorem homoCapacityE8_eq (z : Nat) : homoCapacityE8 z = homoCapacity z := by
  simp [homoCapacityE8, homoCapacity, homo_pair]

/-- Deuterium: one proton, one neutron. -/
def dLabel : Fin 2 → NucleonLabel := fun i => if i = 0 then .proton else .neutron

theorem deuteron_counts :
    completeEdgeCount dLabel .pp = 0 ∧
      completeEdgeCount dLabel .pn = 1 ∧
      completeEdgeCount dLabel .nn = 0 := by
  decide

/-- One proton can host at most three `pn` links. -/
theorem one_proton_max_neutrons : pnCapacity 1 = 3 := by
  norm_num [pnCapacity]

/-- Two protons give one `pp` link and at most six `pn` links. -/
theorem two_proton_max_neutrons : pnCapacity 2 = 6 ∧ homoCapacity 2 = 1 := by
  norm_num [pnCapacity, homoCapacity]

/-- H-3 fits the 3+1 channel split. -/
theorem h3_within_capacity :
    completeEdgeCount h3Label .pp ≤ homoCapacity 1 ∧
      completeEdgeCount h3Label .pn ≤ pnCapacity 1 ∧
      completeEdgeCount h3Label .nn ≤ homoCapacity 2 := by
  decide

/-- He-3 fits the 3+1 channel split. -/
theorem he3_within_capacity :
    completeEdgeCount he3Label .pp ≤ homoCapacity 2 ∧
      completeEdgeCount he3Label .pn ≤ pnCapacity 1 ∧
      completeEdgeCount he3Label .nn ≤ homoCapacity 1 := by
  decide

/-- He-4 fits the 3+1 channel split (two `pn` plus one homo per species). -/
theorem he4_within_capacity :
    completeEdgeCount he4Label .pp ≤ homoCapacity 2 ∧
      completeEdgeCount he4Label .pn ≤ pnCapacity 2 ∧
      completeEdgeCount he4Label .nn ≤ homoCapacity 2 := by
  decide

/-- He-4 uses 3 of the 4 channels on every nucleon (K4 tetrahedron). -/
theorem he4_uses_three_channels :
    PMAtoms.neighborCount PMAtoms.tetrahedron 0 = 3 := by
  exact PMAtoms.tetrahedron_neighbors 0

end PMAtoms
