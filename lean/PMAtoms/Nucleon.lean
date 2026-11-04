import Mathlib.Tactic
import PMElementaryParticles.SubstrateLedger
import PMAtoms.Shells
import PMConstants.BaryonNumber

/-!
# What a proton system and a neutron system are

A nucleon is assembled from the substrate, not asserted: take the three colour
axes that survive after singling out the lepton axis
(`SubstrateLedger.colour_axes_exist`), put one up/down base protocol on each
axis (`slotChannel`), and read charge with Paper III's generator
(`ChargeProtocols.Q`). Summing the three slots gives the proton (`uud`, `+1`) or
neutron (`udd`, `0`); summing `BaryonNumber.axisB` over the three colour axes
gives baryon number `1`. Spin `1/2` supplies the two states, and lepton number is
`0` because no lepton axis is occupied.

The equality `Q_slotChannel` is the key bridge: the substrate charge generator on
the actual channel equals the quark charge. `charge_eq_channels` then says a
nucleon's charge is literally the sum of three substrate channel charges, and
`baryon_from_three_colours` says the three colour axes carry baryon `1`.

Nothing here postulates a nuclear force or binding energy; this module fixes the
charge/baryon/colour/isospin content of the two nucleon systems. The proton and
neutron masses are compared separately through `proton_ratio`/`neutron_ratio` in
`e8p`.
-/

namespace PMAtoms

/-- The three colour slots of a confined quark system. -/
inductive Colour
  | red | green | blue
  deriving DecidableEq, Repr

/-- Up and down quarks, the only flavours a nucleon uses. -/
inductive Quark
  | up | down
  deriving DecidableEq, Repr

namespace Quark

def charge : Quark → ℚ
  | .up => 2 / 3
  | .down => -1 / 3

def baryon : Quark → ℚ
  | _ => 1 / 3

/-- The Paper V protocol corresponding to a quark flavour. -/
def toProtocol : Quark → PMElementaryParticles.ProtocolInventory.BaseProtocol
  | .up => .up
  | .down => .down

/-- The quark charge is exactly Paper V's protocol charge. -/
theorem charge_eq_protocol (q : Quark) :
    charge q = PMElementaryParticles.ProtocolDynamics.baseCharge (toProtocol q) := by
  cases q <;> norm_num [charge, toProtocol, PMElementaryParticles.ProtocolDynamics.baseCharge]

end Quark

/-- The two base nucleon systems. -/
inductive Nucleon
  | proton | neutron
  deriving DecidableEq, Repr

namespace Nucleon

/-- Quark content by colour slot: proton `uud`, neutron `udd`. -/
def content : Nucleon → Fin 3 → Quark
  | .proton => fun i => if i = 2 then .down else .up
  | .neutron => fun i => if i = 0 then .up else .down

/-- The same content as a list, for display/lemmas. -/
def contentList (n : Nucleon) : List Quark := [content n 0, content n 1, content n 2]

/-- Confinement uses one quark of each colour. -/
def colourContent : List Colour := [.red, .green, .blue]

/-- Charge summed over the three colour slots. -/
def charge (n : Nucleon) : ℚ := ∑ i : Fin 3, Quark.charge (content n i)

/-- Baryon number summed over the three colour slots. -/
def baryon (n : Nucleon) : ℚ := ∑ i : Fin 3, Quark.baryon (content n i)

/-- The actual substrate channel for colour slot `i` holding flavour `q`. -/
def slotChannel (i : Fin 3) (q : Quark) : PMConstants.PacketGaugeActions.Channels :=
  .inl (i, if q = .up then 0 else 1)

/-- **The substrate charge generator agrees with the quark charge on each slot.** -/
theorem Q_slotChannel (i : Fin 3) (q : Quark) :
    PMElementaryParticles.ChargeProtocols.Q (slotChannel i q) = (Quark.charge q : ℂ) := by
  cases q <;> simp [slotChannel, PMElementaryParticles.ChargeProtocols.Q_eval, Quark.charge]

/-- **A nucleon's charge is the sum of three actual substrate channel charges.** -/
theorem charge_eq_channels (n : Nucleon) :
    (∑ i : Fin 3, (Quark.charge (content n i) : ℂ)) =
      ∑ i : Fin 3, PMElementaryParticles.ChargeProtocols.Q (slotChannel i (content n i)) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [Q_slotChannel]

/-- **Three colour slots give baryon number one**: each colour axis carries `1/3`. -/
theorem baryon_from_three_colours :
    (∑ i : Fin 3, PMConstants.BaryonNumber.axisB (Fin.succ i)) = 1 := by
  simp [PMConstants.BaryonNumber.axisB, Fin.succ_ne_zero]

theorem colour_singlet_slots : (Finset.univ : Finset (Fin 3)).card = 3 := rfl

/-- Two spin states per nucleon, inherited from the PM-2 chiral projector. -/
def spinStates : ℕ := PMAtoms.spinStates

/-- Third component of isospin. -/
def isospin3 : Nucleon → ℚ
  | .proton => 1 / 2
  | .neutron => -1 / 2

/-- The Paper V protocols occupied by a nucleon (three confined quarks). -/
def protocols (n : Nucleon) : List PMElementaryParticles.ProtocolInventory.BaseProtocol :=
  (contentList n).map Quark.toProtocol

theorem proton_quarks : contentList .proton = [.up, .up, .down] := by
  simp [contentList, content]

theorem neutron_quarks : contentList .neutron = [.up, .down, .down] := by
  simp [contentList, content]

theorem proton_charge : charge .proton = 1 := by
  simp [charge, content, Quark.charge, Fin.sum_univ_three]
  norm_num

theorem neutron_charge : charge .neutron = 0 := by
  simp [charge, content, Quark.charge, Fin.sum_univ_three]
  norm_num

theorem baryon_one (n : Nucleon) : baryon n = 1 := by
  cases n <;> simp [baryon, Quark.baryon]

theorem colour_length : colourContent.length = 3 := rfl

theorem spin_states : spinStates = 2 := rfl

theorem isospin_gap : isospin3 .proton - isospin3 .neutron = 1 := by
  norm_num [isospin3]

theorem proton_neutron_distinct : Nucleon.proton ≠ Nucleon.neutron := by decide

theorem charge_gap : charge .proton - charge .neutron = 1 := by
  rw [proton_charge, neutron_charge]; norm_num

theorem protocols_length (n : Nucleon) : (protocols n).length = 3 := by
  cases n <;> rfl

end Nucleon

/-- A nucleon together with its spin state: the basic system placed in a nucleus. -/
structure NucleonSystem where
  nucleon : Nucleon
  spin : Fin 2
  deriving DecidableEq, Repr

/-- A proton system: any spin state of the `uud` nucleon. -/
abbrev ProtonSystem := { s : NucleonSystem // s.nucleon = .proton }

/-- A neutron system: any spin state of the `udd` nucleon. -/
abbrev NeutronSystem := { s : NucleonSystem // s.nucleon = .neutron }

end PMAtoms
