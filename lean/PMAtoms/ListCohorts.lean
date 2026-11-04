import PMElementaryParticles.ProtocolDynamics
import Mathlib.Tactic

/-!
# Multiplicity-preserving cohorts

A `Finset` loses multiplicity, so `e ν ν̄` becomes `{e,ν}`. This module uses a
`List State`, kept computable, so the two-neutrino exit is a three-element cohort.
Constraints come only from the protocol ledger: nonempty, lower tier, conserved
charge, odd fermion number (half-integer total spin), and a weak-doublet partner.
No Standard-Model input is used.
-/

namespace PMAtoms

open PMElementaryParticles.ProtocolDynamics

def baseProtocolsList : List PMElementaryParticles.ProtocolInventory.BaseProtocol :=
  [PMElementaryParticles.ProtocolInventory.BaseProtocol.electron,
   PMElementaryParticles.ProtocolInventory.BaseProtocol.up,
   PMElementaryParticles.ProtocolInventory.BaseProtocol.down,
   PMElementaryParticles.ProtocolInventory.BaseProtocol.neutrino]

def tiersList : List Tier :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩]

def allStatesList : List State :=
  baseProtocolsList.flatMap (fun b => tiersList.map (fun t => (b, t)))

def weakPartnerList : PMElementaryParticles.ProtocolInventory.BaseProtocol → PMElementaryParticles.ProtocolInventory.BaseProtocol
  | .electron => .neutrino
  | .neutrino => .electron
  | .up => .down
  | .down => .up

/-- Charge in thirds, as an integer (`up=2`, `down=-1`, `e=-3`, `ν=0`). -/
def charge3 : PMElementaryParticles.ProtocolInventory.BaseProtocol → Int
  | .up => 2
  | .down => -1
  | .electron => -3
  | .neutrino => 0

def listCharge3 (l : List State) : Int := (l.map (fun d => charge3 d.1)).sum

def listsOfLength (xs : List State) : Nat → List (List State)
  | 0 => [[]]
  | k + 1 => (listsOfLength xs k).flatMap (fun l => xs.map (fun x => l ++ [x]))

/-- Candidate lists (multiplicity preserved). -/
def candidateLists (p : State) : List (List State) :=
  let below := allStatesList.filter (fun s => decide (s.2 < p.2))
  (List.range 4).flatMap (fun k => listsOfLength below k) |>.filter (fun l =>
    !l.isEmpty &&
      decide (listCharge3 l = charge3 p.1) &&
      (l.length % 2 == 1) &&
      l.any (fun d => d.1 == weakPartnerList p.1))

theorem muon_list_mem :
    ([(.electron, ⟨0, by decide⟩), (.neutrino, ⟨0, by decide⟩),
      (.neutrino, ⟨0, by decide⟩)] : List State)
      ∈ candidateLists (.electron, ⟨1, by decide⟩) := by
  decide

theorem electron_list_not :
    ([(.electron, ⟨0, by decide⟩)] : List State)
      ∉ candidateLists (.electron, ⟨1, by decide⟩) := by
  decide

theorem electron_neutrino_list_not :
    ([(.electron, ⟨0, by decide⟩), (.neutrino, ⟨0, by decide⟩)] : List State)
      ∉ candidateLists (.electron, ⟨1, by decide⟩) := by
  decide

def listCost (l : List State) : ℝ := l.length

end PMAtoms
