import PMElementaryParticles.ProtocolDynamics
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Candidate cohorts from the protocol ledger

Finite cohort generation from the 16 protocol states, plus the weak-doublet
partner constraint. The multiplicity-preserving list model lives in
`PMAtoms.ListCohorts`.
-/

namespace PMAtoms

open PMElementaryParticles.ProtocolDynamics

/-- The four base protocols. -/
def baseProtocols : List PMElementaryParticles.ProtocolInventory.BaseProtocol :=
  [PMElementaryParticles.ProtocolInventory.BaseProtocol.electron,
   PMElementaryParticles.ProtocolInventory.BaseProtocol.up,
   PMElementaryParticles.ProtocolInventory.BaseProtocol.down,
   PMElementaryParticles.ProtocolInventory.BaseProtocol.neutrino]

/-- All 16 protocol states. -/
def allStates : Finset State :=
  baseProtocols.toFinset.product (Finset.univ : Finset Tier)

def cohortChargeF (C : Finset State) : ℚ := C.sum (fun s => baseCharge s.1)

def lowerStates (p : State) : Finset State :=
  allStates.filter (fun s => decide (s.2 < p.2))

noncomputable def candidateCohorts (p : State) : Finset (Finset State) := by
  classical
  exact (lowerStates p).powerset.filter
    (fun C => C.Nonempty ∧ cohortChargeF C = baseCharge p.1)

theorem muon_cohort_mem :
    ({(.electron, ⟨0, by decide⟩), (.neutrino, ⟨0, by decide⟩),
      (.neutrino, ⟨0, by decide⟩)} : Finset State)
      ∈ candidateCohorts (.electron, ⟨1, by decide⟩) := by
  simp [candidateCohorts, lowerStates, allStates, baseProtocols, cohortChargeF, baseCharge]
  decide

theorem electron_singleton_mem :
    ({(.electron, ⟨0, by decide⟩)} : Finset State)
      ∈ candidateCohorts (.electron, ⟨1, by decide⟩) := by
  simp [candidateCohorts, lowerStates, allStates, baseProtocols, cohortChargeF, baseCharge]

/-- Weak doublet partner: electron↔neutrino, up↔down. -/
def weakPartner : PMElementaryParticles.ProtocolInventory.BaseProtocol → PMElementaryParticles.ProtocolInventory.BaseProtocol
  | .electron => .neutrino
  | .neutrino => .electron
  | .up => .down
  | .down => .up

def hasWeakPartner (p : State) (C : Finset State) : Prop :=
  ∃ d ∈ C, d.1 = weakPartner p.1

noncomputable def candidateCohortsWeak (p : State) : Finset (Finset State) := by
  classical
  exact (candidateCohorts p).filter (fun C => hasWeakPartner p C)

theorem muon_cohort_weak :
    ({(.electron, ⟨0, by decide⟩), (.neutrino, ⟨0, by decide⟩),
      (.neutrino, ⟨0, by decide⟩)} : Finset State)
      ∈ candidateCohortsWeak (.electron, ⟨1, by decide⟩) := by
  simp [candidateCohortsWeak, hasWeakPartner, weakPartner, candidateCohorts, lowerStates,
    allStates, baseProtocols, cohortChargeF, baseCharge]
  decide

theorem electron_singleton_not_weak :
    ({(.electron, ⟨0, by decide⟩)} : Finset State)
      ∉ candidateCohortsWeak (.electron, ⟨1, by decide⟩) := by
  simp [candidateCohortsWeak, hasWeakPartner, weakPartner]

def cohortCost (C : Finset State) : ℝ := C.card

theorem exists_least_cohort_cost (p : State) (h : (candidateCohorts p).Nonempty) :
    ∃ best ∈ candidateCohorts p,
      ∀ C ∈ candidateCohorts p, cohortCost best ≤ cohortCost C :=
  (candidateCohorts p).exists_min_image cohortCost h

end PMAtoms
