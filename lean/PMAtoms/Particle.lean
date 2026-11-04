import PMElementaryParticles.CompositeMasses
import PMElementaryParticles.LeptonMasses
import Mathlib.Tactic

/-!
# Composite particles: what persists, and what decays

This is the generic decay ledger above `Nucleon`/`Nucleus`/`Atom`. A species has
a certified mass (in electron-mass units), charge, baryon number and lepton
number. A decay is a nonempty product list with conserved `Q`, `B`, `L` and a
strictly smaller total mass. `Stable` means no such channel exists.

The interesting content is not the definition but the mass comparisons: `β⁻`
decay of the neutron, muon decay, charged-pion decay and tau decay are all
kinematically allowed by the **certified** mass enclosures. Stability of the
proton is a baryon-number statement, not a mass coincidence.
-/

noncomputable section
namespace PMAtoms

open PMElementaryParticles.CompositeMasses PMElementaryParticles.LeptonMasses

/-- Species with a certified mass in `m_e` units and the three conserved
quantum numbers used by the substrate ledger. -/
inductive Species
  | proton | neutron | electron | positron | neutrino | antineutrino
  | muon | antimuon | tau | pion0 | pionPlus | kaon0 | kaonPlus
  deriving DecidableEq, Repr

namespace Species

/-- Mass in electron-mass units. Neutrinos are massless in this ledger. -/
def mass : Species → ℝ
  | .proton => PMElementaryParticles.CompositeMasses.proton
  | .neutron => PMElementaryParticles.CompositeMasses.neutron
  | .electron => 1
  | .positron => 1
  | .neutrino => 0
  | .antineutrino => 0
  | .muon => PMElementaryParticles.LeptonMasses.muon
  | .antimuon => PMElementaryParticles.LeptonMasses.muon
  | .tau => PMElementaryParticles.LeptonMasses.tau
  | .pion0 => PMElementaryParticles.CompositeMasses.pion0
  | .pionPlus => PMElementaryParticles.LeptonMasses.pionPlus
  | .kaon0 => PMElementaryParticles.CompositeMasses.kaon0
  | .kaonPlus => PMElementaryParticles.CompositeMasses.kaonPlus

def charge : Species → ℚ
  | .proton => 1
  | .neutron => 0
  | .electron => -1
  | .positron => 1
  | .neutrino => 0
  | .antineutrino => 0
  | .muon => -1
  | .antimuon => 1
  | .tau => -1
  | .pion0 => 0
  | .pionPlus => 1
  | .kaon0 => 0
  | .kaonPlus => 1

def baryon : Species → ℚ
  | .proton => 1
  | .neutron => 1
  | _ => 0

def lepton : Species → ℚ
  | .electron => 1
  | .positron => -1
  | .neutrino => 1
  | .antineutrino => -1
  | .muon => 1
  | .antimuon => -1
  | .tau => 1
  | _ => 0

end Species

def pCharge (ds : List Species) : ℚ := (ds.map Species.charge).sum
def pBaryon (ds : List Species) : ℚ := (ds.map Species.baryon).sum
def pLepton (ds : List Species) : ℚ := (ds.map Species.lepton).sum
def pMass (ds : List Species) : ℝ := (ds.map Species.mass).sum

/-- A decay is kinematically allowed when charge, baryon and lepton number are
conserved and the products are lighter than the parent. -/
def ParticleDecay (p : Species) (ds : List Species) : Prop :=
  ds ≠ [] ∧ pCharge ds = p.charge ∧ pBaryon ds = p.baryon ∧
    pLepton ds = p.lepton ∧ pMass ds < p.mass

/-- A species persists when no allowed decay channel exists. -/
def Stable (p : Species) : Prop := ∀ ds, ¬ ParticleDecay p ds

theorem stable_of_no_channel (p : Species) (h : ∀ ds, ¬ ParticleDecay p ds) : Stable p := h

theorem decay_charge {p : Species} {ds : List Species} (h : ParticleDecay p ds) :
    pCharge ds = p.charge := h.2.1

theorem decay_baryon {p : Species} {ds : List Species} (h : ParticleDecay p ds) :
    pBaryon ds = p.baryon := h.2.2.1

theorem decay_lepton {p : Species} {ds : List Species} (h : ParticleDecay p ds) :
    pLepton ds = p.lepton := h.2.2.2.1

theorem decay_lighter {p : Species} {ds : List Species} (h : ParticleDecay p ds) :
    pMass ds < p.mass := h.2.2.2.2

theorem mass_nonneg : ∀ s : Species, 0 ≤ s.mass
  | .proton => le_of_lt (by simp [Species.mass]; linarith [PMElementaryParticles.CompositeMasses.proton_value.1])
  | .neutron => le_of_lt (by simp [Species.mass]; linarith [PMElementaryParticles.CompositeMasses.neutron_value.1])
  | .electron => by norm_num [Species.mass]
  | .positron => by norm_num [Species.mass]
  | .neutrino => by norm_num [Species.mass]
  | .antineutrino => by norm_num [Species.mass]
  | .muon => le_of_lt (by simp [Species.mass]; linarith [PMElementaryParticles.LeptonMasses.muon_value.1])
  | .antimuon => le_of_lt (by simp [Species.mass]; linarith [PMElementaryParticles.LeptonMasses.muon_value.1])
  | .tau => by simp [Species.mass, PMElementaryParticles.LeptonMasses.tau_value]
  | .pion0 => le_of_lt PMElementaryParticles.CompositeMasses.pion0_pos
  | .pionPlus => le_of_lt (by simp [Species.mass]; linarith [PMElementaryParticles.LeptonMasses.pionPlus_value.1])
  | .kaon0 => le_of_lt PMElementaryParticles.CompositeMasses.kaon0_pos
  | .kaonPlus => le_of_lt PMElementaryParticles.CompositeMasses.kaonPlus_pos

theorem baryon_nonneg (s : Species) : 0 ≤ s.baryon := by
  cases s <;> norm_num [Species.baryon]

theorem baryon_pos_cases {s : Species} (h : 0 < s.baryon) :
    s = .proton ∨ s = .neutron := by
  cases s <;> simp [Species.baryon] at h ⊢

lemma exists_pos_of_sum_pos : ∀ (ds : List Species),
    0 < pBaryon ds → ∃ d ∈ ds, 0 < Species.baryon d
  | [], h => by simp [pBaryon] at h
  | a :: as, h => by
      by_cases ha : 0 < Species.baryon a
      · exact ⟨a, by simp, ha⟩
      · have has : 0 < pBaryon as := by
          simp [pBaryon] at h ⊢
          have := baryon_nonneg a
          linarith
        obtain ⟨d, hd, hdpos⟩ := exists_pos_of_sum_pos as has
        exact ⟨d, by simp [hd], hdpos⟩

lemma le_pMass_of_mem (d : Species) : ∀ (ds : List Species), d ∈ ds → d.mass ≤ pMass ds
  | [], hd => by simp at hd
  | a :: as, hd => by
      rw [pMass]
      simp only [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp hd with rfl | hd'
      · have := List.sum_nonneg (l := as.map Species.mass)
          (fun x hx => by
            obtain ⟨s, -, rfl⟩ := List.mem_map.mp hx
            exact mass_nonneg s)
        linarith
      · have ih := le_pMass_of_mem d as hd'
        rw [pMass] at ih
        have := mass_nonneg a
        linarith

/-- **The proton does not decay.** Any channel with total baryon number one must
contain a proton or neutron; both weigh at least the proton, and all other
products have nonnegative mass, so the products cannot be lighter. -/
theorem proton_stable : Stable .proton := by
  intro ds hdec
  have hB : pBaryon ds = 1 := by
    rw [decay_baryon hdec]
    norm_num [Species.baryon]
  have hpos : 0 < pBaryon ds := by rw [hB]; norm_num
  obtain ⟨d, hd, hdpos⟩ := exists_pos_of_sum_pos ds hpos
  have hdcase := baryon_pos_cases hdpos
  have hdge : Species.mass .proton ≤ d.mass := by
    rcases hdcase with rfl | rfl
    · exact le_rfl
    · have hp := PMElementaryParticles.CompositeMasses.proton_value
      have hn := PMElementaryParticles.CompositeMasses.neutron_value
      simp [Species.mass]
      linarith
  have hle : Species.mass .proton ≤ pMass ds :=
    le_trans hdge (le_pMass_of_mem d ds hd)
  have hlt := decay_lighter hdec
  linarith

/-- **Neutron `β⁻` decay is allowed**: `n → p e ν̄`, with
`m_p + m_e < m_n` from the certified mass enclosures. -/
theorem neutron_beta :
    ParticleDecay .neutron [.proton, .electron, .antineutrino] := by
  have hp := PMElementaryParticles.CompositeMasses.proton_value
  have hn := PMElementaryParticles.CompositeMasses.neutron_value
  refine ⟨by simp, ?_, ?_, ?_, ?_⟩
  · norm_num [pCharge, Species.charge]
  · norm_num [pBaryon, Species.baryon]
  · norm_num [pLepton, Species.lepton]
  · simp [pMass, Species.mass]
    linarith

/-- **Muon decay is allowed**: `μ → e ν ν̄`. -/
theorem muon_decay :
    ParticleDecay .muon [.electron, .neutrino, .antineutrino] := by
  have hm := PMElementaryParticles.LeptonMasses.muon_value
  refine ⟨by simp, ?_, ?_, ?_, ?_⟩
  · norm_num [pCharge, Species.charge]
  · norm_num [pBaryon, Species.baryon]
  · norm_num [pLepton, Species.lepton]
  · simp [pMass, Species.mass]
    linarith

/-- **Charged-pion decay is allowed**: `π⁺ → μ⁺ ν`. -/
theorem pionPlus_decay :
    ParticleDecay .pionPlus [.antimuon, .neutrino] := by
  have hp := PMElementaryParticles.LeptonMasses.pionPlus_value
  have hm := PMElementaryParticles.LeptonMasses.muon_value
  refine ⟨by simp, ?_, ?_, ?_, ?_⟩
  · norm_num [pCharge, Species.charge]
  · norm_num [pBaryon, Species.baryon]
  · norm_num [pLepton, Species.lepton]
  · simp [pMass, Species.mass]
    linarith

/-- **Tau decay is allowed**: `τ → μ ν ν̄`. -/
theorem tau_decay :
    ParticleDecay .tau [.muon, .neutrino, .antineutrino] := by
  have ht := PMElementaryParticles.LeptonMasses.tau_value
  have hm := PMElementaryParticles.LeptonMasses.muon_value
  refine ⟨by simp, ?_, ?_, ?_, ?_⟩
  · norm_num [pCharge, Species.charge]
  · norm_num [pBaryon, Species.baryon]
  · norm_num [pLepton, Species.lepton]
  · simp [pMass, Species.mass]
    rw [ht]
    linarith

end PMAtoms
