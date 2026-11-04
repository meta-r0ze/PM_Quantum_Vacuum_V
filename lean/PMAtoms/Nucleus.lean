import Mathlib.Data.List.Basic
import Mathlib.Tactic
import PersistenceMechanics.Selection
import PMAtoms.Shells
import PMAtoms.Nucleon

/-!
# Nuclear ledger: which `(Z, N)` combinations the substrate rules allow

A nucleus is a ledger of `Z` protons and `N` neutrons. This module does **not**
postulate binding energies, so it cannot select the observed valley of stability.
What it does prove is the structural part the persistence rules supply:

* charge `Q = Z`, baryon number `B = Z + N`, and neutron excess `N − Z`;
* the decay channels `β⁻`, `β⁺`, electron capture, `α`, and fission conserve
  `Q` and `B`, with the electron/neutrino side conserving lepton number;
* conservation alone permits a channel from every nuclide with `N > 0` or
  `Z > 0`, so **stability is not selected by conservation** — it needs a supplied
  cost/binding order;
* with a supplied cost, a nuclide persists exactly when no channel reaches a
  strictly lower-cost daughter (`persists_of_no_lower`, `not_persists_of_lower`);
* the PM selection rule then says a higher-cost parent's survivor share vanishes
  (`lower_cost_species_vanishes`).

Electrons are a separate ledger: a neutral atom has `electrons = Z`, so a nuclear
decay changes the electron count needed for neutrality.
-/

namespace PMAtoms

/-- A nuclide: `Z` protons and `N` neutrons. -/
structure Nuclide where
  Z : ℕ
  N : ℕ
  deriving DecidableEq, Repr

namespace Nuclide

def charge (n : Nuclide) : ℤ := (n.Z : ℤ)

def massNumber (n : Nuclide) : ℕ := n.Z + n.N

def baryon (n : Nuclide) : ℕ := n.massNumber

def neutronExcess (n : Nuclide) : ℤ := (n.N : ℤ) - (n.Z : ℤ)

end Nuclide

/-- Leptons carry the electron ledger; neutrinos carry lepton number but no charge. -/
inductive Lepton
  | electron | positron | neutrino | antineutrino
  deriving DecidableEq, Repr

namespace Lepton

def charge : Lepton → ℤ
  | .electron => -1
  | .positron => 1
  | .neutrino => 0
  | .antineutrino => 0

def number : Lepton → ℤ
  | .electron => 1
  | .positron => -1
  | .neutrino => 1
  | .antineutrino => -1

end Lepton

def totalCharge (ns : List Nuclide) (ls : List Lepton) : ℤ :=
  (ns.map Nuclide.charge).sum + (ls.map Lepton.charge).sum

def totalBaryon (ns : List Nuclide) : ℕ := (ns.map Nuclide.baryon).sum

def totalLepton (ls : List Lepton) : ℤ := (ls.map Lepton.number).sum

/-- A nuclear decay: nonempty products, conserved charge and baryon number, and
zero net lepton number in the products. -/
def Decay (p : Nuclide) (ns : List Nuclide) (ls : List Lepton) : Prop :=
  (ns ≠ [] ∨ ls ≠ []) ∧ totalCharge ns ls = p.charge ∧
    totalBaryon ns = p.baryon ∧ totalLepton ls = 0

/-- Electron capture: the parent absorbs one electron (charge `−1`, lepton `+1`). -/
def Capture (p : Nuclide) (ns : List Nuclide) (ls : List Lepton) : Prop :=
  ns ≠ [] ∧ totalCharge ns ls = p.charge - 1 ∧
    totalBaryon ns = p.baryon ∧ totalLepton ls = 1

def betaMinus (n : Nuclide) : Nuclide := ⟨n.Z + 1, n.N - 1⟩
def betaPlus (n : Nuclide) : Nuclide := ⟨n.Z - 1, n.N + 1⟩
def alphaDaughter (n : Nuclide) : Nuclide := ⟨n.Z - 2, n.N - 2⟩
def alpha : Nuclide := ⟨2, 2⟩

theorem betaMinus_decay (n : Nuclide) (hN : 0 < n.N) :
    Decay n [betaMinus n] [Lepton.electron, Lepton.antineutrino] := by
  refine ⟨Or.inl (by simp), ?_, ?_, ?_⟩
  · simp [totalCharge, betaMinus, Nuclide.charge, Lepton.charge]
  · simp [totalBaryon, betaMinus, Nuclide.baryon, Nuclide.massNumber]
    omega
  · simp [totalLepton, Lepton.number]

theorem betaPlus_decay (n : Nuclide) (hZ : 0 < n.Z) :
    Decay n [betaPlus n] [Lepton.positron, Lepton.neutrino] := by
  refine ⟨Or.inl (by simp), ?_, ?_, ?_⟩
  · simp [totalCharge, betaPlus, Nuclide.charge, Lepton.charge]
    omega
  · simp [totalBaryon, betaPlus, Nuclide.baryon, Nuclide.massNumber]
    omega
  · simp [totalLepton, Lepton.number]

theorem electronCapture_decay (n : Nuclide) (hZ : 0 < n.Z) :
    Capture n [betaPlus n] [Lepton.neutrino] := by
  refine ⟨by simp, ?_, ?_, ?_⟩
  · simp [totalCharge, betaPlus, Nuclide.charge, Lepton.charge]
    omega
  · simp [totalBaryon, betaPlus, Nuclide.baryon, Nuclide.massNumber]
    omega
  · simp [totalLepton, Lepton.number]

theorem alpha_decay (n : Nuclide) (hZ : 2 ≤ n.Z) (hN : 2 ≤ n.N) :
    Decay n [alphaDaughter n, alpha] [] := by
  refine ⟨Or.inl (by simp), ?_, ?_, ?_⟩
  · simp [totalCharge, alphaDaughter, alpha, Nuclide.charge]
    omega
  · simp [totalBaryon, alphaDaughter, alpha, Nuclide.baryon, Nuclide.massNumber]
    omega
  · simp [totalLepton]

theorem fission_decay (n n₁ n₂ : Nuclide)
    (hZ : n₁.Z + n₂.Z = n.Z) (hN : n₁.N + n₂.N = n.N) :
    Decay n [n₁, n₂] [] := by
  refine ⟨Or.inl (by simp), ?_, ?_, ?_⟩
  · simp [totalCharge, Nuclide.charge]
    omega
  · simp [totalBaryon, Nuclide.baryon, Nuclide.massNumber]
    omega
  · simp [totalLepton]

/-- Conservation permits some channel from any nuclide with a neutron. -/
theorem canDecay_of_neutron (n : Nuclide) (hN : 0 < n.N) : ∃ ns ls, Decay n ns ls :=
  ⟨_, _, betaMinus_decay n hN⟩

/-- Conservation permits some channel from any nuclide with a proton. -/
theorem canDecay_of_proton (n : Nuclide) (hZ : 0 < n.Z) : ∃ ns ls, Decay n ns ls :=
  ⟨_, _, betaPlus_decay n hZ⟩

/-- **Conservation alone does not select stability**: every nuclide except the
empty `(0,0)` has an allowed `β`-channel. -/
theorem conservation_permits_all (n : Nuclide) (h : n.Z + n.N > 0) :
    ∃ ns ls, Decay n ns ls := by
  rcases Nat.eq_zero_or_pos n.N with hN | hN
  · have hZ : 0 < n.Z := by omega
    exact canDecay_of_proton n hZ
  · exact canDecay_of_neutron n hN

/-- A supplied cost/binding ledger. `Persists` is local minimality under decay. -/
def Persists (cost : Nuclide → ℝ) (n : Nuclide) : Prop :=
  ∀ ns ls, Decay n ns ls → ∀ d ∈ ns, cost n ≤ cost d

theorem persists_of_no_lower {cost : Nuclide → ℝ} {n : Nuclide}
    (h : ∀ ns ls, Decay n ns ls → ∀ d ∈ ns, cost n ≤ cost d) : Persists cost n := h

theorem not_persists_of_lower {cost : Nuclide → ℝ} {n d : Nuclide}
    {ns : List Nuclide} {ls : List Lepton}
    (hdec : Decay n ns ls) (hd : d ∈ ns) (hcost : cost d < cost n) :
    ¬ Persists cost n := by
  intro hp
  exact (not_lt_of_ge (hp ns ls hdec d hd)) hcost

/-- A neutral atom has as many electrons as protons. Electrons are a separate
ledger, so they are not part of the nuclide's charge count. -/
structure Atom where
  nucleus : Nuclide
  electrons : ℕ
  deriving DecidableEq, Repr

namespace Atom

def netCharge (a : Atom) : ℤ := a.nucleus.charge - (a.electrons : ℤ)

def neutral (a : Atom) : Prop := a.electrons = a.nucleus.Z

def leptonNumber (a : Atom) : ℤ := (a.electrons : ℤ)

theorem neutral_net_zero (a : Atom) (h : a.neutral) : a.netCharge = 0 := by
  unfold netCharge neutral at *
  rw [h]
  simp [Nuclide.charge]

/-- After `β⁻` the nucleus has one more proton, so a neutral atom needs one more
electron; the emitted electron is separate from the nuclear ledger. -/
theorem betaMinus_neutral_needs_electron (a : Atom) (h : a.neutral) :
    (Atom.mk (betaMinus a.nucleus) (a.electrons + 1)).neutral := by
  unfold Atom.neutral at *
  simp [betaMinus, h]

/-- After `β⁺` (or electron capture) a neutral atom needs one fewer electron. -/
theorem betaPlus_neutral_needs_hole (a : Atom) (h : a.neutral) :
    (Atom.mk (betaPlus a.nucleus) (a.electrons - 1)).neutral := by
  unfold Atom.neutral at *
  simp [betaPlus, h]

end Atom

/-- **PM selection rule for nuclei.** If a daughter has strictly lower cost, the
parent's survivor share tends to zero. This is `PersistenceMechanics.Selection.selection`
with constant rate `cost`. -/
theorem lower_cost_species_vanishes {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ι → ℝ) (hp : ∀ i, 0 < p i) {β : ℝ} (hβ : 0 < β)
    (cost : ι → ℝ) {parent daughter : ι} (h : cost daughter < cost parent) :
    Filter.Tendsto
      (fun T => PersistenceMechanics.Selection.survivor p β (fun k => cost k * T) parent)
      Filter.atTop (nhds 0) := by
  refine PersistenceMechanics.Selection.selection hp hβ (fun k T => cost k * T) cost ?_ h
  intro k
  simp

end PMAtoms
