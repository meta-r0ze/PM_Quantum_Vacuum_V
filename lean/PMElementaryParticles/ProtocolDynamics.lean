import PMElementaryParticles.ProtocolInventory

/-!
# Protocol decay dynamics: charge-conserving descent on the inventory

Paper V's decay picture is "a change of routing protocol": a parent protocol ends
in an exit cohort of daughter protocols, with conserved payload (charge) and a
strictly lower resonant tier. This module makes that model concrete on the
`ProtocolInventory` base protocols and proves the paper's qualitative decay laws
for it.

* `Tier = Fin 4` — the resonant tier labels `Δ⁰…Δ³` used by the mass ledger.
* `baseCharge` — the charge class of each base protocol (`up=2/3, down=-1/3,
  electron=-1, neutrino=0`), matching the inventory.
* `Decay p ds` — `p` exits into a **nonempty** cohort `ds` with total charge equal
  to `p`'s and every daughter in a strictly lower tier.
* `decay_charge` — charge is conserved along a decay.
* `decay_tier_lt` — every daughter is strictly lower-tier.
* `no_infinite_chain` — no infinite chain of decays (finite descent), matching the
  paper's "a sequence of strict reductions has at most `L(s₀)` steps".
* `tier_zero_terminal` — a tier-0 parent has no nonempty exit cohort.
* `muon_decay` — the muon (electron protocol, tier 1) exits to
  `e + ν + ν̄` at tier 0, conserving charge `-1 = -1 + 0 + 0`.

The **specific** allowed routes and their rates are model inputs (the paper says
an allowed route and a nonzero rate are separate inputs); this module checks the
conservation/descent structure those routes must satisfy.
-/

noncomputable section
namespace PMElementaryParticles.ProtocolDynamics
open PMElementaryParticles.ProtocolInventory

/-- The four geometric tiers: a point (`Δ⁰`), then a line (`Δ¹`), an area (`Δ²`),
and a volume (`Δ³`). Each protocol's mass ledger occupies a subset of these
(leptons/down `0,1,2`; up-type `0,2,3`); the ladder is "point then 1,2,3
dimensions", not a count of generations. -/
abbrev Tier := Fin 4

theorem tier_card : Fintype.card Tier = 4 := by decide

/-- Charge class of a base protocol, matching `ProtocolInventory`. -/
def baseCharge : BaseProtocol → ℚ
  | .up => 2/3
  | .down => -1/3
  | .electron => -1
  | .neutrino => 0

/-- A protocol state is a base protocol at a resonant tier. -/
abbrev State := BaseProtocol × Tier

/-- Total charge of an exit cohort. -/
def cohortCharge (ds : List State) : ℚ := (ds.map fun d => baseCharge d.1).sum

/-- **Decay as a routing change.** A parent exits into a nonempty daughter cohort
with the same total charge, every daughter in a strictly lower tier. -/
def Decay (p : State) (ds : List State) : Prop :=
  ds ≠ [] ∧ cohortCharge ds = baseCharge p.1 ∧ ∀ d ∈ ds, d.2 < p.2

/-- Charge is conserved along a decay. -/
theorem decay_charge {p : State} {ds : List State} (h : Decay p ds) :
    cohortCharge ds = baseCharge p.1 := h.2.1

/-- Every daughter is strictly lower-tier. -/
theorem decay_tier_lt {p : State} {ds : List State} (h : Decay p ds) :
    ∀ d ∈ ds, d.2 < p.2 := h.2.2

/-- **Finite descent.** No infinite chain of decays exists: following one daughter
each step strictly decreases the tier, and there are only three tiers. -/
theorem no_infinite_chain (f : ℕ → State) (ds : ℕ → List State)
    (hdec : ∀ n, Decay (f n) (ds n)) (hmem : ∀ n, f (n+1) ∈ ds n) :
    False := by
  have hstep : ∀ n, (f (n+1)).2 < (f n).2 := fun n => decay_tier_lt (hdec n) _ (hmem n)
  have hval : ∀ n, (f n).2.val + n ≤ (f 0).2.val := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hs : (f (n+1)).2.val + 1 ≤ (f n).2.val := by
        have := hstep n
        rw [Fin.lt_def] at this
        omega
      omega
  have h4 := hval 4
  have hlt : (f 0).2.val < 4 := (f 0).2.isLt
  omega

/-- A tier-0 parent has no nonempty exit cohort (daughters would need tier `< 0`). -/
theorem tier_zero_terminal (b : BaseProtocol) (ds : List State) :
    ¬ Decay (b, ⟨0, by decide⟩) ds := by
  rintro ⟨hne, -, hlt⟩
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil ds hne
  have this := hlt d hd
  have h0 : (⟨0, by decide⟩ : Fin 3).val = 0 := rfl
  rw [Fin.lt_def, h0] at this
  omega

/-- **The muon channel:** the electron protocol at tier 1 exits to
`e + ν + ν̄` at tier 0, conserving charge `-1 = -1 + 0 + 0`. -/
theorem muon_decay :
    Decay (.electron, ⟨1, by decide⟩)
      [(.electron, ⟨0, by decide⟩), (.neutrino, ⟨0, by decide⟩),
       (.neutrino, ⟨0, by decide⟩)] := by
  refine ⟨by simp, ?_, ?_⟩
  · norm_num [cohortCharge, baseCharge]
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;> decide

/-- The electron cohort of the muon decay is exactly the conserved-charge content. -/
theorem muon_decay_charge :
    cohortCharge [(.electron, ⟨0, by decide⟩), (.neutrino, ⟨0, by decide⟩),
       (.neutrino, ⟨0, by decide⟩)] = baseCharge .electron := by
  norm_num [cohortCharge, baseCharge]

end PMElementaryParticles.ProtocolDynamics
