import PMAtoms.RateModel
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Which transition family? A persistence/selection question

A decay channel fixes the **payload** (charge, baryon number, lepton number and
the lower-tier exit). It does not, by itself, fix the **transition family**: the
finite set of substrate events that implements that payload. That family is not
an external input; it is selected by persistence.

The argument:

1. The available families are the substrate transition families that realize the
   channel payload (the protocol/channel constraints).
2. Each family has the `NetCost` toll cost (`RateModel.channelCost`).
3. Persistence selects a least-cost family: `exists_least_cost`, and the
   selected family's rate is `β · cost`.

So the remaining modelling content is the **candidate set** of substrate
families, which comes from the native operations and protocol ledger. Once the
candidate set is specified, the family is a persistence minimum, not a choice of
measured rate.
-/

noncomputable section
namespace PMAtoms

open PMSubstrate.NetCost

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- A transition family: a finite set of substrate events, with its toll. -/
structure TransitionFamily (Ω : Type*) [Fintype Ω] [DecidableEq Ω] where
  events : Finset (Finset Ω)
  toll : ℝ

/-- `NetCost` cost of a transition family. -/
def familyCost (c0 : ℝ) (F : TransitionFamily Ω) : ℝ :=
  F.events.sum (fun E => c0 * prob E)

theorem familyCost_nonneg (c0 : ℝ) (F : TransitionFamily Ω) (hc0 : 0 ≤ c0) :
    0 ≤ familyCost c0 F := by
  unfold familyCost
  exact Finset.sum_nonneg (fun E _ => mul_nonneg hc0 (by unfold PMSubstrate.NetCost.prob; positivity))

/-- **Persistence selects a least-cost family.** -/
theorem exists_least_cost (c0 : ℝ) (cands : Finset (TransitionFamily Ω))
    (h : cands.Nonempty) :
    ∃ best ∈ cands, ∀ c ∈ cands, familyCost c0 best ≤ familyCost c0 c :=
  cands.exists_min_image (familyCost c0) h

/-- The persistence-selected family (a least-cost candidate). -/
def selectedFamily (c0 : ℝ) (cands : Finset (TransitionFamily Ω))
    (h : cands.Nonempty) : TransitionFamily Ω :=
  Classical.choose (exists_least_cost c0 cands h)

theorem selectedFamily_mem (c0 : ℝ) (cands : Finset (TransitionFamily Ω))
    (h : cands.Nonempty) : selectedFamily c0 cands h ∈ cands :=
  (Classical.choose_spec (exists_least_cost c0 cands h)).1

theorem selectedFamily_min (c0 : ℝ) (cands : Finset (TransitionFamily Ω))
    (h : cands.Nonempty) :
    ∀ c ∈ cands, familyCost c0 (selectedFamily c0 cands h) ≤ familyCost c0 c :=
  (Classical.choose_spec (exists_least_cost c0 cands h)).2

/-- Rate of the persistence-selected family. -/
def selectedRate (β c0 : ℝ) (cands : Finset (TransitionFamily Ω))
    (h : cands.Nonempty) : ℝ :=
  β * familyCost c0 (selectedFamily c0 cands h)

/-- **The selected rate is no larger than any candidate's rate.** -/
theorem selectedRate_le (β c0 : ℝ) (cands : Finset (TransitionFamily Ω))
    (h : cands.Nonempty) (hβ : 0 ≤ β) {c : TransitionFamily Ω} (hc : c ∈ cands) :
    selectedRate β c0 cands h ≤ β * familyCost c0 c := by
  unfold selectedRate
  exact mul_le_mul_of_nonneg_left (selectedFamily_min c0 cands h c hc) hβ

/-- Mean life of the persistence-selected family. -/
def selectedMeanLife (β c0 : ℝ) (cands : Finset (TransitionFamily Ω))
    (h : cands.Nonempty) : ℝ :=
  MeanLife (selectedRate β c0 cands h)

/-- **A least-cost family is the persistence optimum**: no candidate has a
smaller ledger cost. This is the static form of the selection rule; the
asymptotic form is `PersistenceMechanics.Selection.selection`. -/
theorem selected_is_persistence_optimum (c0 : ℝ) (cands : Finset (TransitionFamily Ω))
    (h : cands.Nonempty) :
    IsLeast (cands.image (familyCost c0)) (familyCost c0 (selectedFamily c0 cands h)) := by
  constructor
  · exact Finset.mem_image.mpr ⟨selectedFamily c0 cands h, selectedFamily_mem c0 cands h, rfl⟩
  · intro y hy
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hy
    exact selectedFamily_min c0 cands h c hc

end PMAtoms
