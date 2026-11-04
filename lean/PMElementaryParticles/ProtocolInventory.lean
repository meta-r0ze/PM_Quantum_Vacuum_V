import PMElementaryParticles.ChargeProtocols

/-!
# The Paper V protocol inventory: base protocols, anchors, and the sterile vacancy

Paper V's §4 claims the 16-channel substrate admits **four base routing protocols**
(electron, up, down, neutrino), two routing modes (colour bulk or not), three
geometric anchors (D=4 manifold, χ=2 boundary, none), and exactly **one sterile
vacancy** — the unanchored, uncoloured, static slot. Paper III's
`CarrierRepresentation` proves the carrier multiplicities and charges; this module
proves that Paper V's *protocol* reading of the same `Channels` type is internally
exact. These are inventory/counting statements about the stipulated routing model
(the paper itself calls it stipulated); they do **not** derive the physical
identification.

* `channels_card` — the substrate has 16 channels.
* `two_routing_modes` — 12 route through the colour bulk, 4 do not.
* `hand_split` — 8 active (left-handed temporal boundary) and 8 static.
* `anchor_split` — 12 manifold (quark), 2 boundary (electron), 2 unanchored.
* `inventory_split` — up 6, down 6, electron 2, neutrino 1, sterile 1, summing to 16.
* `sterile_iff_no_base` — the sterile vacancy is exactly the single uncoloured,
  static, unanchored channel with no base protocol.
* `baseProtocol_charge` — the structural classification reproduces the charges
  computed from Paper III's generator (`ChargeProtocols.Q`).
-/

noncomputable section
namespace PMElementaryParticles.ProtocolInventory
open PMConstants PacketGaugeActions

/-- The four base routing protocols of Paper V §4. -/
inductive BaseProtocol
  | electron | up | down | neutrino
  deriving DecidableEq, Repr

instance : Fintype BaseProtocol where
  elems := {BaseProtocol.electron, BaseProtocol.up, BaseProtocol.down, BaseProtocol.neutrino}
  complete := by intro x; cases x <;> simp

/-- The geometric anchor a protocol uses to bridge chiral sectors. -/
inductive Anchor
  | manifold   -- D = 4 spacetime anchor (quarks)
  | boundary   -- χ = 2 topological anchor (electron)
  | unanchored -- none (neutrino, sterile vacancy)
  deriving DecidableEq, Repr

/-- Routing through the internal colour bulk `N_res = σ − χ = 3`. -/
def colourBulk : Channels → Bool
  | .inl _ => true
  | .inr (.inl _) => true
  | _ => false

/-- Coupled to the active (left-handed) temporal boundary. -/
def active : Channels → Bool
  | .inl _ => true
  | .inr (.inl _) => false
  | .inr (.inr (.inl _)) => true
  | .inr (.inr (.inr _)) => false

/-- The geometric anchor used by the channel. -/
def anchor : Channels → Anchor
  | .inl _ => .manifold
  | .inr (.inl _) => .manifold
  | .inr (.inr (.inl s)) => if s = 0 then .unanchored else .boundary
  | .inr (.inr (.inr s)) => if s = 0 then .unanchored else .boundary

/-- The base protocol (if any) of a channel. The sterile vacancy has none. -/
def baseProtocol : Channels → Option BaseProtocol
  | .inl (_, s) => some (if s = 0 then .up else .down)
  | .inr (.inl (_, s)) => some (if s = 0 then .up else .down)
  | .inr (.inr (.inl s)) => if s = 0 then some .neutrino else some .electron
  | .inr (.inr (.inr s)) => if s = 0 then none else some .electron

/-- The substrate has exactly 16 channels (`ν = 16`). -/
theorem channels_card : Fintype.card Channels = 16 := by decide +kernel

/-- **Two routing modes.** 12 channels route through the colour bulk, 4 do not. -/
theorem two_routing_modes :
    (Finset.univ.filter fun c : Channels => colourBulk c = true).card = 12 ∧
      (Finset.univ.filter fun c : Channels => colourBulk c = false).card = 4 := by
  constructor <;> decide +kernel

/-- **Hand split.** 8 active (left-handed boundary) and 8 static channels. -/
theorem hand_split :
    (Finset.univ.filter fun c : Channels => active c = true).card = 8 ∧
      (Finset.univ.filter fun c : Channels => active c = false).card = 8 := by
  constructor <;> decide +kernel

/-- **Anchor split.** 12 manifold, 2 boundary, 2 unanchored. -/
theorem anchor_split :
    (Finset.univ.filter fun c : Channels => anchor c = .manifold).card = 12 ∧
      (Finset.univ.filter fun c : Channels => anchor c = .boundary).card = 2 ∧
      (Finset.univ.filter fun c : Channels => anchor c = .unanchored).card = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- **The full inventory.** Up 6, down 6, electron 2, neutrino 1, sterile 1. -/
theorem inventory_split :
    (Finset.univ.filter fun c : Channels => baseProtocol c = some .up).card = 6 ∧
    (Finset.univ.filter fun c : Channels => baseProtocol c = some .down).card = 6 ∧
    (Finset.univ.filter fun c : Channels => baseProtocol c = some .electron).card = 2 ∧
    (Finset.univ.filter fun c : Channels => baseProtocol c = some .neutrino).card = 1 ∧
    (Finset.univ.filter fun c : Channels => baseProtocol c = none).card = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- There are exactly four base protocols (the inductive has four constructors). -/
theorem baseProtocol_cases (b : BaseProtocol) :
    b = .electron ∨ b = .up ∨ b = .down ∨ b = .neutrino := by
  cases b <;> simp

/-- **The sterile vacancy is unique.** The only channel that is uncoloured, static
and unanchored is exactly the channel with no base protocol. -/
theorem sterile_iff_no_base (c : Channels) :
    (colourBulk c = false ∧ active c = false ∧ anchor c = .unanchored) ↔
      baseProtocol c = none := by
  rcases c with ⟨a, s⟩ | ⟨a, s⟩ | s | s <;> fin_cases s <;>
    simp [colourBulk, active, anchor, baseProtocol]

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- **The structural classification reproduces Paper III's generator charges.** -/
theorem baseProtocol_charge :
    (∀ c : Channels, baseProtocol c = some .up → ChargeProtocols.Q c = 2/3) ∧
    (∀ c : Channels, baseProtocol c = some .down → ChargeProtocols.Q c = -1/3) ∧
    (∀ c : Channels, baseProtocol c = some .electron → ChargeProtocols.Q c = -1) ∧
    (∀ c : Channels, baseProtocol c = some .neutrino → ChargeProtocols.Q c = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro c h <;>
    rw [ChargeProtocols.Q_eval] <;>
    rcases c with ⟨a, s⟩ | ⟨a, s⟩ | s | s <;> fin_cases s <;>
      simp [baseProtocol] at h ⊢ <;> norm_num

/-- **The no-colour channels are exactly Paper III's leptonic channels**, i.e. the
integer-charge ones (`ChargeProtocols.integer_iff_colourless`). This ties the
routing-mode count to the generator charge. -/
theorem colourBulk_false_iff_leptonic (c : Channels) :
    colourBulk c = false ↔ ReferenceMasses.leptonic c = true := by
  rcases c with ⟨a, s⟩ | ⟨a, s⟩ | s | s <;> fin_cases s <;>
    simp [colourBulk, ReferenceMasses.leptonic]

end PMElementaryParticles.ProtocolInventory

