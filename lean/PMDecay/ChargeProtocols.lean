import PMNested.ReferenceMasses
import PMNested.ReferenceAxis

/-!
# Paper V's charge protocols from Paper III's packet

Paper V's routing protocols state that colourless packets carry integer charge and coloured
packets fractional charge in thirds (`Q_quark = Y/3`, the colour bulk `σ − χ = 3`). With Paper III's
derived packet (charges from `Hypercharge.standard`, unbroken `Q = T₃ + Y/2`):

* `charge_values`: every carrier's charge is one of `2/3, −1/3, 0, −1`.
* `thirds`: `3Q` is an integer on every carrier.
* `integer_iff_colourless`: `Q` is an integer exactly on the four leptonic carriers, the ones
  colour fixes (`ReferenceMasses.colour_moves_iff`).

The denominator `3` is the number of colour axes, the axes orthogonal to the reference
(`ReferenceAxis`: colour is the stabilizer of the reference's axis, `4 − 1 = 3`).
-/

noncomputable section
namespace PMDecay.ChargeProtocols
open PMNested Matrix GeneratorNormalization PacketTraceForm

def Q (c : PacketGaugeActions.Channels) : ℂ := (t3 + hyperGen) c c

lemma Q_eval (c : PacketGaugeActions.Channels) :
    Q c = match c with
      | .inl (_, s) => if s = 0 then 2/3 else -1/3
      | .inr (.inl (_, s)) => if s = 0 then 2/3 else -1/3
      | .inr (.inr (.inl s)) => if s = 0 then 0 else -1
      | .inr (.inr (.inr s)) => if s = 0 then 0 else -1 := by
  rcases c with ⟨a, s⟩ | ⟨a, s⟩ | s | s <;> fin_cases s <;>
    simp [Q, t3, hyperGen, weakGen, PacketGaugeActions.charge, PacketGaugeActions.block,
      kroneckerMap_apply, Matrix.add_apply] <;> norm_num

theorem charge_values (c : PacketGaugeActions.Channels) :
    Q c = 2/3 ∨ Q c = -1/3 ∨ Q c = 0 ∨ Q c = -1 := by
  rw [Q_eval]; rcases c with ⟨a, s⟩ | ⟨a, s⟩ | s | s <;> fin_cases s <;> simp

theorem thirds (c : PacketGaugeActions.Channels) : ∃ n : ℤ, 3 * Q c = n := by
  rcases charge_values c with h | h | h | h <;> rw [h]
  · exact ⟨2, by norm_num⟩
  · exact ⟨-1, by norm_num⟩
  · exact ⟨0, by norm_num⟩
  · exact ⟨-3, by norm_num⟩

lemma not_int_two_thirds : ¬ ∃ m : ℤ, (2/3 : ℂ) = m := by
  rintro ⟨m, hm⟩
  have h := congrArg Complex.re hm
  simp at h
  have : (3 : ℝ) * m = 2 := by rw [← h]; norm_num
  have : (3 : ℤ) * m = 2 := by exact_mod_cast this
  omega

lemma not_int_neg_third : ¬ ∃ m : ℤ, (-1/3 : ℂ) = m := by
  rintro ⟨m, hm⟩
  have h := congrArg Complex.re hm
  simp at h
  have : (3 : ℝ) * m = -1 := by rw [← h]; norm_num
  have : (3 : ℤ) * m = -1 := by exact_mod_cast this
  omega

/-- **Integer charge exactly on the colourless carriers.** -/
theorem integer_iff_colourless (c : PacketGaugeActions.Channels) :
    (∃ m : ℤ, Q c = m) ↔ ReferenceMasses.leptonic c = true := by
  rw [Q_eval]
  rcases c with ⟨a, s⟩ | ⟨a, s⟩ | s | s <;> fin_cases s <;>
    simp [ReferenceMasses.leptonic, not_int_two_thirds, not_int_neg_third]
  · exact ⟨0, by simp⟩
  · exact ⟨-1, by simp⟩
  · exact ⟨0, by simp⟩
  · exact ⟨-1, by simp⟩

end PMDecay.ChargeProtocols
