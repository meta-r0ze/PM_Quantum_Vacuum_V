import PMDecay.LeptonMasses
import PMDecay.MuonRate

/-!
# The tau lifetime from the muon's, with the derived lepton masses

`MuonRate` gives `Γ(ℓ → e ν ν̄) = G_F² m_ℓ⁵/(192π³)` with one `G_F` for every lepton (the shared
reference, `WeakMatching.fermi_from_reference`). Dividing the tau's leptonic width by the muon's
cancels `G_F` and `192π³`:

  `τ_τ = τ_μ · (m_μ/m_τ)⁵ · B(τ → eνν̄)`.

* `rate_ratio`: the `m⁵` law makes the width ratio `(m_τ/m_μ)⁵` (from `MuonRate.muon_rate`).
* `tau_lifetime_tree`: with Paper V's `m_μ` and `m_τ` (`LeptonMasses`), the measured
  `τ_μ = 2.1969811 μs` and `B_e = 17.82 %`, `291.15 < τ_τ < 291.17` fs.
* `tau_lifetime_pull`: with the standard small corrections (electron phase space in the muon,
  W propagator in the tau, the difference of the QED corrections at the two masses) entering as a
  factor `c ∈ [0.9995, 0.9997]`, the pull against PDG `290.3 ± 0.5` fs, combined with the `B_e`
  error (`±0.65` fs) as `0.82` fs, lies in `(0.8, 1.0)σ`.

So the tau lifetime is consistent with the derived masses. It does not resolve the `−2σ` tau-mass
tension: that tension moves `τ_τ` by only about `0.15` fs, below the lifetime's precision.
The corrections factor is standard physics stated as a premise, not derived here.
-/

noncomputable section
namespace PMDecay.TauLifetime
open PMDecay.LeptonMasses

/-- **The `m⁵` law: width ratio of two leptons.** -/
theorem rate_ratio (G mμ mτ : ℝ) (hG : G ≠ 0) (hμ : mμ ≠ 0) :
    (∫ E in (0 : ℝ)..(mτ / 2), MuonRate.rate G mτ E) / (∫ E in (0 : ℝ)..(mμ / 2), MuonRate.rate G mμ E) =
      (mτ / mμ) ^ 5 := by
  rw [MuonRate.muon_rate, MuonRate.muon_rate]
  have : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- Predicted tau lifetime in femtoseconds (tree level). -/
def tauLife : ℝ := 2.1969811e9 * 0.1782 * (muon / tau) ^ 5

theorem tau_lifetime_tree : 291.15 < tauLife ∧ tauLife < 291.17 := by
  have hm := muon_value
  have ht := tau_value
  unfold tauLife
  rw [ht]
  have hr1 : (206.7682716 / 3477 : ℝ) < muon / 3477 := by
    apply div_lt_div_of_pos_right hm.1 (by norm_num)
  have hr2 : muon / 3477 < (206.7682718 / 3477 : ℝ) := by
    apply div_lt_div_of_pos_right hm.2 (by norm_num)
  have p1 : (206.7682716 / 3477 : ℝ) ^ 5 < (muon / 3477) ^ 5 :=
    pow_lt_pow_left₀ hr1 (by norm_num) (by norm_num)
  have p2 : (muon / 3477) ^ 5 < (206.7682718 / 3477 : ℝ) ^ 5 :=
    pow_lt_pow_left₀ hr2 (by positivity) (by norm_num)
  constructor <;> nlinarith [p1, p2]

theorem tau_lifetime_pull (c : ℝ) (hc : 0.9995 ≤ c ∧ c ≤ 0.9997) :
    0.8 < (c * tauLife - 290.3) / 0.82 ∧ (c * tauLife - 290.3) / 0.82 < 1.0 := by
  have h := tau_lifetime_tree
  constructor
  · rw [lt_div_iff₀ (by norm_num)]; nlinarith [h.1, hc.1]
  · rw [div_lt_iff₀ (by norm_num)]; nlinarith [h.2, hc.2]

end PMDecay.TauLifetime
