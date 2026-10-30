import PMDecay.CompositeMasses

/-!
# Charged lepton and charged pion masses against CODATA 2022 and PDG

Units of `m_e`; `α`, `α⁻¹`, `π` as in `CompositeMasses`.

| Formula | Value | Comparison |
| --- | --- | --- |
| `m_μ = Δσ − χ − 2π + α(χ+σ)/(1−α)` | `206.7682717` | CODATA `206.7682827(46)`: `muon_tension`, pull in `(−2.5, −2.3)` |
| `m_τ = Δ²χ − Δσ − χ − D` | `3477`, i.e. `1776.743` MeV | PDG `1776.93(9)` MeV: `tau_tension`, pull in `(−2.1, −2.0)` |
| `m_π⁺ = 2α⁻¹ − σχ + 1/(ν−χ) + σ + D − α(σ−χ)/χ` | `139.57041` MeV | PDG `139.57039(18)`: `pionPlus_mass` within `0.2σ` |

The muon and tau formulas sit about `2.4σ` and `2.1σ` low. These are recorded as tensions, not
agreements: the muon ratio is known to `2·10⁻⁸`, so a missing term of size about `1.1·10⁻⁵ m_e`
(roughly `0.2 α²`) would be needed.
-/

noncomputable section
namespace PMDecay.LeptonMasses
open PMDecay.CompositeMasses

def muon : ℝ := 43 * 5 - 2 - 2 * Real.pi + αe * (2 + 5) / (1 - αe)
def tau : ℝ := 43 ^ 2 * 2 - 43 * 5 - 2 - 4
def pionPlus : ℝ := 2 * αinv - 5 * 2 + 1 / (16 - 2) + 5 + 4 - αe * ((5 - 2) / 2)

theorem muon_value : 206.7682716 < muon ∧ muon < 206.7682718 := by
  have hp := pi_b; have ha := a_b
  have h1 : 0 < 1 - αe := by linarith [ha.2]
  have q1 : αe * 7 / (1 - αe) < 0.05145697 := by
    rw [div_lt_iff₀ h1]; nlinarith [ha.1, ha.2]
  have q2 : 0.05145696 < αe * 7 / (1 - αe) := by
    rw [lt_div_iff₀ h1]; nlinarith [ha.1, ha.2]
  unfold muon
  have e : αe * (2 + 5) / (1 - αe) = αe * 7 / (1 - αe) := by norm_num
  rw [e]; constructor <;> nlinarith [hp.1, hp.2]

theorem muon_tension : -2.5 < (muon - 206.7682827) / 0.0000046 ∧
    (muon - 206.7682827) / 0.0000046 < -2.3 := by
  have h := muon_value
  constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

theorem tau_value : tau = 3477 := by norm_num [tau]

theorem tau_tension : -2.1 < (tau * me - 1776.93) / 0.09 ∧ (tau * me - 1776.93) / 0.09 < -2.0 := by
  rw [tau_value]; unfold me; constructor <;> norm_num

theorem pionPlus_mass : |(pionPlus * me - 139.57039) / 0.00018| < 0.2 := by
  have hg := g_b; have ha := a_b
  unfold pionPlus me
  rw [abs_lt]; constructor
  · rw [lt_div_iff₀ (by norm_num)]; nlinarith [hg.1, ha.2]
  · rw [div_lt_iff₀ (by norm_num)]; nlinarith [hg.2, ha.1]

/-! ## Mass splittings

* `kaon_inversion`: `m_K⁰ − m_K⁺ = Dσ − Dπ − 2π/(ν−χ) + 1/√2 + α(σ−χ)/χ` is positive, the observed
  inversion, and lies in `(3.93, 3.94)` MeV (PDG `497.611 − 493.677 = 3.934`).
* `pion_splitting`: `m_π⁺ − m_π⁰ = σ + D − α(σ−χ)/χ` lies in `(4.5933, 4.5935)` MeV (PDG `4.5936(5)`, within `0.6σ`).
-/

theorem kaon_inversion : 3.93 < (kaon0 - kaonPlus) * me ∧ (kaon0 - kaonPlus) * me < 3.94 := by
  have hp := pi_b; have ha := a_b
  have hs : (0.7071067811 : ℝ) < 1 / Real.sqrt 2 ∧ 1 / Real.sqrt 2 < 0.7071067812 := by
    have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hpos := Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)
    constructor
    · rw [lt_div_iff₀ hpos]; nlinarith
    · rw [div_lt_iff₀ hpos]; nlinarith
  unfold kaon0 kaonPlus me
  constructor <;> nlinarith [hp.1, hp.2, hs.1, hs.2, ha.1, ha.2]

theorem pion_splitting : 4.5933 < (pionPlus - pion0) * me ∧ (pionPlus - pion0) * me < 4.5935 := by
  have ha := a_b
  unfold pionPlus pion0 me
  constructor <;> nlinarith [ha.1, ha.2]

end PMDecay.LeptonMasses
