import PMNested.CertifiedConstants
import PMArch.Impedance
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Paper V's composite mass formulas against CODATA 2022 and PDG

Masses in units of `m_e` unless stated. `α⁻¹` is Paper I's derived `geometricIndex`
(`PMArch.geometricIndex_bounds`), `α = 1/α⁻¹` (`PMNested.CertifiedConstants.alpha_bounds`).
`Z_TOL = χ(R_M − σ)/(N³ R_M σ)` and `Z_MAR = 1/(Δ² L_embed (σ+1))` are Paper I's Toll and Margin.

| Formula | Value | Comparison |
| --- | --- | --- |
| `m_p = Δ² − πD − 1/D + 5Z_TOL − Z_MAR/χ − α(D + 1/D)` | `1836.15267344` | CODATA `1836.152673426(32)`: `proton_ratio` within `0.6σ` |
| `m_n = Δ² − πD − 1/D + σ/2 + 3Z_TOL − Z_MAR` | `1838.68366203` | CODATA `1838.68366200(74)`: `neutron_ratio` within `0.1σ` |
| `m_π⁰ = 2α⁻¹ − σχ + 1/(ν − χ)` | `134.97701` MeV | PDG `134.9768(5)`: `pion_mass` within `0.9σ` |
| `m_K⁰ = (σ+χ)α⁻¹ − σ + Dσ − 2π/(ν − χ)` | `497.6124` MeV | PDG `497.611(13)`: `kaon0_mass` within `0.2σ` |
| `m_K⁺ = (σ+χ)α⁻¹ − σ + Dπ − 1/√2 − α(σ−χ)/χ` | `493.6762` MeV | PDG `493.677(16)`: `kaonPlus_mass` within `0.1σ` |
| `r_p = D ħ/(m_p c)` | `0.841236` fm | CODATA 2022 `0.84075(64)`: `proton_radius` within `0.8σ` |

`m_e c² = 0.51099895069` MeV and `ħc = 197.3269804` MeV·fm (CODATA 2022); their uncertainties are
far below the comparisons. These certify the stated formulas' values. They do not derive the
formulas: each term's assignment (which dimensions a composite synchronizes, the charge-load
factors) is the paper's proposed ledger.
-/

noncomputable section
namespace PMDecay.CompositeMasses
open PMArch

def zTol : ℝ := 2 * (172 - 5) / (32 ^ 3 * 172 * 5)
def zMar : ℝ := 1 / (43 ^ 2 * 31 * 6)
def αe : ℝ := PMNested.CertifiedConstants.α
def αinv : ℝ := geometricIndex
def base : ℝ := 43 ^ 2 - Real.pi * 4 - 1 / 4

def proton : ℝ := base + 5 * zTol - zMar / 2 - αe * (4 + 1 / 4)
def neutron : ℝ := base + 5 / 2 + 3 * zTol - zMar
def pion0 : ℝ := 2 * αinv - 5 * 2 + 1 / (16 - 2)
def kaon0 : ℝ := (5 + 2) * αinv - 5 + 4 * 5 - 2 * (Real.pi / (16 - 2))
def kaonPlus : ℝ := (5 + 2) * αinv - 5 + 4 * Real.pi - 1 / Real.sqrt 2 - αe * ((5 - 2) / 2)

def me : ℝ := 0.51099895069
def hbarc : ℝ := 197.3269804

lemma pi_b : (3.14159265358979323846 : ℝ) < Real.pi ∧ Real.pi < 3.14159265358979323847 :=
  ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
lemma a_b : (0.007297352562 : ℝ) < αe ∧ αe < 0.007297352563 :=
  PMNested.CertifiedConstants.alpha_bounds
lemma g_b : (137.035999212381397211 : ℝ) < αinv ∧ αinv < 137.035999212381397213 :=
  geometricIndex_bounds

theorem proton_value : 1836.152673444 < proton ∧ proton < 1836.152673445 := by
  have hp := pi_b; have ha := a_b
  unfold proton base zTol zMar
  constructor <;> nlinarith [hp.1, hp.2, ha.1, ha.2]

theorem proton_ratio : |(proton - 1836.152673426) / 0.000000032| < 1 := by
  have h := proton_value
  rw [abs_lt]; constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

theorem neutron_value : 1838.6836620 < neutron ∧ neutron < 1838.6836621 := by
  have hp := pi_b
  unfold neutron base zTol zMar
  constructor <;> nlinarith [hp.1, hp.2]

theorem neutron_ratio : |(neutron - 1838.68366200) / 0.00000074| < 0.2 := by
  have h := neutron_value
  rw [abs_lt]; constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

theorem pion_mass : |(pion0 * me - 134.9768) / 0.0005| < 0.9 := by
  have hg := g_b
  unfold pion0 me
  rw [abs_lt]; constructor
  · rw [lt_div_iff₀ (by norm_num)]; nlinarith [hg.1]
  · rw [div_lt_iff₀ (by norm_num)]; nlinarith [hg.2]

theorem kaon0_mass : |(kaon0 * me - 497.611) / 0.013| < 0.2 := by
  have hg := g_b; have hp := pi_b
  unfold kaon0 me
  rw [abs_lt]; constructor
  · rw [lt_div_iff₀ (by norm_num)]; nlinarith [hg.1, hp.2]
  · rw [div_lt_iff₀ (by norm_num)]; nlinarith [hg.2, hp.1]

theorem kaonPlus_mass : |(kaonPlus * me - 493.677) / 0.016| < 0.1 := by
  have hg := g_b; have hp := pi_b; have ha := a_b
  have hs : (0.7071067811 : ℝ) < 1 / Real.sqrt 2 ∧ 1 / Real.sqrt 2 < 0.7071067812 := by
    have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hpos := Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)
    constructor
    · rw [lt_div_iff₀ hpos]; nlinarith
    · rw [div_lt_iff₀ hpos]; nlinarith
  unfold kaonPlus me
  rw [abs_lt]; constructor
  · rw [lt_div_iff₀ (by norm_num)]; nlinarith [hg.1, hp.1, hs.2, ha.2]
  · rw [div_lt_iff₀ (by norm_num)]; nlinarith [hg.2, hp.2, hs.1, ha.1]

theorem proton_radius : |(4 * hbarc / (proton * me) - 0.84075) / 0.00064| < 0.8 := by
  have h := proton_value
  have hpos : 0 < proton * me := by unfold me; nlinarith
  have r1 : 4 * hbarc / (proton * me) < 0.841237 := by
    rw [div_lt_iff₀ hpos]; unfold hbarc me; nlinarith
  have r2 : 0.841235 < 4 * hbarc / (proton * me) := by
    rw [lt_div_iff₀ hpos]; unfold hbarc me; nlinarith
  rw [abs_lt]; constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

/-! ## The ledger counts are pinned by the data

Replace the proton's Toll count `5` and Margin divisor `χ = 2` by naturals `k`, `j`, and the
neutron's `3` and `1` likewise. One Toll is `1.19·10⁻⁵ m_e` and one Margin `2.9·10⁻⁶ m_e`, far larger
than the CODATA uncertainties, so the counts are fixed exactly.
* `proton_counts`: within `1σ` of CODATA exactly when `k = 5` and `j = 2`.
* `neutron_counts`: within `1σ` exactly when `k = 3` and `j = 1`.
These test the proposed counts (σ and σ − χ synchronized dimensions; boundary and volumetric Margin
shares); they do not derive why a baryon synchronizes those dimensions. -/

def protonWith (k j : ℕ) : ℝ := base + k * zTol - zMar / j - αe * (4 + 1 / 4)
def neutronWith (k j : ℕ) : ℝ := base + 5 / 2 + k * zTol - zMar / j

lemma zTol_val : zTol = 167 / 14090240 := by norm_num [zTol]
lemma zMar_val : zMar = 1 / 343914 := by norm_num [zMar]

theorem proton_counts (k j : ℕ) (hj : 0 < j) :
    |(protonWith k j - 1836.152673426) / 0.000000032| < 1 ↔ k = 5 ∧ j = 2 := by
  have hv := proton_value
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have e : protonWith k j = proton + (k * zTol - zMar / j - (5 * zTol - zMar / 2)) := by
    unfold protonWith proton; ring
  constructor
  · intro h
    rw [abs_lt, lt_div_iff₀ (by norm_num), div_lt_iff₀ (by norm_num), e] at h
    obtain ⟨h1, h2⟩ := h
    rw [zTol_val, zMar_val] at h1 h2
    have hr0 : 0 < 1 / (343914 : ℝ) / j := by positivity
    have hr1 : 1 / (343914 : ℝ) / j ≤ 1 / 343914 := div_le_self (by norm_num) (by exact_mod_cast hj)
    have k1 : (4 : ℝ) < k := by nlinarith
    have k2 : (k : ℝ) < 6 := by nlinarith
    have hk : k = 5 := by
      have a : 4 < k := by exact_mod_cast k1
      have b : k < 6 := by exact_mod_cast k2
      omega
    subst hk
    have j1 : (1.9 : ℝ) < j := by
      by_contra hc; push Not at hc
      have : 1 / (343914 : ℝ) / 1.9 ≤ 1 / 343914 / j := by
        apply div_le_div_of_nonneg_left (by norm_num) hjR hc
      push_cast at h1 h2; nlinarith
    have j2 : (j : ℝ) < 2.1 := by
      by_contra hc; push Not at hc
      have : 1 / (343914 : ℝ) / j ≤ 1 / 343914 / 2.1 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      push_cast at h1 h2; nlinarith
    have a : 1 < j := by
      have : (1 : ℝ) < j := by linarith
      exact_mod_cast this
    have b : j < 3 := by
      have : (j : ℝ) < 3 := by linarith
      exact_mod_cast this
    exact ⟨rfl, by omega⟩
  · rintro ⟨rfl, rfl⟩
    rw [e]; push_cast; ring_nf
    have := proton_ratio
    convert this using 3; ring

theorem neutron_counts (k j : ℕ) (hj : 0 < j) :
    |(neutronWith k j - 1838.68366200) / 0.00000074| < 1 ↔ k = 3 ∧ j = 1 := by
  have hv := neutron_value
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have e : neutronWith k j = neutron + (k * zTol - zMar / j - (3 * zTol - zMar)) := by
    unfold neutronWith neutron; ring
  constructor
  · intro h
    rw [abs_lt, lt_div_iff₀ (by norm_num), div_lt_iff₀ (by norm_num), e] at h
    obtain ⟨h1, h2⟩ := h
    rw [zTol_val, zMar_val] at h1 h2
    have hr0 : 0 < 1 / (343914 : ℝ) / j := by positivity
    have hr1 : 1 / (343914 : ℝ) / j ≤ 1 / 343914 := div_le_self (by norm_num) (by exact_mod_cast hj)
    have k1 : (2 : ℝ) < k := by nlinarith
    have k2 : (k : ℝ) < 4 := by nlinarith
    have hk : k = 3 := by
      have a : 2 < k := by exact_mod_cast k1
      have b : k < 4 := by exact_mod_cast k2
      omega
    subst hk
    have j2 : (j : ℝ) < 1.5 := by
      by_contra hc; push Not at hc
      have : 1 / (343914 : ℝ) / j ≤ 1 / 343914 / 1.5 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      push_cast at h1 h2; nlinarith
    have b : j < 2 := by
      have : (j : ℝ) < 2 := by linarith
      exact_mod_cast this
    exact ⟨rfl, by omega⟩
  · rintro ⟨rfl, rfl⟩
    rw [e]; push_cast; ring_nf
    have := neutron_ratio
    rw [abs_lt] at this ⊢; constructor <;> linarith [this.1, this.2]

end PMDecay.CompositeMasses
