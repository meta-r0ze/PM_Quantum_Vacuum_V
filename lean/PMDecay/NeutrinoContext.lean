import PMNested.FloorNeutrino

/-!
# The contextual neutrino masses against oscillation data

Paper V proposes a free-streaming rest mass at the thermal floor, `M_rest = πα m_e/(Δ³ν)`
(`9.208–9.210` meV, `FloorNeutrino.floor_bounds`), and an interacting mass `M_weak = 6 M_rest`
(`σ + 1 = 6`), and reads the atmospheric splitting from them. This module certifies what those
readings give and compares them with NuFIT 6.0 (normal ordering), `Δm²₃ℓ = (2.534 ± 0.025)·10⁻³ eV²`
and `Δm²₂₁ = (7.49 ± 0.19)·10⁻⁵ eV²`. The check uses the larger error on each side.

* `weak_minus_rest`: `M_weak² − M_rest² = 35 M_rest² ∈ (2.967, 2.969)·10⁻³ eV²`, which is more than
  `17σ` above the atmospheric value (`weak_minus_rest_excluded`).
* `weak_squared_excluded`: `M_weak²` itself, `(3.052, 3.054)·10⁻³ eV²`, is more than `20σ` above.
* `atmospheric_factor`: the common multiplier `k` with `(k² − 1) M_rest² = Δm²₃ℓ` lies in
  `(5.55, 5.57)`, not `6`.
* With any common multiplier the tower's two gaps keep the ratio `1849`, while the observed ratio is
  near `34` (`FloorNeutrino.no_moderate_gap_ratio`), so no single rescaling fits both splittings.

So the stated contextual reading does not reproduce the atmospheric splitting: it overshoots by
about `17%`. A derived propagation Hamiltonian, not a common factor, is needed.
-/

noncomputable section
namespace PMDecay.NeutrinoContext
open PMNested FloorNeutrino CertifiedConstants

def mRest : ℝ := Bulk.floorMass α meEV

lemma sq_bounds : (0.009208 : ℝ) ^ 2 < mRest ^ 2 ∧ mRest ^ 2 < (0.009210 : ℝ) ^ 2 := by
  have hf := floor_bounds
  unfold mRest
  constructor <;> nlinarith [hf.1, hf.2]

theorem weak_minus_rest :
    (0.002967 : ℝ) < (6 * mRest) ^ 2 - mRest ^ 2 ∧ (6 * mRest) ^ 2 - mRest ^ 2 < 0.002969 := by
  obtain ⟨h1, h2⟩ := sq_bounds
  constructor <;> nlinarith

theorem weak_minus_rest_excluded : 17 < ((6 * mRest) ^ 2 - mRest ^ 2 - 0.002534) / 0.000025 := by
  obtain ⟨h, -⟩ := weak_minus_rest
  rw [lt_div_iff₀ (by norm_num)]; linarith

theorem weak_squared_excluded :
    (0.003052 : ℝ) < (6 * mRest) ^ 2 ∧ (6 * mRest) ^ 2 < 0.003054 ∧
      20 < ((6 * mRest) ^ 2 - 0.002534) / 0.000025 := by
  obtain ⟨h1, h2⟩ := sq_bounds
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  rw [lt_div_iff₀ (by norm_num)]; nlinarith

/-- **The multiplier the atmospheric value would need.** -/
theorem atmospheric_factor (k : ℝ) (hk : 0 < k) (hfit : (k ^ 2 - 1) * mRest ^ 2 = 0.002534) :
    5.55 < k ∧ k < 5.57 := by
  obtain ⟨h1, h2⟩ := sq_bounds
  constructor
  · by_contra h; push Not at h
    have : k ^ 2 ≤ 5.55 ^ 2 := by nlinarith
    nlinarith
  · by_contra h; push Not at h
    have : 5.57 ^ 2 ≤ k ^ 2 := by nlinarith
    nlinarith

end PMDecay.NeutrinoContext
