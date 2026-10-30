import PMAction.WallExchange
import PMDecay.SubstrateBridge
import PMDecay.MuonRate

/-!
# The three scaling relations of the `M⁵` bridge, from derived formulas

`SubstrateBridge.conditional_exponent` derives the fifth power from three scaling relations
(kinetic `2d + 1 = 4`, vertex `c + 4d = 4`, rate `2c + k = 1`) and calls them proof obligations.
Each now has a derived source, stated as a homogeneity (scaling) degree of an actual formula.

* **Kinetic, derivative order one** (`momentum_linear`, `dispersion`): Paper II's momentum term
  `K(k) = Σ kⱼ αⱼ` is linear in `k` and squares to `|k|²`. The Hamiltonian is first order in
  derivatives with speed one, so the `1` in `2d + 1 = 4` is the derivative order of the actual
  kinetic operator.
* **Vertex, `c = −2`** (`fermi_scaling`): `G_F = 1/(√2 v²)` (Paper III `MatterRunning`, Paper V
  `WeakMatching`) has scaling degree `−2` under `v ↦ r v`.
* **Rate, `k = 5` and `2c + k = 1`** (`rate_scaling`, `rate_dimension_one`): the derived rate
  `Γ(G, m) = ∫₀^{m/2} dΓ/dE = G² m⁵/(192π³)` (`MuonRate`) has degree `5` in `m`. Rescaling `G` by
  `r⁻²` and `m` by `r` multiplies it by `r`, so the rate has dimension one.
* `obligations_met`: `conditional_exponent`'s three hypotheses hold at `(3/2, −2, 5)`.

What stays an input: the dimension count of the action (`∫ d⁴x ψ̄ ∂ ψ` dimensionless, which turns
derivative order one into `2d + 1 = 4`), and the inputs of `MuonRate` and `VATrace` (contact limit,
spin sums). The fifth power is now a consequence of the derived contact interaction rather than a
benchmark ansatz.
-/

noncomputable section
namespace PMDecay.ScalingObligations
open Matrix PMAction ConcreteFermion

/-- **The momentum term is linear in `k`.** -/
theorem momentum_linear (r : ℝ) (k : Fin 3 → ℝ) :
    WallExchange.K (fun j => r * k j) = (r : ℂ) • WallExchange.K k := by
  simp [WallExchange.K, Finset.smul_sum, smul_smul, Complex.ofReal_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  ext a b
  simp [Complex.real_smul]

set_option maxHeartbeats 1000000 in
/-- **It squares to `|k|²`: first order, speed one.** -/
theorem dispersion (k : Fin 3 → ℝ) :
    WallExchange.K k * WallExchange.K k = ((k 0 ^ 2 + k 1 ^ 2 + k 2 ^ 2 : ℝ) : ℂ) • (1 : Spin) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [WallExchange.K, alpha, Fin.sum_univ_three, mul_apply, Fin.sum_univ_four, one_apply] <;>
    ring_nf <;> simp only [Complex.I_sq] <;> ring

/-- `G_F` as a function of the VEV. -/
def fermi (v : ℝ) : ℝ := 1 / (Real.sqrt 2 * v ^ 2)

/-- **The vertex coupling has scaling degree `−2`.** -/
theorem fermi_scaling (r v : ℝ) (hr : r ≠ 0) (hv : v ≠ 0) : fermi (r * v) = r ^ (-2 : ℤ) * fermi v := by
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  simp only [fermi, _root_.zpow_neg, zpow_ofNat]
  field_simp

/-- The derived width. -/
def width (G m : ℝ) : ℝ := ∫ E in (0 : ℝ)..(m / 2), MuonRate.rate G m E

/-- **The width has degree five in the mass.** -/
theorem rate_scaling (G m r : ℝ) : width G (r * m) = r ^ 5 * width G m := by
  simp only [width, MuonRate.muon_rate]; ring

/-- **Rescaling `G` as `r⁻²` and `m` as `r` scales the width by `r`: dimension one.** -/
theorem rate_dimension_one (G m r : ℝ) (hr : r ≠ 0) :
    width (r ^ (-2 : ℤ) * G) (r * m) = r * width G m := by
  simp only [width, MuonRate.muon_rate, _root_.zpow_neg, zpow_ofNat]
  have : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- **The bridge's three relations hold at the derived values.** -/
theorem obligations_met :
    (2 * (3/2 : ℚ) + 1 = (PMArch.baseline.dimension : ℚ)) ∧
      ((-2 : ℚ) + 4 * (3/2) = (PMArch.baseline.dimension : ℚ)) ∧ (2 * (-2 : ℚ) + 5 = 1) ∧
      SubstrateBridge.conditional_exponent (3/2) (-2) 5 (by norm_num [PMArch.baseline])
        (by norm_num [PMArch.baseline]) (by norm_num) = ⟨rfl, rfl, rfl⟩ := by
  refine ⟨by norm_num [PMArch.baseline], by norm_num [PMArch.baseline], by norm_num, rfl⟩

end PMDecay.ScalingObligations
