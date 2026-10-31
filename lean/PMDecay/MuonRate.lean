import PMDecay.MassScaling
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The `192π³` of muon decay

`WeakMatching` normalized the V-A spectrum but left the coefficient of
`Γ = G_F² m⁵/(192π³)` unproved. This module derives it from three inputs, each stated as a premise:

1. **Amplitude.** The spin-averaged V-A contact amplitude is `64 G_F² (p·k̄)(p_e·k)`, with `p` the
   muon, `p_e` the electron, `k, k̄` the two neutrinos (Paper II supplies the contact limit and the
   vertex factor; `SpinorRateBridge` imports the actual bilinear spin-sum proof).
2. **Covariance of the neutrino pair.** The two-neutrino phase-space integral of `k^α k̄^β` depends
   only on `q = k + k̄`, so it is `A g^{αβ} q² + B q^α q^β`. `PairIsotropy`
   derives this form in the pair rest frame from explicit angular symmetries. Transport to
   other frames and identification of the physical measure remain inputs.
3. **Massless phase-space measure.** Lorentz-invariant measure `d³k/((2π)³ 2E)`.

What is proved:

* `pair_kinematics`: for massless `k, k̄`, `q² = 2 k·k̄` and `(q·k)(q·k̄) = (q²)²/4`.
* `tensor_coeffs`: contracting with `g` and with `qq` gives `A = Φ₂/12`, `B = Φ₂/6`.
* `two_body`: the supplied solid-angle and delta-Jacobian factors simplify to
  `Φ₂ = 1/(8π)`, so `A = 1/(96π)`, `B = 2A`; this is not a constructed delta-function measure.
* `rest_frame`: in the muon rest frame, the contracted amplitude is
  `64 G_F² m² E (3m − 4E)/(96π)`.
* `electron_measure`: `4π E²/((2π)³ 2E) = E/(4π²)`.
* `rate_density`: so `dΓ/dE = G_F² m E² (3m − 4E)/(12π³)`.
* `muon_rate`: `∫₀^{m/2} dΓ/dE dE = G_F² m⁵/(192π³)`.
* `spectrum_form`: in `x = 2E/m`, `dΓ/dx = G_F² m⁵/(192π³) · 2x²(3 − 2x)`, the spectrum
  `MassScaling.spectrum` that `WeakMatching.spectrum_normalized` integrates to one.

So `192π³` is not an input: `192π³ = 2 · 4π² · 96π · 16 / 64`, from the flux `1/(2m)`, the electron
measure `1/(4π²)`, the covariant pair integral `1/(96π)`, the endpoint `(m/2)⁴` against `m⁴`, and the
amplitude normalization `64`.
-/

noncomputable section
namespace PMDecay.MuonRate
open intervalIntegral

/-- Minkowski product, signature `(+,−,−,−)`. -/
def mdot (u v : Fin 4 → ℝ) : ℝ := u 0 * v 0 - u 1 * v 1 - u 2 * v 2 - u 3 * v 3

/-- **Massless pair kinematics.** -/
theorem pair_kinematics (k k' : Fin 4 → ℝ) (hk : mdot k k = 0) (hk' : mdot k' k' = 0) :
    mdot (k + k') (k + k') = 2 * mdot k k' ∧
      mdot (k + k') k * mdot (k + k') k' = (mdot (k + k') (k + k')) ^ 2 / 4 := by
  unfold mdot at *
  simp only [Pi.add_apply]
  constructor
  · nlinarith [hk, hk']
  · have e1 : (k 0 + k' 0) * k 0 - (k 1 + k' 1) * k 1 - (k 2 + k' 2) * k 2 - (k 3 + k' 3) * k 3 =
        k' 0 * k 0 - k' 1 * k 1 - k' 2 * k 2 - k' 3 * k 3 := by linarith
    have e2 : (k 0 + k' 0) * k' 0 - (k 1 + k' 1) * k' 1 - (k 2 + k' 2) * k' 2 - (k 3 + k' 3) * k' 3 =
        k 0 * k' 0 - k 1 * k' 1 - k 2 * k' 2 - k 3 * k' 3 := by linarith
    have e3 : (k 0 + k' 0) * (k 0 + k' 0) - (k 1 + k' 1) * (k 1 + k' 1) - (k 2 + k' 2) * (k 2 + k' 2)
        - (k 3 + k' 3) * (k 3 + k' 3) = 2 * (k 0 * k' 0 - k 1 * k' 1 - k 2 * k' 2 - k 3 * k' 3) := by
      linarith
    rw [e1, e2, e3]; ring

/-- **The covariant tensor coefficients.** With `∫ k·k̄ = (s/2)Φ` and `∫ (q·k)(q·k̄) = (s²/4)Φ`
(from `pair_kinematics`), the form `A g s + B q q` has `A = Φ/12`, `B = Φ/6`. -/
theorem tensor_coeffs (Φ A B s : ℝ) (hs : s ≠ 0)
    (hg : (4 * A + B) * s = s / 2 * Φ) (hq : (A + B) * s ^ 2 = s ^ 2 / 4 * Φ) :
    A = Φ / 12 ∧ B = Φ / 6 := by
  have h1 : 4 * A + B = Φ / 2 := by
    have := mul_right_cancel₀ hs (show (4 * A + B) * s = (Φ / 2) * s by rw [hg]; ring)
    exact this
  have h2 : A + B = Φ / 4 := by
    have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
    exact mul_right_cancel₀ hs2 (show (A + B) * s ^ 2 = (Φ / 4) * s ^ 2 by rw [hq]; ring)
  constructor <;> linarith

/-- **Massless two-body phase space.** Rest frame: `(4π/(2π)²) · (1/4) · (1/2) = 1/(8π)`
(solid angle, `|k|²/(2|k|·2|k|)`, and the Jacobian of `δ(√s − 2|k|)`). -/
theorem two_body : 4 * Real.pi / (2 * Real.pi) ^ 2 * (1 / 4) * (1 / 2) = 1 / (8 * Real.pi) := by
  have : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp; ring

theorem pair_coeffs : (1 / (8 * Real.pi)) / 12 = 1 / (96 * Real.pi) ∧
    (1 / (8 * Real.pi)) / 6 = 2 * (1 / (96 * Real.pi)) := by
  have : Real.pi ≠ 0 := Real.pi_ne_zero
  constructor <;> field_simp <;> ring

/-- **Rest-frame contraction of the amplitude with the pair tensor.** -/
theorem rest_frame (G m E : ℝ) :
    let p : Fin 4 → ℝ := ![m, 0, 0, 0]
    let pe : Fin 4 → ℝ := ![E, E, 0, 0]
    let q := p - pe
    let A := 1 / (96 * Real.pi)
    64 * G ^ 2 * (A * mdot p pe * mdot q q + 2 * A * mdot p q * mdot pe q) =
      64 * G ^ 2 * m ^ 2 * E * (3 * m - 4 * E) / (96 * Real.pi) := by
  intro p pe q A
  simp only [p, pe, q, A, mdot, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- **Massless electron measure.** -/
theorem electron_measure (E : ℝ) (hE : E ≠ 0) :
    4 * Real.pi * E ^ 2 / ((2 * Real.pi) ^ 3 * (2 * E)) = E / (4 * Real.pi ^ 2) := by
  have : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp; ring

/-- The electron energy spectrum. -/
def rate (G m E : ℝ) : ℝ := G ^ 2 * m * E ^ 2 * (3 * m - 4 * E) / (12 * Real.pi ^ 3)

/-- **Flux × electron measure × contracted amplitude.** -/
theorem rate_density (G m E : ℝ) (hm : m ≠ 0) :
    1 / (2 * m) * (E / (4 * Real.pi ^ 2)) * (64 * G ^ 2 * m ^ 2 * E * (3 * m - 4 * E) /
      (96 * Real.pi)) = rate G m E := by
  have : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold rate; field_simp; ring

/-- **`Γ = G_F² m⁵/(192π³)`.** -/
theorem muon_rate (G m : ℝ) :
    ∫ E in (0 : ℝ)..(m / 2), rate G m E = G ^ 2 * m ^ 5 / (192 * Real.pi ^ 3) := by
  have h : (fun E => rate G m E) =
      fun E => (G ^ 2 * m / (12 * Real.pi ^ 3)) * (3 * m * E ^ 2 - 4 * E ^ 3) := by
    funext E; unfold rate; ring
  rw [h, integral_const_mul, integral_sub, integral_const_mul, integral_const_mul, integral_pow,
    integral_pow]
  · have : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp; ring
  all_goals
    apply Continuous.intervalIntegrable
    fun_prop

/-- **The spectrum in `x = 2E/m`.** -/
theorem spectrum_form (G m x : ℝ) :
    rate G m (m * x / 2) * (m / 2) = G ^ 2 * m ^ 5 / (192 * Real.pi ^ 3) * MassScaling.spectrum x := by
  have : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold rate MassScaling.spectrum; field_simp; ring

end PMDecay.MuonRate
