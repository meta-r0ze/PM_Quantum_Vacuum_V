import PMElementaryParticles.MassiveDaughterSpectrum
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Closed-form massive-daughter contact width

Evaluation of `MassiveDaughterSpectrum.width`, with a massive charged daughter
and two massless neutrinos. The logarithmic correction is obtained from an
antiderivative of the proved spectrum, not inserted as a numerical factor.
The vertex, flux and phase-space normalization retain their existing scope.
-/
noncomputable section
namespace PMElementaryParticles.MassiveWidth
open MassiveDaughterSpectrum

def kernel (m μ E : ℝ) : ℝ := momentum μ E *
  (E * (3 * m ^ 2 + 3 * μ ^ 2 - 4 * m * E) - 2 * m * μ ^ 2)

def primitive (m μ E : ℝ) : ℝ :=
  (m ^ 2 + μ ^ 2) * momentum μ E ^ 3 -
    m / 2 * E * momentum μ E * (2 * E ^ 2 + μ ^ 2) +
      3 * m * μ ^ 4 / 2 * Real.log (E + momentum μ E)

theorem log_derivative (μ E : ℝ) (hμ : 0 < μ) (hE : μ < E) :
    HasDerivAt (fun x => Real.log (x + momentum μ x)) (1 / momentum μ E) E := by
  have hP : 0 < momentum μ E := Real.sqrt_pos.mpr (by nlinarith)
  have harg : E + momentum μ E ≠ 0 := ne_of_gt (add_pos (lt_trans hμ hE) hP)
  have hd := ((hasDerivAt_id E).add (momentum_derivative μ E hμ.le hE)).log harg
  convert hd using 1
  · rfl
  · change 1 / momentum μ E = (1 + E / momentum μ E) / (E + momentum μ E)
    field_simp
    ring

theorem primitive_derivative (m μ E : ℝ) (hμ : 0 < μ) (hE : μ < E) :
    HasDerivAt (primitive m μ) (kernel m μ E) E := by
  have hP : 0 < momentum μ E := Real.sqrt_pos.mpr (by nlinarith)
  have hs := momentum_shell μ E (by nlinarith)
  have hd := (((momentum_derivative μ E hμ.le hE).pow 3).const_mul (m ^ 2 + μ ^ 2)).sub
    ((((hasDerivAt_id E).const_mul (m / 2)).mul
      (momentum_derivative μ E hμ.le hE)).mul
        ((((hasDerivAt_id E).pow 2).const_mul 2).add_const (μ ^ 2)))
  have hd' := hd.add ((log_derivative μ E hμ hE).const_mul (3 * m * μ ^ 4 / 2))
  convert hd' using 1
  · rfl
  · dsimp [kernel]
    field_simp
    linear_combination -(m * (2 * E ^ 2 + 3 * μ ^ 2)) * hs

theorem primitive_continuous (m μ b : ℝ) (hμ : 0 < μ) :
    ContinuousOn (primitive m μ) (Set.Icc μ b) := by
  intro E hE
  have harg : E + momentum μ E ≠ 0 := by
    have := Real.sqrt_nonneg (E ^ 2 - μ ^ 2)
    dsimp [momentum]
    linarith [hE.1]
  apply ContinuousAt.continuousWithinAt
  unfold primitive momentum at *
  fun_prop (disch := assumption)

theorem width_primitive (G m μ : ℝ) (hμ : 0 < μ) (hm : μ < m) :
    width G m μ = G ^ 2 / (12 * Real.pi ^ 3) *
      (primitive m μ (endpoint m μ) - primitive m μ μ) := by
  have hr : rate G m μ = fun E => G ^ 2 / (12 * Real.pi ^ 3) * kernel m μ E := by
    funext E
    unfold rate kernel
    ring
  unfold width
  rw [hr, intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (threshold m μ (lt_trans hμ hm) hμ.le hm).1.le (primitive_continuous m μ _ hμ)
  · intro E hE
    exact primitive_derivative m μ E hμ hE.1
  · have hc : Continuous (kernel m μ) := by unfold kernel momentum; fun_prop
    exact hc.intervalIntegrable _ _

/-- Squared-mass-ratio correction; its value at zero uses Real.log 0 = 0,
and is justified independently by `massless_width` below. -/
def phase (r : ℝ) : ℝ := 1 - 8 * r + 8 * r ^ 3 - r ^ 4 - 12 * r ^ 2 * Real.log r

theorem phase_zero : phase 0 = 1 := by norm_num [phase]
theorem phase_one : phase 1 = 0 := by norm_num [phase]

/-- The logarithmic correction extends continuously to the massless endpoint. -/
theorem phase_continuous : Continuous phase := by
  have he : phase = fun r => 1 - 8 * r + 8 * r ^ 3 - r ^ 4 - 12 * r * (r * Real.log r) := by
    funext r
    unfold phase
    ring
  rw [he]
  have hlog := Real.continuous_mul_log
  fun_prop

theorem massless_limit : Filter.Tendsto phase (nhds 0) (nhds 1) := by
  simpa only [phase_zero] using phase_continuous.tendsto 0

theorem threshold_limit : Filter.Tendsto phase (nhds 1) (nhds 0) := by
  simpa only [phase_one] using phase_continuous.tendsto 1

theorem endpoint_momentum (m μ : ℝ) (hμ : 0 ≤ μ) (hm : μ ≤ m) (hm0 : 0 < m) :
    momentum μ (endpoint m μ) = (m ^ 2 - μ ^ 2) / (2 * m) := by
  have hp : 0 ≤ (m ^ 2 - μ ^ 2) / (2 * m) := by
    apply div_nonneg _ (by positivity)
    nlinarith
  unfold momentum
  have he : endpoint m μ ^ 2 - μ ^ 2 = ((m ^ 2 - μ ^ 2) / (2 * m)) ^ 2 := by
    unfold endpoint
    field_simp
    ring
  rw [he, Real.sqrt_sq hp]

theorem primitive_lower (m μ : ℝ) :
    primitive m μ μ = 3 * m * μ ^ 4 / 2 * Real.log μ := by
  simp [primitive, momentum]

theorem positive_mass_width (G m μ : ℝ) (hμ : 0 < μ) (hm : μ < m) :
    width G m μ = G ^ 2 * m ^ 5 / (192 * Real.pi ^ 3) * phase ((μ / m) ^ 2) := by
  have hm0 : 0 < m := lt_trans hμ hm
  have hsum : endpoint m μ + (m ^ 2 - μ ^ 2) / (2 * m) = m := by
    unfold endpoint
    field_simp
    ring
  have hlog : Real.log ((μ / m) ^ 2) = 2 * (Real.log μ - Real.log m) := by
    rw [Real.log_pow, Real.log_div hμ.ne' hm0.ne']
    norm_num
  rw [width_primitive G m μ hμ hm, primitive_lower]
  simp only [primitive, endpoint_momentum m μ hμ.le hm.le hm0, hsum, phase, hlog]
  unfold endpoint
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- The actual integrated spectrum, including the zero-daughter-mass and
zero-phase-space endpoints. No logarithm is evaluated by approximation. -/
theorem closed_width (G m μ : ℝ) (hm0 : 0 < m) (hμ : 0 ≤ μ) (hm : μ ≤ m) :
    width G m μ = G ^ 2 * m ^ 5 / (192 * Real.pi ^ 3) * phase ((μ / m) ^ 2) := by
  rcases hμ.eq_or_lt with h | h
  · subst μ
    simpa [phase_zero] using MassiveDaughterSpectrum.massless_width G m hm0
  · rcases hm.eq_or_lt with heq | hlt
    · subst μ
      have he : endpoint m m = m := by unfold endpoint; field_simp; ring
      simp [width, he, div_self hm0.ne', phase_one]
    · exact positive_mass_width G m μ h hlt

/-- Positivity of the logarithmic expression follows from the positive spectrum,
rather than from a numerical test or an independent logarithm estimate. -/
theorem phase_positive (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) : 0 < phase r := by
  have hs : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  have hs1 : Real.sqrt r < 1 := by nlinarith [Real.sq_sqrt hr]
  have hw := width_positive 1 1 (Real.sqrt r) (by norm_num) hs hs1
  rw [closed_width 1 1 (Real.sqrt r) (by norm_num) hs hs1.le] at hw
  simp only [div_one, Real.sq_sqrt hr, one_pow, one_mul] at hw
  have hc : 0 < (1 : ℝ) / (192 * Real.pi ^ 3) := by positivity
  exact (pos_iff_pos_of_mul_pos hw).mp hc

theorem threshold_width (G m : ℝ) (hm : 0 < m) : width G m m = 0 := by
  rw [closed_width G m m hm hm.le le_rfl]
  simp [div_self hm.ne', phase_one]

end PMElementaryParticles.MassiveWidth
