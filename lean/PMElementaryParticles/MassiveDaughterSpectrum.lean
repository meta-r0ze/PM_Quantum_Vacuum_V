import PMElementaryParticles.PairTransport
import PMElementaryParticles.MassiveExternalAmplitude
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A massive charged daughter and a massless neutrino pair

The all-mass spin-sum theorem leaves the contact amplitude unchanged in form.
Here the charged daughter's mass is retained in the rest-frame kinematics and
the radial measure. The existing transported pair average gives the resulting
energy density, rather than inserting a phase correction fitted to a lifetime.

As in `PairTransport`, the two-body volume, parent flux and continuum measure
normalization are supplied. This is a tree-level contact spectrum with massless
neutrinos, not a construction of the physical measure or a radiative correction.
-/
noncomputable section
namespace PMElementaryParticles.MassiveDaughterSpectrum
open Matrix PairIsotropy PairIsotropy.AngularAverage PairTransport

def endpoint (m μ : ℝ) : ℝ := (m ^ 2 + μ ^ 2) / (2 * m)
def momentum (μ E : ℝ) : ℝ := Real.sqrt (E ^ 2 - μ ^ 2)

/-- Energy density with the charged-daughter mass retained. -/
def rate (G m μ E : ℝ) : ℝ :=
  G ^ 2 * momentum μ E *
    (E * (3 * m ^ 2 + 3 * μ ^ 2 - 4 * m * E) - 2 * m * μ ^ 2) /
      (12 * Real.pi ^ 3)

theorem momentum_shell (μ E : ℝ) (h : μ ^ 2 ≤ E ^ 2) :
    momentum μ E ^ 2 = E ^ 2 - μ ^ 2 := Real.sq_sqrt (sub_nonneg.mpr h)

/-- The energy-to-radial-momentum Jacobian away from the daughter threshold. -/
theorem momentum_derivative (μ E : ℝ) (hμ : 0 ≤ μ) (hE : μ < E) :
    HasDerivAt (momentum μ) (E / momentum μ E) E := by
  have hs : 0 < E ^ 2 - μ ^ 2 := by nlinarith
  have hd := (((hasDerivAt_id E).pow 2).sub_const (μ ^ 2)).sqrt hs.ne'
  convert hd using 1
  · rfl
  · dsimp [momentum]
    ring

/-- The available energy interval has positive length exactly below threshold. -/
theorem endpoint_gap (m μ : ℝ) (hm : m ≠ 0) :
    endpoint m μ - μ = (m - μ) ^ 2 / (2 * m) := by
  unfold endpoint
  field_simp
  ring

theorem threshold (m μ : ℝ) (hm : 0 < m) (hμ : 0 ≤ μ) (h : μ < m) :
    μ < endpoint m μ ∧ endpoint m μ < m := by
  constructor
  · have := endpoint_gap m μ hm.ne'
    have : 0 < endpoint m μ - μ := by rw [this]; positivity
    linarith
  · apply (div_lt_iff₀ (by positivity : 0 < 2 * m)).mpr
    nlinarith

/-- Massive on-shell daughter, and the invariant mass left for the pair. -/
theorem kinematics (m μ E P : ℝ) (hP : P ^ 2 = E ^ 2 - μ ^ 2) :
    let p : Fin 4 → ℝ := ![m, 0, 0, 0]
    let pe : Fin 4 → ℝ := ![E, P, 0, 0]
    MuonRate.mdot pe pe = μ ^ 2 ∧
      MuonRate.mdot (p - pe) (p - pe) = m ^ 2 + μ ^ 2 - 2 * m * E := by
  simp [MuonRate.mdot]
  constructor <;> nlinarith

/-- Rest-frame contraction of the already derived pair tensor. -/
theorem rest_contraction (G m μ E P : ℝ) (hP : P ^ 2 = E ^ 2 - μ ^ 2) :
    let p : Fin 4 → ℝ := ![m, 0, 0, 0]
    let pe : Fin 4 → ℝ := ![E, P, 0, 0]
    let q := p - pe
    64 * G ^ 2 * ((1 / (96 * Real.pi)) * MuonRate.mdot pe p * MuonRate.mdot q q +
      (2 / (96 * Real.pi)) * MuonRate.mdot pe q * MuonRate.mdot p q) =
      64 * G ^ 2 * m *
        (E * (3 * m ^ 2 + 3 * μ ^ 2 - 4 * m * E) - 2 * m * μ ^ 2) /
          (96 * Real.pi) := by
  dsimp
  simp only [MuonRate.mdot, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    mul_zero, sub_zero]
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  linear_combination G ^ 2 * m * (2 * m - 3 * E) * hP

/-- Radial Jacobian: P²/(2E) dP = P/2 dE when dP/dE = E/P.
This simplifies the supplied measure; it does not construct it. -/
theorem radial_measure (E P : ℝ) (hE : E ≠ 0) (hP : P ≠ 0) :
    (4 * Real.pi * P ^ 2 / ((2 * Real.pi) ^ 3 * (2 * E))) * (E / P) =
      P / (4 * Real.pi ^ 2) := by
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

theorem density (G m μ E : ℝ) (hm : m ≠ 0) :
    1 / (2 * m) * (momentum μ E / (4 * Real.pi ^ 2)) *
      (64 * G ^ 2 * m *
        (E * (3 * m ^ 2 + 3 * μ ^ 2 - 4 * m * E) - 2 * m * μ ^ 2) /
          (96 * Real.pi)) = rate G m μ E := by
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold rate
  field_simp
  ring

/-- Exact massless reduction on the physical positive-energy branch. -/
theorem massless (G m E : ℝ) (hE : 0 ≤ E) : rate G m 0 E = MuonRate.rate G m E := by
  simp [rate, momentum, Real.sqrt_sq hE, MuonRate.rate]
  ring

/-- The physical interior spectrum is strictly positive for a nonzero coupling. -/
theorem rate_positive (G m μ E : ℝ) (hG : G ≠ 0) (hμ : 0 ≤ μ)
    (hm : μ < m) (hE : μ < E) (hEnd : E < endpoint m μ) :
    0 < rate G m μ E := by
  have hm0 : 0 < m := lt_of_le_of_lt hμ hm
  have hE0 : 0 < E := lt_of_le_of_lt hμ hE
  have hEm : E < m := lt_trans hEnd (threshold m μ hm0 hμ hm).2
  have hq : 0 < m ^ 2 + μ ^ 2 - 2 * m * E := by
    have := (lt_div_iff₀ (by positivity : 0 < 2 * m)).mp hEnd
    nlinarith
  have hprod : 0 < m * E - μ ^ 2 := by nlinarith
  have hb : 0 < E * (3 * m ^ 2 + 3 * μ ^ 2 - 4 * m * E) - 2 * m * μ ^ 2 := by
    have h := mul_pos hE0 hq
    have h' := mul_pos hprod (sub_pos.mpr hEm)
    nlinarith
  have hP : 0 < momentum μ E := Real.sqrt_pos.mpr (by nlinarith)
  unfold rate
  positivity

theorem momentum_scaling (r μ E : ℝ) (hr : 0 ≤ r) :
    momentum (r * μ) (r * E) = r * momentum μ E := by
  unfold momentum
  rw [show (r * E) ^ 2 - (r * μ) ^ 2 = r ^ 2 * (E ^ 2 - μ ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr]

/-- The differential width has degree four when all masses and energies scale. -/
theorem rate_scaling (G m μ E r : ℝ) (hr : 0 ≤ r) :
    rate G (r * m) (r * μ) (r * E) = r ^ 4 * rate G m μ E := by
  unfold rate
  rw [momentum_scaling r μ E hr]
  ring

def width (G m μ : ℝ) : ℝ := ∫ E in μ..endpoint m μ, rate G m μ E

theorem rate_continuous (G m μ : ℝ) : Continuous (rate G m μ) := by
  unfold rate momentum
  fun_prop

theorem width_positive (G m μ : ℝ) (hG : G ≠ 0) (hμ : 0 ≤ μ) (hm : μ < m) :
    0 < width G m μ := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    ((rate_continuous G m μ).intervalIntegrable _ _)
  · intro E hE
    exact rate_positive G m μ E hG hμ hm hE.1 hE.2
  · exact (threshold m μ (lt_of_le_of_lt hμ hm) hμ hm).1

theorem massless_width (G m : ℝ) (hm : 0 < m) :
    width G m 0 = G ^ 2 * m ^ 5 / (192 * Real.pi ^ 3) := by
  have he : endpoint m 0 = m / 2 := by
    unfold endpoint
    field_simp
    ring
  unfold width
  rw [he, ← MuonRate.muon_rate]
  apply intervalIntegral.integral_congr
  intro E hE
  rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ m / 2)] at hE
  exact massless G m E hE.1

theorem endpoint_scaling (m μ r : ℝ) (hm : m ≠ 0) (hr : r ≠ 0) :
    endpoint (r * m) (r * μ) = r * endpoint m μ := by
  unfold endpoint
  field_simp

/-- Nonzero daughter masses preserve the fifth power at fixed mass ratio.
Holding the daughter mass fixed instead is a different scaling question. -/
theorem width_scaling (G m μ r : ℝ) (hm : m ≠ 0) (hr : 0 < r) :
    width G (r * m) (r * μ) = r ^ 5 * width G m μ := by
  unfold width
  rw [endpoint_scaling m μ r hm hr.ne']
  have h := intervalIntegral.smul_integral_comp_mul_left
    (a := μ) (b := endpoint m μ) (rate G (r * m) (r * μ)) r
  rw [← h]
  simp only [smul_eq_mul, rate_scaling G m μ _ r hr.le]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- The spectrum comes from an actual boosted angular average, just as in the
massless calculation. Interior energies give a timelike neutrino pair. -/
theorem pair_density {Ω : Type*} (A : AngularAverage Ω)
    (hΦ : A.volume = 1 / (8 * Real.pi)) (G m μ E : ℝ)
    (hμ : 0 ≤ μ) (hm : μ < m) (hE : μ < E) (hEnd : E < endpoint m μ) :
    let p : Fin 4 → ℝ := ![m, 0, 0, 0]
    let pe : Fin 4 → ℝ := ![E, momentum μ E, 0, 0]
    let q := p - pe
    ∃ Λ, IsLorentz Λ ∧
      (∀ ω, Λ *ᵥ A.leftMomentum (Real.sqrt (MuonRate.mdot q q)) ω +
        Λ *ᵥ A.rightMomentum (Real.sqrt (MuonRate.mdot q q)) ω = q) ∧
      1 / (2 * m) * (momentum μ E / (4 * Real.pi ^ 2)) *
        (64 * G ^ 2 * A.average (fun ω =>
          MuonRate.mdot pe (Λ *ᵥ A.leftMomentum (Real.sqrt (MuonRate.mdot q q)) ω) *
            MuonRate.mdot p (Λ *ᵥ A.rightMomentum (Real.sqrt (MuonRate.mdot q q)) ω))) =
          rate G m μ E := by
  intro p pe q
  have hm0 : 0 < m := lt_of_le_of_lt hμ hm
  have hP := momentum_shell μ E (by nlinarith)
  have hq := (kinematics m μ E (momentum μ E) hP).2
  have hs : 0 < MuonRate.mdot q q := by
    rw [hq]
    have he := (lt_div_iff₀ (by positivity : 0 < 2 * m)).mp hEnd
    nlinarith
  have hq0 : 0 < q 0 := by
    have := (threshold m μ hm0 hμ hm).2
    dsimp [q, p, pe]
    linarith
  obtain ⟨Λ, hΛ, hboost⟩ := boost_to q hq0 hs
  refine ⟨Λ, hΛ, fun ω => by rw [transported_sum A, hboost], ?_⟩
  rw [pair_contraction A hΛ, hboost, Real.sq_sqrt hs.le, hΦ]
  have hc := rest_contraction G m μ E (momentum μ E) hP
  dsimp only at hc
  have hcoef : (1 / (8 * Real.pi)) / 12 = 1 / (96 * Real.pi) ∧
      (1 / (8 * Real.pi)) / 6 = 2 / (96 * Real.pi) := by constructor <;> ring
  rw [hcoef.1, hcoef.2, hc]
  exact density G m μ E hm0.ne'

end PMElementaryParticles.MassiveDaughterSpectrum
