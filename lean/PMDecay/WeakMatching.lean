import PMNested.MatterRunning
import PMAction.ContactMatching
import PMAction.ChargedCurrent
import PMDecay.MassScaling

/-!
# Paper V's weak matching from Papers II and III

`MassScaling.mediator_matching` takes the mediator mass `M_W = g v/2` as given. The earlier papers
now supply each ingredient:

* `mediator_mass_derived`: on Paper III's reference, `M_W² = g²v²/4`
  (`PMNested.MatterRunning.mWsq_eq`, from `ReferenceMasses.charged_entry`).
* `matching_from_reference`: hence `g²/(8 M_W²) = 1/(2v²)` for every `g ≠ 0`, the identity of
  `mediator_matching`, with the mass relation derived rather than assumed.
* `fermi_from_reference`: `G_F = 1/(√2 v²)` (Paper III), using Paper II's contact limit
  (`PMAction.ContactMatching.contact_limit`) and vertex factor `g/(2√2)`
  (`PMAction.ChargedCurrent.vertex_coefficient`).

**The spectrum moments.** `MassScaling.spectrum` is the massless V-A electron spectrum.
* `spectrum_normalized`: `∫₀¹ 2x²(3 - 2x) dx = 1`.
* `spectrum_mean`: `∫₀¹ x · 2x²(3 - 2x) dx = 7/10`, the standard mean electron energy fraction.
These are the integrals the earlier endpoint checks stood in for. The `192π³` coefficient (the
full three-body phase-space integral with the V-A amplitude) is still not proved here.
-/

noncomputable section
namespace PMDecay.WeakMatching
open PMNested MatterRunning MassScaling intervalIntegral

theorem mediator_mass_derived (g v : ℝ) : mWsq g v = g ^ 2 * v ^ 2 / 4 := mWsq_eq g v

theorem matching_from_reference (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) :
    g ^ 2 / (8 * mWsq g v) = 1 / (2 * v ^ 2) := by
  rw [mWsq_eq]
  have h := mediator_matching g v hg hv
  rw [show (g * v / 2) ^ 2 = g ^ 2 * v ^ 2 / 4 by ring] at h
  exact h

theorem fermi_from_reference (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) :
    Real.sqrt 2 * (g ^ 2 / (8 * mWsq g v)) = 1 / (Real.sqrt 2 * v ^ 2) :=
  MatterRunning.fermi_from_reference g v hg hv

theorem spectrum_normalized : ∫ x in (0 : ℝ)..1, MassScaling.spectrum x = 1 := by
  have h : (fun x : ℝ => MassScaling.spectrum x) = fun x => 6 * x ^ 2 - 4 * x ^ 3 := by
    funext x; unfold MassScaling.spectrum; ring
  rw [h, integral_sub, integral_const_mul, integral_const_mul, integral_pow, integral_pow]
  · norm_num
  all_goals
    apply Continuous.intervalIntegrable
    fun_prop

theorem spectrum_mean : ∫ x in (0 : ℝ)..1, x * MassScaling.spectrum x = 7 / 10 := by
  have h : (fun x : ℝ => x * MassScaling.spectrum x) = fun x => 6 * x ^ 3 - 4 * x ^ 4 := by
    funext x; unfold MassScaling.spectrum; ring
  rw [h, integral_sub, integral_const_mul, integral_const_mul, integral_pow, integral_pow]
  · norm_num
  all_goals
    apply Continuous.intervalIntegrable
    fun_prop

end PMDecay.WeakMatching
