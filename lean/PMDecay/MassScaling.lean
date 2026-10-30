import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! Dimensional bookkeeping and algebra for a stipulated local four-fermion
amplitude. No spinor amplitude or phase-space integral is asserted here. -/
noncomputable section
namespace PMDecay.MassScaling

def phaseSpaceExponent (n : ℤ) : ℤ := 2*n-4
def kinematicDimension (n : ℤ) : ℤ := 3*n-4

theorem three_body_dimensions : phaseSpaceExponent 3 = 2 ∧ kinematicDimension 3 = 5 := by
  norm_num [phaseSpaceExponent, kinematicDimension]

theorem width_exponent : (-1 : ℤ)+4+phaseSpaceExponent 3 = 5 := by
  norm_num [phaseSpaceExponent]

/-- Canonical Dirac kinetic dimension: two fields and one derivative in dimension four. -/
theorem canonical_fermion_dimension (d : ℚ) : 2*d+1 = 4 ↔ d = 3/2 := by
  constructor <;> intro h <;> linarith

theorem four_fermion_coupling_dimension :
    4*(3/2 : ℚ) = 6 ∧ 4-4*(3/2 : ℚ) = -2 := by norm_num

/-- Tree-level contact matching if the mediator mass is g v / 2. -/
theorem mediator_matching (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) :
    g^2/(8*(g*v/2)^2) = 1/(2*v^2) := by
  field_simp
  ring

theorem fermi_dimension_fixes_fifth (k : ℤ) : 2*(-2)+k = 1 ↔ k = 5 := by omega

def weakWidth (coefficient coupling mass : ℝ) : ℝ := coefficient*coupling^2*mass^5

theorem mass_rescaling (c g m r : ℝ) : weakWidth c g (r*m) = r^5*weakWidth c g m := by
  unfold weakWidth
  ring

theorem units_covariance (c g m r : ℝ) (hr : r ≠ 0) :
    weakWidth c (g/r^2) (r*m) = r*weakWidth c g m := by
  unfold weakWidth
  field_simp
 

/-- Scalar scaling factors from parent normalization, squared amplitude and measure. -/
theorem combined_scaling (c g m : ℝ) (hm : m ≠ 0) :
    (1/m)*(c*g^2*m^4)*m^2 = weakWidth c g m := by
  unfold weakWidth
  field_simp
 

/-- Shape used for the massless V-A muon spectrum; its antiderivative is algebraic. -/
def spectrum (x : ℝ) : ℝ := 2*x^2*(3-2*x)
def cumulative (x : ℝ) : ℝ := 2*x^3-x^4

theorem spectrum_endpoints : cumulative 0 = 0 ∧ cumulative 1 = 1 := by
  norm_num [cumulative]

theorem spectrum_nonnegative {x : ℝ} (_h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ spectrum x := by
  unfold spectrum
  have : 0 ≤ 3-2*x := by linarith
  positivity

end PMDecay.MassScaling
