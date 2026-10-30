import PMDecay.MassScaling
import PMArch.Lattices
import PMArch.Impedance

/-! An explicit dependency bridge and an E8-internal independence witness.
The arithmetic bridge does not assert its operator/scaling premises follow from E8. -/
noncomputable section
namespace PMDecay.SubstrateBridge
open PMArch

/-- If the earlier action model supplies these three scaling relations, D=4
forces the fifth power internally. These relations remain proof obligations. -/
theorem conditional_exponent (fieldDim couplingDim exponent : ℚ)
    (hkinetic : 2*fieldDim+1 = (baseline.dimension : ℚ))
    (hvertex : couplingDim+4*fieldDim = (baseline.dimension : ℚ))
    (hrate : 2*couplingDim+exponent = 1) :
    fieldDim=3/2 ∧ couplingDim = -2 ∧ exponent=5 := by
  norm_num [baseline] at hkinetic hvertex
  constructor
  · linarith
  · constructor <;> linarith

abbrev Lattice := Fin 8 → ℤ

def normMass (z : Lattice) : ℝ := (Lattices.pairing z z : ℝ)/2

def widthCandidate (power : ℕ) (z : Lattice) : ℝ := normMass z ^ power

theorem candidate_positive (power : ℕ) (z : Lattice) (hz : z ≠ 0) :
    0 < widthCandidate power z := by
  have hi := Lattices.positive_norm z hz
  have hr : (0 : ℝ) < Lattices.pairing z z := by exact_mod_cast hi
  unfold widthCandidate normMass
  positivity

/-- Any norm-preserving substrate symmetry preserves every candidate exponent. -/
theorem candidate_symmetry (power : ℕ) (f : Lattice → Lattice)
    (hf : ∀ z, Lattices.pairing (f z) (f z) = Lattices.pairing z z) (z : Lattice) :
    widthCandidate power (f z) = widthCandidate power z := by
  simp only [widthCandidate, normMass, hf]

def root : Lattice := ![0,1,0,0,0,0,0,0]
def doubledRoot : Lattice := ![0,2,0,0,0,0,0,0]

/-- E8 norm symmetry, positivity, and one-root calibration do not select M^5:
both cubic and quintic laws satisfy them, yet disagree at another E8 vector. -/
theorem symmetry_and_reference_do_not_select_fifth :
    widthCandidate 3 root = 1 ∧ widthCandidate 5 root = 1 ∧
    widthCandidate 3 doubledRoot = 64 ∧ widthCandidate 5 doubledRoot = 1024 := by
  norm_num [widthCandidate, normMass, root, doubledRoot, Lattices.pairing,
    Lattices.gram, dotProduct, Matrix.mulVec, Fin.sum_univ_succ]

end PMDecay.SubstrateBridge
