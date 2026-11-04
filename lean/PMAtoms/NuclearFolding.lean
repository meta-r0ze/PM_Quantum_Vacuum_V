import PMAtoms.NuclearCharge
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# 3D folding and the Coulomb scaling law

The line/ring is folded into 3D by a position map `Fin A → Fin 3 → ℝ`. The static
charge energy uses the 3D distance kernel `1/|r_i − r_j|`. A homothetic folding
`r ↦ lam r` scales the energy by `1/lam`; with `lam = A^{1/3}` this gives the
`Z²/A^{1/3}` valley term.
-/

noncomputable section
namespace PMAtoms

/-- A 3D folding of the nuclear line. -/
structure Folding (A : Nat) where
  pos : Fin A → Fin 3 → ℝ
  inj : Function.Injective pos

/-- Euclidean distance in the 3D substrate. -/
def dist (p q : Fin 3 → ℝ) : ℝ :=
  Real.sqrt (∑ i, (p i - q i) ^ 2)

/-- Homothetic rescaling of a folding. -/
def Folding.scale {A : Nat} (lam : ℝ) (hlam : 0 < lam) (F : Folding A) : Folding A where
  pos i := fun k => lam * F.pos i k
  inj := by
    intro i j h
    apply F.inj
    funext k
    have hk := congrFun h k
    exact mul_left_cancel₀ (ne_of_gt hlam) hk

/-- Coulomb pair energy on the folded positions (self pairs excluded). -/
def coulombEnergy {A : Nat} (F : Folding A) (Q : Fin A → ℝ) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else Q i * Q j / dist (F.pos i) (F.pos j)

lemma dist_scale {lam : ℝ} (hlam : 0 < lam) (p q : Fin 3 → ℝ) :
    dist (fun k => lam * p k) (fun k => lam * q k) = lam * dist p q := by
  unfold dist
  have hsum : (∑ i, (lam * p i - lam * q i) ^ 2) =
      lam ^ 2 * (∑ i, (p i - q i) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum, Real.sqrt_mul (sq_nonneg lam), Real.sqrt_sq_eq_abs, abs_of_pos hlam]

/-- **3D folding scaling law.** Rescaling the folding by `lam > 0` scales the
Coulomb energy by `1/lam`. -/
theorem coulombEnergy_scale {A : Nat} (F : Folding A) (Q : Fin A → ℝ)
    {lam : ℝ} (hlam : 0 < lam) :
    coulombEnergy (F.scale lam hlam) Q = (1 / lam) * coulombEnergy F Q := by
  unfold coulombEnergy Folding.scale
  simp only [dist_scale hlam]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i = j
  · simp [h]
  · simp [h]
    field_simp

/-- Radius of a folded nucleus with `A` nucleons. -/
def foldedRadius (A : Nat) : ℝ := (A : ℝ) ^ ((1 : ℝ) / 3)

/-- **Valley scaling.** With the radius `A^{1/3}`, the energy scales as
`A^{-1/3}`; for `Z` unit charges this is the `Z²/A^{1/3}` Coulomb form. -/
theorem coulombEnergy_folded {A : Nat} (F : Folding A) (Q : Fin A → ℝ)
    (hA : 0 < A) :
    coulombEnergy (F.scale (foldedRadius A) (by unfold foldedRadius; positivity)) Q =
      (1 / foldedRadius A) * coulombEnergy F Q := by
  apply coulombEnergy_scale

/-- Full folded kernel: softened `1/√(r²+a²)`. It is finite at the lattice
short distance and tends to `1/r` at long distance. -/
def softenedKernel (a r : ℝ) : ℝ := 1 / Real.sqrt (r ^ 2 + a ^ 2)

theorem softenedKernel_pos {a r : ℝ} (h : 0 < r ^ 2 + a ^ 2) :
    0 < softenedKernel a r := by
  unfold softenedKernel
  exact one_div_pos.mpr (Real.sqrt_pos.mpr h)

/-- Self-energy of the softened kernel at the lattice site. -/
theorem softenedKernel_zero {a : ℝ} (ha : 0 < a) : softenedKernel a 0 = 1 / a := by
  unfold softenedKernel
  rw [show (0 : ℝ) ^ 2 + a ^ 2 = a ^ 2 by ring, Real.sqrt_sq_eq_abs, abs_of_pos ha]

/-- Nearest-neighbour kernel at lattice spacing 1. -/
theorem softenedKernel_one_one : softenedKernel 1 1 = 1 / Real.sqrt 2 := by
  norm_num [softenedKernel]

theorem softenedKernel_one_zero : softenedKernel 1 0 = 1 := by
  norm_num [softenedKernel]

/-- The full kernel is homothetic: `K(λa, λr) = K(a,r)/λ`. -/
theorem softenedKernel_scale {a r lam : ℝ} (hlam : 0 < lam) :
    softenedKernel (lam * a) (lam * r) = (1 / lam) * softenedKernel a r := by
  unfold softenedKernel
  have hsq : (lam * r) ^ 2 + (lam * a) ^ 2 = lam ^ 2 * (r ^ 2 + a ^ 2) := by ring
  rw [hsq, Real.sqrt_mul (sq_nonneg lam), Real.sqrt_sq_eq_abs, abs_of_pos hlam]
  field_simp

/-- At long distance the softened kernel is bounded by `1/r`. -/
theorem softenedKernel_le_inv {a r : ℝ} (_ha : 0 ≤ a) (hr : 0 < r) :
    softenedKernel a r ≤ 1 / r := by
  unfold softenedKernel
  apply one_div_le_one_div_of_le hr
  rw [Real.le_sqrt (le_of_lt hr)]
  all_goals nlinarith [sq_nonneg a, sq_nonneg r]

/-- E8 charge coupling `πD/(2σ)` in `m_e` units. -/
def e8ChargeCoupling : ℝ := Real.pi * (D : ℝ) / (2 * (σ : ℝ))

theorem e8ChargeCoupling_eq : e8ChargeCoupling = Real.pi * 4 / 10 :=
  charge_coupling

/-- Softened 3D sphere Coulomb energy with lattice-scale regularization. -/
def sphereCoulomb (c : ℝ) (z a : Nat) : ℝ :=
  c * (((σ - χ : Nat) : ℝ) / (σ : ℝ)) *
    ((z * (z - 1) : Nat) : ℝ) /
    Real.sqrt (((a : ℝ) ^ (((χ : ℝ) / (σ - χ : Nat)))) + 1)

theorem sphereCoulomb_factor :
    (((σ - χ : Nat) : ℝ) / (σ : ℝ)) = 3 / 5 := sphere_factor

theorem sphereCoulomb_exponent :
    ((χ : ℝ) / (σ - χ : Nat)) = (2 : ℝ) / 3 := by
  norm_num [σ, χ, PMSubstrate.baseline]

theorem sphereCoulomb_zero (c : ℝ) (a : Nat) : sphereCoulomb c 0 a = 0 := by
  simp [sphereCoulomb]

theorem sphereCoulomb_one (c : ℝ) (a : Nat) : sphereCoulomb c 1 a = 0 := by
  simp [sphereCoulomb]

theorem sphereCoulomb_nonneg {c : ℝ} (hc : 0 ≤ c) (z a : Nat) :
    0 ≤ sphereCoulomb c z a := by
  unfold sphereCoulomb
  positivity

end PMAtoms
