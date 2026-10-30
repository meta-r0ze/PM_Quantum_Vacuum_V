import PMAction.VATrace
import PMDecay.MuonAmplitude

/-!
# The muon's mass drops out of the V−A trace

The muon is massive, so its spin sum is `p̸ + m_μ` (Paper II research `SpinorCompleteness.spin_sums`),
not `p̸`. In the V−A amplitude the muon's spinor sits between two chiral vertices, and the mass term
is killed there by chirality:

* `chiral_sandwich`: `(1 − γ⁵) γ^ν (1 − γ⁵) = 0` for every `ν`.
* `massive_trace`: `Tr[a̸ γ^μ (1−γ⁵) (b̸ + m) γ^ν (1−γ⁵)] = Tr[a̸ γ^μ (1−γ⁵) b̸ γ^ν (1−γ⁵)]` for
  every complex `m`.
* `massive_amplitude`: hence `muon_amplitude` holds unchanged with the muon factor `p̸ + m_μ`:
  `(G²/2) Σ W(k, p + m_μ) W(pₑ, k̄) = 128 G² (p·k̄)(pₑ·k)`. The muon mass enters the rate only
  through kinematics (`MuonRate`), not through the trace.
-/

noncomputable section
namespace PMDecay.MassiveMuon
open Matrix PMAction VATrace ConcreteFermion

theorem chiral_sandwich (ν : Fin 4) : L * g ν * L = 0 := by
  fin_cases ν <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [L, g, mul_apply, Fin.sum_univ_four]

/-- The trace with a massive middle spinor factor. -/
def Wm (a b : Fin 4 → ℂ) (m : ℂ) (μ ν : Fin 4) : ℂ :=
  (sl a * g μ * L * (sl b + m • (1 : Spin)) * g ν * L).trace

theorem massive_trace (a b : Fin 4 → ℂ) (m : ℂ) (μ ν : Fin 4) : Wm a b m μ ν = W a b μ ν := by
  have h : sl a * g μ * L * (sl b + m • (1 : Spin)) * g ν * L =
      sl a * g μ * L * sl b * g ν * L + m • (sl a * g μ * (L * g ν * L)) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.mul_assoc]
  rw [Wm, h, chiral_sandwich]
  simp [W]

theorem massive_amplitude (G m : ℂ) (p pe k kbar : Fin 4 → ℂ) :
    G ^ 2 / 2 * (∑ μ, ∑ ν, η μ * η ν * Wm k p m μ ν * W pe kbar μ ν) =
      128 * G ^ 2 * mdot p kbar * mdot pe k := by
  simp only [massive_trace]
  exact (muon_amplitude G p pe k kbar).1

end PMDecay.MassiveMuon
