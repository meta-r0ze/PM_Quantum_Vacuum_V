import PMDecay.CompositeMasses
import PMNested.StrongRunning

/-!
# Paper V's quark mass formulas against PDG 2024

Units of `m_e`, `η = 171/172`. Uncertainties as used by the shared calculator (PDG 2024):
`m_u = 2.16(7)`, `m_d = 4.70(7)`, `m_s = 93.5(8)` MeV; `m_c = 1273.0(46)`, `m_b = 4183(7)`,
`m_t = 172570(290)` MeV.

| Formula | MeV | Pull |
| --- | --- | --- |
| `m_u = D/η` | `2.0560` | `(−1.5, −1.4)` |
| `m_d = (D+σ)/η` | `4.6260` | `(−1.1, −1.0)` |
| `m_s = (DΔ + 2σ)/η` | `93.546` | `(0, 0.1)` |
| `m_c = DΔ²/(η(σ−χ))` | `1267.15` | `(−1.3, −1.2)` |
| `m_b = Δ²(D + χ/σ)/η` | `4181.6` | `(−0.3, −0.1)` |
| `m_t = Δ³(D + 1/D)` | `172668` | `(0.3, 0.4)` |

These are the formulas Paper III's `StrongRunning` uses for the flavour thresholds (`m_c`, `m_b`).
-/

noncomputable section
namespace PMDecay.QuarkMasses
open PMDecay.CompositeMasses

def η : ℝ := 171 / 172
def up : ℝ := 4 / η
def down : ℝ := (4 + 5) / η
def strange : ℝ := (4 * 43 + 2 * 5) / η
def charm : ℝ := 4 * 43 ^ 2 / (η * (5 - 2))
def bottom : ℝ := 43 ^ 2 * (4 + 2 / 5) / η
def top : ℝ := 43 ^ 3 * (4 + 1 / 4)

theorem pulls :
    (-1.5 < (up * me - 2.16) / 0.07 ∧ (up * me - 2.16) / 0.07 < -1.4) ∧
    (-1.1 < (down * me - 4.70) / 0.07 ∧ (down * me - 4.70) / 0.07 < -1.0) ∧
    (0 < (strange * me - 93.5) / 0.8 ∧ (strange * me - 93.5) / 0.8 < 0.1) ∧
    (-1.3 < (charm * me - 1273.0) / 4.6 ∧ (charm * me - 1273.0) / 4.6 < -1.2) ∧
    (-0.3 < (bottom * me - 4183) / 7 ∧ (bottom * me - 4183) / 7 < -0.1) ∧
    (0.3 < (top * me - 172570) / 290 ∧ (top * me - 172570) / 290 < 0.4) := by
  unfold up down strange charm bottom top η me
  norm_num

/-- The thresholds Paper III orders are these formulas. -/
theorem threshold_match : charm = PMNested.StrongRunning.mCharm ∧ bottom = PMNested.StrongRunning.mBottom := by
  unfold charm bottom η PMNested.StrongRunning.mCharm PMNested.StrongRunning.mBottom PMNested.overhead
  constructor <;> ring

end PMDecay.QuarkMasses
