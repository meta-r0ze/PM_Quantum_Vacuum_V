import PMAtoms.NuclearGraph
import Mathlib.Tactic

/-!
# Binding identities for the typed nuclear graph

The H-3/He-3/He-4 data fix the link-weight identities and show that He-4 needs a
non-pairwise closure term. The mirror pair fixes the `nn − pp` link difference.
-/

namespace PMAtoms

/-- Under the H-3 and He-3 pairwise equations, the He-4 pairwise prediction is
`b_H3 + b_He3 = 0.017392 u`, not the measured `0.030377 u`. -/
theorem he4_pairwise_shortfall (wpp wpn wnn : ℝ)
    (hH3 : 2 * wpn + wnn = 0.009106)
    (hHe3 : wpp + 2 * wpn = 0.008286) :
    wpp + 4 * wpn + wnn = 0.017392 ∧
      wpp + 4 * wpn + wnn < 0.030377 := by
  constructor <;> linarith

/-- The missing He-4 amount is the 4-body closure `≈0.012985 u`. -/
theorem he4_closure_gap (wpp wpn wnn : ℝ)
    (hH3 : 2 * wpn + wnn = 0.009106)
    (hHe3 : wpp + 2 * wpn = 0.008286) :
    0.030377 - (wpp + 4 * wpn + wnn) = 0.012985 := by
  linarith

/-- **Mirror relation.** `w_nn − w_pp` is exactly the H-3/He-3 mass displacement. -/
theorem mirror_link_difference (wpp wpn wnn : ℝ)
    (hH3 : 2 * wpn + wnn = 0.009106)
    (hHe3 : wpp + 2 * wpn = 0.008286) :
    wnn - wpp = 0.000820 := by
  linarith

end PMAtoms
