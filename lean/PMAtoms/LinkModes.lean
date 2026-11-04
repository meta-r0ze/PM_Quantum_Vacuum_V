import PMFlavor.SubstrateLink
import Mathlib.Tactic

/-!
# Link modes from the substrate link

`SubstrateLink.linkOverlap` has eigenvalues `4` (democratic) and `1,1` (sum-zero).
Row sum `4`, two endpoints ⇒ `2A` link endpoints, i.e. `A` effective links at the
full unit — the leading count used by the periodic table.

The residual is the two **light modes** (`1,1`), whose occupation depends on the
colour/generation imbalance of the nucleus. This module makes that split explicit:
`effectiveLinks A light = A + light/2` (light = total weight in the two sum-zero
modes). The numeric light occupation is the open colour/glue input.
-/

noncomputable section
namespace PMAtoms

/-- Link spectrum: one democratic mode (4) and two light modes (1,1). -/
def linkSpectrum : List ℝ := [4, 1, 1]

theorem linkSpectrum_sum : linkSpectrum.sum = 6 := by
  norm_num [linkSpectrum]

/-- Row sum of the substrate link. -/
def linkRowSum : ℝ := 4

theorem linkRowSum_eq : linkRowSum = 4 := rfl

/-- Effective link count: `A` volume links plus half the light-mode weight. -/
def effectiveLinks (a : ℕ) (light : ℝ) : ℝ := (a : ℝ) + light / 2

/-- No light-mode occupation ⇒ the leading `A`-link count. -/
theorem effectiveLinks_zero (a : ℕ) : effectiveLinks a 0 = (a : ℝ) := by
  simp [effectiveLinks]

/-- The residual after the volume count is exactly half the light-mode weight. -/
theorem residual_eq_light (a : ℕ) (light : ℝ) :
    effectiveLinks a light - (a : ℝ) = light / 2 := by
  simp [effectiveLinks]

end PMAtoms
