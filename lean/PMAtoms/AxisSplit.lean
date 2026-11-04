import PMAtoms.Invariants
import PMConstants.BaryonNumber
import Mathlib.Tactic

/-!
# The 3+1 axis split from the substrate

`BaryonNumber.axisB` assigns `0` to the lepton/reference axis and `1/3` to each
colour axis. This proves the four channels split as three colour axes plus one
reference axis — the origin of the `3 pn + 1 homo` channel rule.
-/

namespace PMAtoms
open PMConstants.BaryonNumber

/-- The reference axis is the unique axis with baryon weight zero. -/
theorem lepton_axis_unique (i : Fin 4) : axisB i = 0 ↔ i = 0 := by
  fin_cases i <;> simp [axisB]

/-- Exactly one reference axis. -/
theorem reference_axis_card :
    ((Finset.univ.filter (fun i : Fin 4 => axisB i = 0)).card) = 1 := by
  have h : (Finset.univ.filter (fun i : Fin 4 => axisB i = 0)) = {0} := by
    ext i
    simp [lepton_axis_unique]
  rw [h]
  simp

/-- Exactly three colour axes. -/
theorem colour_axis_card :
    ((Finset.univ.filter (fun i : Fin 4 => axisB i = 1/3)).card) = 3 := by
  have h : (Finset.univ.filter (fun i : Fin 4 => axisB i = 1/3)) = {1, 2, 3} := by
    ext i
    fin_cases i <;> simp [axisB]
  rw [h]
  simp

/-- The axes split into the reference axis and the three colour axes. -/
theorem axis_split :
    (Finset.univ.filter (fun i : Fin 4 => axisB i = 0)) ∪
      (Finset.univ.filter (fun i : Fin 4 => axisB i = 1/3)) = Finset.univ := by
  ext i
  fin_cases i <;> simp [axisB]

/-- `3 + 1 = 4` from the two axis sets. -/
theorem three_plus_one_axes :
    ((Finset.univ.filter (fun i : Fin 4 => axisB i = 1/3)).card) + 1 = 4 := by
  rw [colour_axis_card]

end PMAtoms
