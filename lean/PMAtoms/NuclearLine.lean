import PMAtoms.NuclearCoordination
import PMAtoms.NuclearBinding
import Mathlib.Tactic

/-!
# The line/ring count model

Alternating `p/n` ring plus alpha diagonals:

`m = min(Z,N)`, `d = |N−Z|`,
`pn = 2m`, `pp = (d if Z>N) + m/2`, `nn = (d if N>Z) + m/2`.
-/

namespace PMAtoms

/-- `(pp, pn, nn)` counts for the line/ring + alpha-diagonal arrangement. -/
def lineCounts (z n : Nat) : Nat × Nat × Nat :=
  let m := min z n
  let d := if z > n then z - n else n - z
  let pn := 2 * m
  let pp := (if z > n then d else 0) + m / 2
  let nn := (if n > z then d else 0) + m / 2
  (pp, pn, nn)

/-- E8 form: the homo count uses `χ = 2` instead of the literal 2. -/
def lineCountsE8 (z n : Nat) : Nat × Nat × Nat :=
  let m := min z n
  let d := if z > n then z - n else n - z
  let pn := χ * m
  let pp := (if z > n then d else 0) + m / χ
  let nn := (if n > z then d else 0) + m / χ
  (pp, pn, nn)

theorem lineCountsE8_eq (z n : Nat) : lineCountsE8 z n = lineCounts z n := by
  unfold lineCountsE8 lineCounts
  rw [homo_pair]

theorem lineCounts_h3 : lineCounts 1 2 = (0, 2, 1) := by decide
theorem lineCounts_he3 : lineCounts 2 1 = (1, 2, 0) := by decide
theorem lineCounts_he4 : lineCounts 2 2 = (1, 4, 1) := by decide
theorem lineCounts_c12 : lineCounts 6 6 = (3, 12, 3) := by decide
theorem lineCounts_o16 : lineCounts 8 8 = (4, 16, 4) := by decide

/-- Binding from the line/ring counts. -/
def lineBinding (wpp wpn wnn : ℝ) (z n : Nat) : ℝ :=
  let c := lineCounts z n
  wpp * (c.1 : ℝ) + wpn * (c.2.1 : ℝ) + wnn * (c.2.2 : ℝ)

/-- On the diagonal `Z=N=m`, the counts are `(m/2, 2m, m/2)`: the pure
alpha/line chain. -/
theorem lineCounts_diagonal (m : Nat) : lineCounts m m = (m / 2, 2 * m, m / 2) := by
  unfold lineCounts
  simp

/-- Charge load of a link: `pp` carries two unit charges, `pn` one, `nn` none. -/
def chargeLoad : LinkType → ℝ
  | .pp => 1
  | .pn => 0
  | .nn => 0

/-- Add a charge penalty `c` to the `pp` link. -/
def chargeWeight (w : LinkType → ℝ) (c : ℝ) : LinkType → ℝ :=
  fun t => w t + c * chargeLoad t

theorem chargeWeight_pp (w : LinkType → ℝ) (c : ℝ) :
    chargeWeight w c .pp = w .pp + c := by
  simp [chargeWeight, chargeLoad]

theorem chargeWeight_pn (w : LinkType → ℝ) (c : ℝ) :
    chargeWeight w c .pn = w .pn := by
  simp [chargeWeight, chargeLoad]

/-- Ring end cost: zero for `Z=N`, `c` for an open line. -/
def endCost (c : ℝ) (z n : Nat) : ℝ := if z = n then 0 else c

theorem endCost_ring (c : ℝ) (m : Nat) : endCost c m m = 0 := by
  simp [endCost]

theorem endCost_open (c : ℝ) {z n : Nat} (h : z ≠ n) : endCost c z n = c := by
  simp [endCost, h]

/-- Homo-capacity-capped line counts: `pp ≤ Z/2`, `nn ≤ N/2`. The excess
like-block beyond the homo capacity must use a different (saturated) arrangement. -/
def cappedLineCounts (z n : Nat) : Nat × Nat × Nat :=
  let c := lineCounts z n
  (min (z / 2) c.1, c.2.1, min (n / 2) c.2.2)

theorem capped_pp_le (z n : Nat) : (cappedLineCounts z n).1 ≤ z / 2 := by
  unfold cappedLineCounts
  exact Nat.min_le_left _ _

theorem capped_nn_le (z n : Nat) : (cappedLineCounts z n).2.2 ≤ n / 2 := by
  unfold cappedLineCounts
  exact Nat.min_le_left _ _

/-- Binding including a boundary cost for an open line (`Z ≠ N`). -/
def lineBindingEnds (wpp wpn wnn endCost : ℝ) (z n : Nat) : ℝ :=
  lineBinding wpp wpn wnn z n - (if z = n then 0 else endCost)

theorem lineBindingEnds_ring (wpp wpn wnn endCost : ℝ) (m : Nat) :
    lineBindingEnds wpp wpn wnn endCost m m = lineBinding wpp wpn wnn m m := by
  simp [lineBindingEnds]

theorem lineBindingEnds_open (wpp wpn wnn endCost : ℝ) {z n : Nat} (h : z ≠ n) :
    lineBindingEnds wpp wpn wnn endCost z n =
      lineBinding wpp wpn wnn z n - endCost := by
  simp [lineBindingEnds, h]

theorem lineBinding_he4 (wpp wpn wnn : ℝ) :
    lineBinding wpp wpn wnn 2 2 = wpp + 4 * wpn + wnn := by
  unfold lineBinding
  rw [lineCounts_he4]
  norm_num
  ring

theorem lineBinding_h3 (wpp wpn wnn : ℝ) :
    lineBinding wpp wpn wnn 1 2 = 2 * wpn + wnn := by
  unfold lineBinding
  rw [lineCounts_h3]
  norm_num
  ring

theorem lineBinding_he3 (wpp wpn wnn : ℝ) :
    lineBinding wpp wpn wnn 2 1 = wpp + 2 * wpn := by
  unfold lineBinding
  rw [lineCounts_he3]
  norm_num
  ring

/-- The line/ring counts stay inside the 3+1 channel bounds for He-4. -/
theorem lineCounts_he4_capacity :
    (lineCounts 2 2).1 ≤ homoCapacity 2 ∧
      (lineCounts 2 2).2.1 ≤ pnCapacity 2 ∧
      (lineCounts 2 2).2.2 ≤ homoCapacity 2 := by
  decide

end PMAtoms
