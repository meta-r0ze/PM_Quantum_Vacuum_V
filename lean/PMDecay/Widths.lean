import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

noncomputable section
namespace PMDecay.Widths
open Finset

def lifetime (hbar width : ℝ) : ℝ := hbar/width

theorem lifetime_pos {hbar width : ℝ} (hh : 0 < hbar) (hw : 0 < width) :
    0 < lifetime hbar width := div_pos hh hw

theorem lifetime_rescale (hbar width k : ℝ) :
    lifetime hbar (width*k) = lifetime hbar width/k := by
  simp only [lifetime, div_div]

theorem width_lifetime_order {hbar a b : ℝ} (hh : 0 ≤ hbar) (ha : 0 < a) (hab : a ≤ b) :
    lifetime hbar b ≤ lifetime hbar a := by
  unfold lifetime
  apply (div_le_div_iff₀ (by linarith : 0 < b) ha).mpr
  nlinarith

def total {ι : Type*} [Fintype ι] (width : ι → ℝ) : ℝ := ∑ i, width i

def branching {ι : Type*} [Fintype ι] (width : ι → ℝ) (i : ι) : ℝ := width i/total width

theorem branching_normalized {ι : Type*} [Fintype ι] (width : ι → ℝ)
    (ht : 0 < total width) : ∑ i, branching width i = 1 := by
  simp only [branching, ← sum_div]
  exact div_self (ne_of_gt ht)

theorem branching_nonnegative {ι : Type*} [Fintype ι] (width : ι → ℝ)
    (hw : ∀ i, 0 ≤ width i) (ht : 0 < total width) (i : ι) : 0 ≤ branching width i :=
  div_nonneg (hw i) (le_of_lt ht)

theorem identical_channels (n : ℕ) (g : ℝ) : total (fun _ : Fin n => g) = n*g := by
  simp [total]

def referenceWidth (base ratio mixing channels phase : ℝ) : ℝ :=
  base*ratio^5*mixing^2*channels*phase

theorem reference_width_pos {base ratio mixing channels phase : ℝ}
    (hb : 0 < base) (hr : 0 < ratio) (hv : mixing ≠ 0)
    (hc : 0 < channels) (hp : 0 < phase) :
    0 < referenceWidth base ratio mixing channels phase := by
  unfold referenceWidth
  positivity

theorem smaller_phase_longer_life {hbar base ratio mixing channels F G : ℝ}
    (hh : 0 ≤ hbar) (hb : 0 < base) (hr : 0 < ratio) (hv : mixing ≠ 0)
    (hc : 0 < channels) (hf : 0 < F) (hfg : F ≤ G) :
    lifetime hbar (referenceWidth base ratio mixing channels G) ≤
      lifetime hbar (referenceWidth base ratio mixing channels F) := by
  apply width_lifetime_order hh (reference_width_pos hb hr hv hc hf)
  unfold referenceWidth
  exact mul_le_mul_of_nonneg_left hfg (by positivity)

def neutronFactor : ℝ := 43/(43-2/5)

theorem neutron_factor_exact : neutronFactor = 215/213 ∧ 1 < neutronFactor := by
  norm_num [neutronFactor]

theorem neutron_lifetime_rescaling (hbar width : ℝ) :
    lifetime hbar (width/neutronFactor) = neutronFactor*lifetime hbar width := by
  simp only [lifetime, div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

end PMDecay.Widths
