import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
namespace PMDecay.Survival

def survive (rate time : ℝ) : ℝ := Real.exp (-rate*time)
def timeConstant (rate : ℝ) : ℝ := 1/rate
def halfTime (rate : ℝ) : ℝ := Real.log 2/rate

theorem positive (rate time : ℝ) : 0 < survive rate time := Real.exp_pos _

theorem bounded {rate time : ℝ} (hr : 0 ≤ rate) (ht : 0 ≤ time) :
    0 < survive rate time ∧ survive rate time ≤ 1 := by
  refine ⟨positive _ _, ?_⟩
  unfold survive
  exact Real.exp_le_one_iff.mpr (by nlinarith)

theorem memoryless (rate t u : ℝ) : survive rate (t+u) = survive rate t * survive rate u := by
  simp only [survive, ← Real.exp_add]
  congr 1
  ring

theorem competing_hazards (a b t : ℝ) : survive (a+b) t = survive a t * survive b t := by
  simp only [survive, ← Real.exp_add]
  congr 1
  ring

theorem zero_rate (t : ℝ) : survive 0 t = 1 := by simp [survive]

theorem at_time_constant {rate : ℝ} (hr : 0 < rate) :
    survive rate (timeConstant rate) = Real.exp (-1) := by
  unfold survive timeConstant
  congr 1
  field_simp

theorem at_half_time {rate : ℝ} (hr : 0 < rate) :
    survive rate (halfTime rate) = 1/2 := by
  have he : -rate*(Real.log 2/rate) = -Real.log 2 := by field_simp
  rw [survive, halfTime, he, Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num

theorem half_time_relation (rate : ℝ) : halfTime rate = timeConstant rate * Real.log 2 := by
  unfold halfTime timeConstant
  ring

/-- Determinism of an update alone does not give a nonzero decay hazard. -/
theorem deterministic_state_can_remain :
    ∃ update : Bool → Bool, (∀ x, update x = x) ∧ ∀ n, update^[n] true = true := by
  refine ⟨id, fun _ => rfl, ?_⟩
  intro n
  simp

end PMDecay.Survival
