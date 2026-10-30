import Mathlib.Tactic

namespace PMDecay.Routing

/-- These fields are explicit modeling hypotheses, not global axioms. -/
structure Model (State Label : Type*) where
  latency : State → ℕ
  label : State → Label
  step : State → State → Prop
  descends : ∀ {s t}, step s t → latency t < latency s
  preserves : ∀ {s t}, step s t → label t = label s

variable {State Label : Type*} (M : Model State Label)

def Terminal (s : State) : Prop := ∀ t, ¬ M.step s t

theorem minimum_terminal (s : State)
    (hmin : ∀ t, M.label t = M.label s → M.latency s ≤ M.latency t) : Terminal M s := by
  intro t ht
  have := M.descends ht
  have := hmin t (M.preserves ht)
  omega

theorem trace_bound (s : ℕ → State) : ∀ n,
    (∀ i, i < n → M.step (s i) (s (i+1))) → M.latency (s n)+n ≤ M.latency (s 0) := by
  intro n
  induction n with
  | zero => intro h; simp
  | succ n ih =>
    intro h
    have hp := ih (fun i hi => h i (by omega))
    have hl := M.descends (h n (by omega))
    omega

theorem trace_conserves (s : ℕ → State) : ∀ n,
    (∀ i, i < n → M.step (s i) (s (i+1))) → M.label (s n) = M.label (s 0) := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
    intro h
    exact (M.preserves (h n (by omega))).trans (ih (fun i hi => h i (by omega)))

theorem no_infinite_descent (s : ℕ → State) : ¬ ∀ i, M.step (s i) (s (i+1)) := by
  intro h
  have hb := trace_bound M s (M.latency (s 0)+1) (fun i _ => h i)
  omega

/-- Strictly positive individual costs need not have a positive uniform gap. -/
theorem positive_costs_without_gap (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < 1/((n : ℝ)+1) ∧ 1/((n : ℝ)+1) < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1/ε)
  refine ⟨n, by positivity, ?_⟩
  apply (div_lt_iff₀ (show 0 < (n : ℝ)+1 by positivity)).mpr
  have h := (div_lt_iff₀ hε).mp hn
  nlinarith

end PMDecay.Routing
