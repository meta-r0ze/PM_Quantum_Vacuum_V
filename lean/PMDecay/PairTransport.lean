import PMDecay.PairIsotropy

/-! # The two-neutrino pair: an actual average, frame transport, and the muon density

`PairIsotropy` derived the rest-frame pair tensor from any linear angular average with
flip and swap symmetry. `MuonRate` then consumed the coefficients `A g q² + B q q` in the
muon rest frame, where `q = p − p_e` is not at rest. This module closes the two gaps
between them.

1. `axisAverage`: an actual `AngularAverage`, the six axis directions `±eᵢ` with total
   weight `Φ`. It is an exact second-moment rule (a spherical 2-design), and the pair
   tensor only involves moments of degree ≤ 2, so on the pair tensor it agrees with the
   uniform sphere. The interface is therefore consistent, not merely assumed.
2. `transported_tensor`: for any Lorentz matrix `Λ`, the averaged tensor of the boosted pair
   is `Φ/12 g q² + Φ/6 q q` with `q = Λ(Q,0,0,0)`. It depends only on `q`
   (`frame_independent`), and the boosted members stay massless and sum to `q`.
3. `boost_lorentz`, `boost_to`: every future timelike `q` is reached from rest by an explicit
   Lorentz boost.
4. `timelike_pair`: so for every future timelike `q` the pair tensor is
   `Φ/12 g (q·q) + Φ/6 q q`. No tensor ansatz is assumed in any frame.
5. `muon_pair_contraction`, `muon_density`: contracting the amplitude
   `64 G² (p·k̄)(p_e·k)` with the transported average reproduces `MuonRate.rest_frame`, and
   with the flux and electron measure gives `MuonRate.rate` exactly.

Still supplied: the value `Φ = 1/(8π)` (`MuonRate.two_body` simplifies the solid-angle and
delta-Jacobian factors; it is not a constructed delta measure), the electron measure, and
the flux. The average is a finite exact quadrature, not a continuum integral over all
integrable test functions; for the quadratic pair tensor the two agree.
-/

noncomputable section
namespace PMDecay.PairTransport
open Matrix PMDecay.PairIsotropy PMDecay.PairIsotropy.AngularAverage

/-! ## 1. An actual angular average -/

/-- Direction component `j` of the axis sample `(a, s)`: `∓1` on axis `a`, zero elsewhere. -/
def axisDir (j : Fin 3) (ω : Fin 3 × Bool) : ℝ :=
  if ω.1 = j then (if ω.2 then -1 else 1) else 0

/-- Reverse the sign of a sample lying on axis `i`. -/
def axisFlip (i : Fin 3) (ω : Fin 3 × Bool) : Fin 3 × Bool :=
  if ω.1 = i then (ω.1, !ω.2) else ω

theorem axisFlip_involutive (i : Fin 3) : Function.Involutive (axisFlip i) := by
  rintro ⟨a, s⟩
  by_cases h : a = i
  · subst h; simp [axisFlip]
  · simp [axisFlip, h]

/-- Interchange axes `i` and `j`. -/
def axisSwap (i j : Fin 3) : Fin 3 × Bool ≃ Fin 3 × Bool :=
  Equiv.prodCongr (Equiv.swap i j) (Equiv.refl Bool)

/-- Equal weight `Φ/6` on each of the six samples. -/
def axisLinear (Φ : ℝ) : ((Fin 3 × Bool) → ℝ) →ₗ[ℝ] ℝ where
  toFun f := Φ / 6 * ∑ ω, f ω
  map_add' f g := by simp only [Pi.add_apply, Finset.sum_add_distrib]; ring
  map_smul' c f := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]; ring

/-- **The six-direction average.** -/
def axisAverage (Φ : ℝ) : AngularAverage (Fin 3 × Bool) where
  average := axisLinear Φ
  direction := axisDir
  unit_length ω := by
    rcases ω with ⟨a, s⟩
    fin_cases a <;> cases s <;> simp [axisDir]
  flip := axisFlip
  flip_invariant i f := by
    show Φ / 6 * ∑ ω, f (axisFlip i ω) = Φ / 6 * ∑ ω, f ω
    exact congrArg _ (Equiv.sum_comp ((axisFlip_involutive i).toPerm _) f)
  flip_direction i j ω := by
    rcases ω with ⟨a, s⟩
    fin_cases i <;> fin_cases j <;> fin_cases a <;> cases s <;> simp [axisDir, axisFlip]
  swap i j := axisSwap i j
  swap_invariant i j f := by
    show Φ / 6 * ∑ ω, f (axisSwap i j ω) = Φ / 6 * ∑ ω, f ω
    exact congrArg _ (Equiv.sum_comp (axisSwap i j) f)
  swap_direction i j ω := by
    rcases ω with ⟨a, s⟩
    simp [axisDir, axisSwap, Equiv.swap_apply_eq_iff]

theorem axis_volume (Φ : ℝ) : (axisAverage Φ).volume = Φ := by
  show Φ / 6 * ∑ _ω : Fin 3 × Bool, (1 : ℝ) = Φ
  simp

/-- The six-direction rule gives the rest-frame pair tensor with coefficients `Φ/12`, `Φ/6`. -/
theorem axis_rest_tensor (Φ Q : ℝ) (μ ν : Fin 4) :
    (axisAverage Φ).average (fun ω => (axisAverage Φ).leftMomentum Q ω μ *
        (axisAverage Φ).rightMomentum Q ω ν) =
      Φ/12 * metric μ ν * Q^2 + Φ/6 * restMomentum Q μ * restMomentum Q ν := by
  rw [rest_covariant, axis_volume]

/-! ## 2. Lorentz transport -/

/-- `Λ` preserves the Minkowski form. -/
def IsLorentz (Λ : Matrix (Fin 4) (Fin 4) ℝ) : Prop := Λᵀ * metric * Λ = metric

theorem metric_sq : (metric : Matrix (Fin 4) (Fin 4) ℝ) * metric = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [metric]

theorem lorentz_transpose {Λ : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz Λ) :
    Λ * metric * Λᵀ = metric := by
  have h1 : (metric * Λᵀ * metric) * Λ = 1 := by
    calc _ = metric * (Λᵀ * metric * Λ) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h, metric_sq]
  have h2 : Λ * (metric * Λᵀ * metric) = 1 := mul_eq_one_comm.mp h1
  calc Λ * metric * Λᵀ = Λ * metric * Λᵀ * (metric * metric) := by
        rw [metric_sq, Matrix.mul_one]
    _ = (Λ * (metric * Λᵀ * metric)) * metric := by simp only [Matrix.mul_assoc]
    _ = metric := by rw [h2, Matrix.one_mul]

theorem mdot_eq (u v : Fin 4 → ℝ) : MuonRate.mdot u v = u ⬝ᵥ (metric *ᵥ v) := by
  simp [MuonRate.mdot, metric, dotProduct, Fin.sum_univ_four, Matrix.mulVec_diagonal]; ring

theorem mdot_lorentz {Λ : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz Λ) (u v : Fin 4 → ℝ) :
    MuonRate.mdot (Λ *ᵥ u) (Λ *ᵥ v) = MuonRate.mdot u v := by
  rw [mdot_eq, mdot_eq, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

variable {Ω : Type*} (A : AngularAverage Ω)

/-- Boosted members stay massless. -/
theorem transported_massless {Λ : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz Λ) (Q : ℝ) (ω : Ω) :
    MuonRate.mdot (Λ *ᵥ A.leftMomentum Q ω) (Λ *ᵥ A.leftMomentum Q ω) = 0 ∧
    MuonRate.mdot (Λ *ᵥ A.rightMomentum Q ω) (Λ *ᵥ A.rightMomentum Q ω) = 0 := by
  rw [mdot_lorentz h, mdot_lorentz h]; exact A.massless_pair Q ω

/-- Boosted members sum to the boosted total momentum. -/
theorem transported_sum (Λ : Matrix (Fin 4) (Fin 4) ℝ) (Q : ℝ) (ω : Ω) :
    Λ *ᵥ A.leftMomentum Q ω + Λ *ᵥ A.rightMomentum Q ω = Λ *ᵥ restMomentum Q := by
  rw [← Matrix.mulVec_add, A.pair_sum]

theorem rest_square (Q : ℝ) : MuonRate.mdot (restMomentum Q) (restMomentum Q) = Q^2 := by
  simp [MuonRate.mdot, restMomentum]; ring

/-- **The transported pair tensor.** -/
theorem transported_tensor {Λ : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz Λ) (Q : ℝ)
    (μ ν : Fin 4) :
    A.average (fun ω => (Λ *ᵥ A.leftMomentum Q ω) μ * (Λ *ᵥ A.rightMomentum Q ω) ν) =
      A.volume/12 * metric μ ν * Q^2 +
        A.volume/6 * (Λ *ᵥ restMomentum Q) μ * (Λ *ᵥ restMomentum Q) ν := by
  have hexp : (fun ω => (Λ *ᵥ A.leftMomentum Q ω) μ * (Λ *ᵥ A.rightMomentum Q ω) ν) =
      ∑ α, ∑ β, (Λ μ α * Λ ν β) •
        (fun ω => A.leftMomentum Q ω α * A.rightMomentum Q ω β) := by
    funext ω
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => by ring
  rw [hexp, map_sum]
  simp_rw [map_sum, map_smul, smul_eq_mul, A.rest_covariant]
  have hg := congrFun (congrFun (lorentz_transpose h) μ) ν
  rw [← hg]
  simp [Matrix.mul_apply, Fin.sum_univ_four, metric, restMomentum, Matrix.mulVec, dotProduct]
  ring

/-- **Frame independence.** Any two Lorentz frames carrying the rest pair to the same `q`
give the same averaged tensor. -/
theorem frame_independent {Λ Λ' : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz Λ)
    (h' : IsLorentz Λ') (Q : ℝ) (he : Λ *ᵥ restMomentum Q = Λ' *ᵥ restMomentum Q)
    (μ ν : Fin 4) :
    A.average (fun ω => (Λ *ᵥ A.leftMomentum Q ω) μ * (Λ *ᵥ A.rightMomentum Q ω) ν) =
      A.average (fun ω => (Λ' *ᵥ A.leftMomentum Q ω) μ * (Λ' *ᵥ A.rightMomentum Q ω) ν) := by
  rw [transported_tensor A h, transported_tensor A h', he]

/-! ## 3. A boost to every future timelike momentum -/

/-- The standard boost with four-velocity `u`; `w` stands for `1/(1+u₀)`. -/
def boost (u : Fin 4 → ℝ) (w : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![u 0, u 1, u 2, u 3;
     u 1, 1 + w*u 1*u 1, w*u 1*u 2, w*u 1*u 3;
     u 2, w*u 2*u 1, 1 + w*u 2*u 2, w*u 2*u 3;
     u 3, w*u 3*u 1, w*u 3*u 2, 1 + w*u 3*u 3]

theorem boost_lorentz (u : Fin 4 → ℝ) (w : ℝ)
    (hu : u 0^2 - u 1^2 - u 2^2 - u 3^2 = 1) (hw : w * (1 + u 0) = 1) :
    IsLorentz (boost u w) := by
  unfold IsLorentz
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boost, metric, Matrix.mul_apply, Fin.sum_univ_four]
  · linear_combination hu
  · linear_combination (-(u 1*(u 0-1))) * hw + (u 1*w) * hu
  · linear_combination (-(u 2*(u 0-1))) * hw + (u 2*w) * hu
  · linear_combination (-(u 3*(u 0-1))) * hw + (u 3*w) * hu
  · linear_combination (-(u 1*(u 0-1))) * hw + (u 1*w) * hu
  · linear_combination (-(u 1*u 1*(1+w*(u 0-1)))) * hw + (u 1*u 1*w^2) * hu
  · linear_combination (-(u 1*u 2*(1+w*(u 0-1)))) * hw + (u 1*u 2*w^2) * hu
  · linear_combination (-(u 1*u 3*(1+w*(u 0-1)))) * hw + (u 1*u 3*w^2) * hu
  · linear_combination (-(u 2*(u 0-1))) * hw + (u 2*w) * hu
  · linear_combination (-(u 2*u 1*(1+w*(u 0-1)))) * hw + (u 2*u 1*w^2) * hu
  · linear_combination (-(u 2*u 2*(1+w*(u 0-1)))) * hw + (u 2*u 2*w^2) * hu
  · linear_combination (-(u 2*u 3*(1+w*(u 0-1)))) * hw + (u 2*u 3*w^2) * hu
  · linear_combination (-(u 3*(u 0-1))) * hw + (u 3*w) * hu
  · linear_combination (-(u 3*u 1*(1+w*(u 0-1)))) * hw + (u 3*u 1*w^2) * hu
  · linear_combination (-(u 3*u 2*(1+w*(u 0-1)))) * hw + (u 3*u 2*w^2) * hu
  · linear_combination (-(u 3*u 3*(1+w*(u 0-1)))) * hw + (u 3*u 3*w^2) * hu

/-- **Every future timelike momentum is a boosted rest momentum.** -/
theorem boost_to (q : Fin 4 → ℝ) (hq0 : 0 < q 0) (hs : 0 < MuonRate.mdot q q) :
    ∃ Λ, IsLorentz Λ ∧ Λ *ᵥ restMomentum (Real.sqrt (MuonRate.mdot q q)) = q := by
  set Q := Real.sqrt (MuonRate.mdot q q) with hQ
  have hQpos : 0 < Q := Real.sqrt_pos.mpr hs
  have hQ2 : Q ^ 2 = MuonRate.mdot q q := Real.sq_sqrt hs.le
  set u : Fin 4 → ℝ := fun μ => q μ / Q with hu_def
  have hu0 : 0 < u 0 := div_pos hq0 hQpos
  refine ⟨boost u (1 / (1 + u 0)), boost_lorentz u _ ?_ ?_, ?_⟩
  · simp only [hu_def, div_pow, hQ2]
    rw [div_sub_div_same, div_sub_div_same, div_sub_div_same, div_eq_one_iff_eq hs.ne']
    unfold MuonRate.mdot
    ring
  · field_simp
  · ext μ
    fin_cases μ <;>
      simp [boost, restMomentum, Matrix.mulVec, dotProduct, Fin.sum_univ_four, hu_def,
        hQpos.ne']

/-- **The pair tensor at any future timelike momentum.** There is a Lorentz frame in which
the massless pair sums to `q`, and its averaged tensor is `Φ/12 g (q·q) + Φ/6 q q`. -/
theorem timelike_pair (q : Fin 4 → ℝ) (hq0 : 0 < q 0) (hs : 0 < MuonRate.mdot q q) :
    ∃ Λ, IsLorentz Λ ∧
      (∀ ω, MuonRate.mdot (Λ *ᵥ A.leftMomentum (Real.sqrt (MuonRate.mdot q q)) ω)
          (Λ *ᵥ A.leftMomentum (Real.sqrt (MuonRate.mdot q q)) ω) = 0 ∧
        MuonRate.mdot (Λ *ᵥ A.rightMomentum (Real.sqrt (MuonRate.mdot q q)) ω)
          (Λ *ᵥ A.rightMomentum (Real.sqrt (MuonRate.mdot q q)) ω) = 0) ∧
      (∀ ω, Λ *ᵥ A.leftMomentum (Real.sqrt (MuonRate.mdot q q)) ω +
        Λ *ᵥ A.rightMomentum (Real.sqrt (MuonRate.mdot q q)) ω = q) ∧
      ∀ μ ν, A.average (fun ω =>
          (Λ *ᵥ A.leftMomentum (Real.sqrt (MuonRate.mdot q q)) ω) μ *
            (Λ *ᵥ A.rightMomentum (Real.sqrt (MuonRate.mdot q q)) ω) ν) =
        A.volume/12 * metric μ ν * MuonRate.mdot q q + A.volume/6 * q μ * q ν := by
  obtain ⟨Λ, hΛ, hq⟩ := boost_to q hq0 hs
  refine ⟨Λ, hΛ, fun ω => transported_massless A hΛ _ ω, fun ω => ?_, fun μ ν => ?_⟩
  · rw [transported_sum A, hq]
  · rw [transported_tensor A hΛ, hq, Real.sq_sqrt hs.le]

/-! ## 4. Contraction with the muon amplitude -/

/-- Averages of Minkowski products are contractions of the tensor. -/
theorem average_bilinear (F G : Ω → Fin 4 → ℝ) (x y : Fin 4 → ℝ) :
    A.average (fun ω => MuonRate.mdot x (F ω) * MuonRate.mdot y (G ω)) =
      ∑ μ, ∑ ν, (metric μ μ * x μ) * (metric ν ν * y ν) *
        A.average (fun ω => F ω μ * G ω ν) := by
  have hf : (fun ω => MuonRate.mdot x (F ω) * MuonRate.mdot y (G ω)) =
      ∑ μ, ∑ ν, ((metric μ μ * x μ) * (metric ν ν * y ν)) • (fun ω => F ω μ * G ω ν) := by
    funext ω
    simp [MuonRate.mdot, Fin.sum_univ_four, metric, Finset.sum_apply]
    ring
  rw [hf, map_sum]
  simp_rw [map_sum, map_smul, smul_eq_mul]

/-- **Pair contraction.** For any frame carrying the rest pair to `q`, the averaged
`(p_e·k)(p·k̄)` is `Φ/12 (p_e·p) q² + Φ/6 (p_e·q)(p·q)`. -/
theorem pair_contraction {Λ : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz Λ) (Q : ℝ)
    (p pe : Fin 4 → ℝ) :
    A.average (fun ω => MuonRate.mdot pe (Λ *ᵥ A.leftMomentum Q ω) *
        MuonRate.mdot p (Λ *ᵥ A.rightMomentum Q ω)) =
      A.volume/12 * MuonRate.mdot pe p * Q^2 +
        A.volume/6 * MuonRate.mdot pe (Λ *ᵥ restMomentum Q) *
          MuonRate.mdot p (Λ *ᵥ restMomentum Q) := by
  rw [average_bilinear A (fun ω => Λ *ᵥ A.leftMomentum Q ω)
    (fun ω => Λ *ᵥ A.rightMomentum Q ω)]
  simp_rw [transported_tensor A h]
  simp [Fin.sum_univ_four, metric, MuonRate.mdot]
  ring

/-- **The muon rest-frame contraction from an actual pair average.** With the two-body
volume `1/(8π)`, the averaged amplitude `64 G² (p·k̄)(p_e·k)` over the boosted pair is the
`MuonRate.rest_frame` value, for any electron energy `0 < E < m/2`. -/
theorem muon_pair_contraction (A : AngularAverage Ω) (hΦ : A.volume = 1 / (8 * Real.pi))
    (G m E : ℝ) (hE : 0 < E) (hEm : E < m / 2) :
    let p : Fin 4 → ℝ := ![m, 0, 0, 0]
    let pe : Fin 4 → ℝ := ![E, E, 0, 0]
    let q := p - pe
    ∃ Λ, IsLorentz Λ ∧
      (∀ ω, Λ *ᵥ A.leftMomentum (Real.sqrt (MuonRate.mdot q q)) ω +
        Λ *ᵥ A.rightMomentum (Real.sqrt (MuonRate.mdot q q)) ω = q) ∧
      64 * G^2 * A.average (fun ω =>
          MuonRate.mdot p (Λ *ᵥ A.rightMomentum (Real.sqrt (MuonRate.mdot q q)) ω) *
            MuonRate.mdot pe (Λ *ᵥ A.leftMomentum (Real.sqrt (MuonRate.mdot q q)) ω)) =
        64 * G ^ 2 * m ^ 2 * E * (3 * m - 4 * E) / (96 * Real.pi) := by
  intro p pe q
  have hs : 0 < MuonRate.mdot q q := by
    simp [q, p, pe, MuonRate.mdot]; nlinarith
  have hq0 : 0 < q 0 := by simp [q, p, pe]; linarith
  obtain ⟨Λ, hΛ, hq⟩ := boost_to q hq0 hs
  refine ⟨Λ, hΛ, fun ω => by rw [transported_sum A, hq], ?_⟩
  have hswap : (fun ω =>
        MuonRate.mdot p (Λ *ᵥ A.rightMomentum (Real.sqrt (MuonRate.mdot q q)) ω) *
          MuonRate.mdot pe (Λ *ᵥ A.leftMomentum (Real.sqrt (MuonRate.mdot q q)) ω)) =
      (fun ω => MuonRate.mdot pe (Λ *ᵥ A.leftMomentum (Real.sqrt (MuonRate.mdot q q)) ω) *
          MuonRate.mdot p (Λ *ᵥ A.rightMomentum (Real.sqrt (MuonRate.mdot q q)) ω)) := by
    funext ω; ring
  rw [hswap, pair_contraction A hΛ, hq, Real.sq_sqrt hs.le, hΦ]
  have := MuonRate.rest_frame G m E
  simp only at this
  rw [← this]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  simp only [p, pe, q, MuonRate.mdot, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  field_simp
  ring

/-- **The muon electron spectrum from the pair average.** Flux × electron measure ×
averaged amplitude is `MuonRate.rate`. -/
theorem muon_density (A : AngularAverage Ω) (hΦ : A.volume = 1 / (8 * Real.pi))
    (G m E : ℝ) (hE : 0 < E) (hEm : E < m / 2) :
    let p : Fin 4 → ℝ := ![m, 0, 0, 0]
    let pe : Fin 4 → ℝ := ![E, E, 0, 0]
    let q := p - pe
    ∃ Λ, IsLorentz Λ ∧
      1 / (2 * m) * (E / (4 * Real.pi ^ 2)) * (64 * G^2 * A.average (fun ω =>
          MuonRate.mdot p (Λ *ᵥ A.rightMomentum (Real.sqrt (MuonRate.mdot q q)) ω) *
            MuonRate.mdot pe (Λ *ᵥ A.leftMomentum (Real.sqrt (MuonRate.mdot q q)) ω))) =
        MuonRate.rate G m E := by
  intro p pe q
  obtain ⟨Λ, hΛ, -, hc⟩ := muon_pair_contraction A hΦ G m E hE hEm
  refine ⟨Λ, hΛ, ?_⟩
  rw [hc]
  exact MuonRate.rate_density G m E (by linarith)

/-- The concrete six-direction average with the two-body volume. -/
theorem axis_muon_density (G m E : ℝ) (hE : 0 < E) (hEm : E < m / 2) :
    let A := axisAverage (1 / (8 * Real.pi))
    let p : Fin 4 → ℝ := ![m, 0, 0, 0]
    let pe : Fin 4 → ℝ := ![E, E, 0, 0]
    let q := p - pe
    ∃ Λ, IsLorentz Λ ∧
      1 / (2 * m) * (E / (4 * Real.pi ^ 2)) * (64 * G^2 * A.average (fun ω =>
          MuonRate.mdot p (Λ *ᵥ A.rightMomentum (Real.sqrt (MuonRate.mdot q q)) ω) *
            MuonRate.mdot pe (Λ *ᵥ A.leftMomentum (Real.sqrt (MuonRate.mdot q q)) ω))) =
        MuonRate.rate G m E :=
  muon_density _ (axis_volume _) G m E hE hEm

end PMDecay.PairTransport
