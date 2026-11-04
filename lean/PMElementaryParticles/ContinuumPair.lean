import PMElementaryParticles.MassiveDaughterSpectrum

/-!
# Continuum angular integration for a massless pair

Use the solid-angle coordinates z = cos θ, φ ∈ [0, 2π], z ∈ [−1, 1].
The iterated Lebesgue integral below is an actual continuum average, unlike the
six-point quadrature. Its volume and all moments needed by the pair tensor
are evaluated exactly. No linearity is asserted for arbitrary nonintegrable
functions, and no delta-function integral is hidden in this definition.

The reduced angular density 1/(32π²) is a stated measure convention. Deriving
it from a substrate state count, and proving the radial energy-shell reduction
and three-body factorization, remain separate obligations.
-/
noncomputable section
namespace PMElementaryParticles.ContinuumPair
open Matrix intervalIntegral PairIsotropy PairIsotropy.AngularAverage

def solidAngle (f : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in (-1 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi), f z φ

def average (f : ℝ → ℝ → ℝ) : ℝ := solidAngle f / (32 * Real.pi ^ 2)

def direction (i : Fin 3) (z φ : ℝ) : ℝ :=
  ![Real.sqrt (1 - z ^ 2) * Real.cos φ,
    Real.sqrt (1 - z ^ 2) * Real.sin φ, z] i

theorem average_nonnegative (f : ℝ → ℝ → ℝ)
    (hf : ∀ z ∈ Set.Icc (-1 : ℝ) 1, ∀ φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi), 0 ≤ f z φ) :
    0 ≤ average f := by
  apply div_nonneg _ (by positivity : (0 : ℝ) ≤ 32 * Real.pi ^ 2)
  apply integral_nonneg (by norm_num)
  intro z hz
  exact integral_nonneg (by positivity) (hf z hz)

theorem unit_direction (z φ : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    ∑ i, direction i z φ ^ 2 = 1 := by
  have hs : Real.sqrt (1 - z ^ 2) ^ 2 = 1 - z ^ 2 :=
    Real.sq_sqrt (by nlinarith [hz.1, hz.2])
  simp only [direction, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, mul_pow]
  rw [hs]
  nlinarith [Real.sin_sq_add_cos_sq φ]

theorem solidAngle_separable (a b : ℝ → ℝ) :
    solidAngle (fun z φ => a z * b φ) =
      (∫ z in (-1 : ℝ)..1, a z) * (∫ φ in (0 : ℝ)..(2 * Real.pi), b φ) := by
  simp only [solidAngle, integral_const_mul, integral_mul_const]

theorem average_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    average (fun z φ => c * f z φ) = c * average f := by
  simp only [average, solidAngle, integral_const_mul]
  ring

theorem inner_continuous (f : ℝ → ℝ → ℝ) (hf : Continuous f.uncurry) :
    Continuous (fun z => ∫ φ in (0 : ℝ)..(2 * Real.pi), f z φ) := by
  simp_rw [integral_of_le (show (0 : ℝ) ≤ 2 * Real.pi by positivity),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact continuous_parametric_integral_of_continuous hf isCompact_Icc

/-- Linearity is proved on continuous test functions, where both integrals are
integrable on their compact intervals. -/
theorem average_add (f g : ℝ → ℝ → ℝ) (hf : Continuous f.uncurry)
    (hg : Continuous g.uncurry) :
    average (fun z φ => f z φ + g z φ) = average f + average g := by
  have hfc (z : ℝ) : Continuous (f z) := hf.comp (continuous_const.prodMk continuous_id)
  have hgc (z : ℝ) : Continuous (g z) := hg.comp (continuous_const.prodMk continuous_id)
  have hi (z : ℝ) : (∫ φ in (0 : ℝ)..(2 * Real.pi), f z φ + g z φ) =
      (∫ φ in (0 : ℝ)..(2 * Real.pi), f z φ) +
        (∫ φ in (0 : ℝ)..(2 * Real.pi), g z φ) :=
    integral_add ((hfc z).intervalIntegrable _ _) ((hgc z).intervalIntegrable _ _)
  unfold average solidAngle
  simp_rw [hi]
  rw [integral_add ((inner_continuous f hf).intervalIntegrable _ _)
    ((inner_continuous g hg).intervalIntegrable _ _)]
  ring

theorem average_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ → ℝ)
    (hf : ∀ i, Continuous (f i).uncurry) :
    average (fun z φ => ∑ i ∈ s, f i z φ) = ∑ i ∈ s, average (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [average, solidAngle]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    have hsum : Continuous (Function.uncurry (fun z φ => ∑ j ∈ s, f j z φ)) := by
      fun_prop
    rw [average_add (f i) _ (hf i) hsum, ih]

theorem volume : average (fun _ _ => 1) = 1 / (8 * Real.pi) := by
  simp only [average, solidAngle, integral_const, sub_zero, sub_neg_eq_add]
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

theorem constant (c : ℝ) : average (fun _ _ => c) = c / (8 * Real.pi) := by
  have h := average_const_mul c (fun _ _ => 1)
  simpa only [mul_one, volume, mul_one_div] using h

theorem azimuth_cos : (∫ φ in (0 : ℝ)..(2 * Real.pi), Real.cos φ) = 0 := by
  simp [integral_cos]

theorem azimuth_sin : (∫ φ in (0 : ℝ)..(2 * Real.pi), Real.sin φ) = 0 := by
  simp [integral_sin]

theorem azimuth_cos_sq : (∫ φ in (0 : ℝ)..(2 * Real.pi), Real.cos φ ^ 2) = Real.pi := by
  simp [integral_cos_sq]

theorem azimuth_sin_sq : (∫ φ in (0 : ℝ)..(2 * Real.pi), Real.sin φ ^ 2) = Real.pi := by
  simp [integral_sin_sq]

theorem azimuth_cross :
    (∫ φ in (0 : ℝ)..(2 * Real.pi), Real.cos φ * Real.sin φ) = 0 := by
  simp_rw [mul_comm (Real.cos _) (Real.sin _)]
  simp [integral_sin_mul_cos₁]

theorem first_moment (i : Fin 3) : average (direction i) = 0 := by
  fin_cases i
  · simp [average, solidAngle, direction, integral_const_mul]
  · simp [average, solidAngle, direction, integral_const_mul]
  · simp [average, solidAngle, direction]
    rw [integral_const_mul, integral_id]
    norm_num

theorem second_moment (i j : Fin 3) :
    average (fun z φ => direction i z φ * direction j z φ) =
      if i = j then 1 / (24 * Real.pi) else 0 := by
  have hsq (z : ℝ) (hz : z ∈ Set.uIcc (-1 : ℝ) 1) :
      Real.sqrt (1 - z ^ 2) ^ 2 = 1 - z ^ 2 := by
    rw [Set.uIcc_of_le (by norm_num)] at hz
    exact Real.sq_sqrt (by nlinarith [hz.1, hz.2])
  have hdiag (b : ℝ → ℝ)
      (hb : (∫ φ in (0 : ℝ)..(2 * Real.pi), b φ ^ 2) = Real.pi) :
      average (fun z φ => (Real.sqrt (1 - z ^ 2) * b φ) ^ 2) =
        1 / (24 * Real.pi) := by
    unfold average solidAngle
    simp_rw [mul_pow, integral_const_mul, hb]
    have he : (∫ z in (-1 : ℝ)..1, Real.sqrt (1 - z ^ 2) ^ 2 * Real.pi) =
        ∫ z in (-1 : ℝ)..1, (1 - z ^ 2) * Real.pi := by
      apply integral_congr
      intro z hz
      change Real.sqrt (1 - z ^ 2) ^ 2 * Real.pi = (1 - z ^ 2) * Real.pi
      rw [hsq z hz]
    rw [he, integral_mul_const, integral_sub, integral_const, integral_pow]
    · have hp : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp
      ring
    all_goals
      apply Continuous.intervalIntegrable
      fun_prop
  have hcross : average (fun z φ => (Real.sqrt (1 - z ^ 2) * Real.cos φ) *
      (Real.sqrt (1 - z ^ 2) * Real.sin φ)) = 0 := by
    have he : (fun z φ => (Real.sqrt (1 - z ^ 2) * Real.cos φ) *
        (Real.sqrt (1 - z ^ 2) * Real.sin φ)) =
        (fun z φ => Real.sqrt (1 - z ^ 2) ^ 2 * (Real.cos φ * Real.sin φ)) := by
      funext z φ
      ring
    rw [he]
    simp [average, solidAngle, integral_const_mul, azimuth_cross]
  have hmix (b : ℝ → ℝ) (hb : (∫ φ in (0 : ℝ)..(2 * Real.pi), b φ) = 0) :
      average (fun z φ => (Real.sqrt (1 - z ^ 2) * b φ) * z) = 0 := by
    have he : (fun z φ => (Real.sqrt (1 - z ^ 2) * b φ) * z) =
        (fun z φ => (Real.sqrt (1 - z ^ 2) * z) * b φ) := by funext z φ; ring
    rw [he]
    simp [average, solidAngle, integral_const_mul, hb]
  have hz : average (fun z _ => z ^ 2) = 1 / (24 * Real.pi) := by
    simp only [average, solidAngle, integral_const, sub_zero, smul_eq_mul]
    rw [integral_const_mul, integral_pow]
    have hp : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  fin_cases i <;> fin_cases j
  · simpa [direction, ← pow_two] using hdiag Real.cos azimuth_cos_sq
  · simpa [direction] using hcross
  · simpa [direction] using hmix Real.cos azimuth_cos
  · simpa [direction, mul_comm] using hcross
  · simpa [direction, ← pow_two] using hdiag Real.sin azimuth_sin_sq
  · simpa [direction] using hmix Real.sin azimuth_sin
  · simpa [direction, mul_comm] using hmix Real.cos azimuth_cos
  · simpa [direction, mul_comm] using hmix Real.sin azimuth_sin
  · simpa [direction, ← pow_two] using hz

def left (Q z φ : ℝ) : Fin 4 → ℝ :=
  ![Q / 2, Q / 2 * direction 0 z φ, Q / 2 * direction 1 z φ, Q / 2 * direction 2 z φ]

def right (Q z φ : ℝ) : Fin 4 → ℝ :=
  ![Q / 2, -Q / 2 * direction 0 z φ, -Q / 2 * direction 1 z φ, -Q / 2 * direction 2 z φ]

theorem pair_sum (Q z φ : ℝ) : left Q z φ + right Q z φ = restMomentum Q := by
  ext i
  fin_cases i <;> simp [left, right, restMomentum] <;> ring

theorem pair_massless (Q z φ : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    MuonRate.mdot (left Q z φ) (left Q z φ) = 0 ∧
      MuonRate.mdot (right Q z φ) (right Q z φ) = 0 := by
  have hu := unit_direction z φ hz
  simp only [Fin.sum_univ_three] at hu
  constructor <;> simp only [left, right, MuonRate.mdot, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons] <;> nlinarith [hu]

theorem transported_massless {Λ : Matrix (Fin 4) (Fin 4) ℝ}
    (h : PairTransport.IsLorentz Λ) (Q z φ : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    MuonRate.mdot (Λ *ᵥ left Q z φ) (Λ *ᵥ left Q z φ) = 0 ∧
      MuonRate.mdot (Λ *ᵥ right Q z φ) (Λ *ᵥ right Q z φ) = 0 := by
  simpa only [PairTransport.mdot_lorentz h] using pair_massless Q z φ hz

/-- The covariant rest-pair tensor now as a continuum integral, with its volume
evaluated instead of supplied as an angular-average hypothesis. -/
theorem rest_tensor (Q : ℝ) (μ ν : Fin 4) :
    average (fun z φ => left Q z φ μ * right Q z φ ν) =
      1 / (96 * Real.pi) * metric μ ν * Q ^ 2 +
        1 / (48 * Real.pi) * restMomentum Q μ * restMomentum Q ν := by
  have hl (c : ℝ) (i : Fin 3) : average (fun z φ => c * direction i z φ) = 0 := by
    rw [average_const_mul, first_moment, mul_zero]
  have hcl (a b : ℝ) (i : Fin 3) :
      average (fun z φ => a * (b * direction i z φ)) = 0 := by
    simpa only [← mul_assoc] using hl (a * b) i
  have hlc (a b : ℝ) (i : Fin 3) :
      average (fun z φ => (a * direction i z φ) * b) = 0 := by
    have he : (fun z φ => (a * direction i z φ) * b) =
        (fun z φ => (a * b) * direction i z φ) := by funext z φ; ring
    rw [he, hl]
  have hll (a b : ℝ) (i j : Fin 3) :
      average (fun z φ => (a * direction i z φ) * (b * direction j z φ)) =
        (a * b) * (if i = j then 1 / (24 * Real.pi) else 0) := by
    have he : (fun z φ => (a * direction i z φ) * (b * direction j z φ)) =
        (fun z φ => (a * b) * (direction i z φ * direction j z φ)) := by funext z φ; ring
    rw [he, average_const_mul, second_moment]
  fin_cases μ <;> fin_cases ν <;>
    simp [left, right, metric, restMomentum, constant, hcl, hlc, hll] <;> ring

theorem left_continuous (Q : ℝ) (i : Fin 4) :
    Continuous (Function.uncurry (fun z φ => left Q z φ i)) := by
  fin_cases i <;> simp only [left, direction, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> fun_prop

theorem right_continuous (Q : ℝ) (i : Fin 4) :
    Continuous (Function.uncurry (fun z φ => right Q z φ i)) := by
  fin_cases i <;> simp only [right, direction, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> fun_prop

/-- Transporting the actual integral gives the same tensor in any Lorentz frame. -/
theorem transported_tensor {Λ : Matrix (Fin 4) (Fin 4) ℝ}
    (h : PairTransport.IsLorentz Λ) (Q : ℝ) (μ ν : Fin 4) :
    average (fun z φ => (Λ *ᵥ left Q z φ) μ * (Λ *ᵥ right Q z φ) ν) =
      1 / (96 * Real.pi) * metric μ ν * Q ^ 2 +
        1 / (48 * Real.pi) * (Λ *ᵥ restMomentum Q) μ * (Λ *ᵥ restMomentum Q) ν := by
  have hexp : (fun z φ => (Λ *ᵥ left Q z φ) μ * (Λ *ᵥ right Q z φ) ν) =
      (fun z φ => ∑ a, ∑ b, (Λ μ a * Λ ν b) * (left Q z φ a * right Q z φ b)) := by
    funext z φ
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [hexp, average_sum]
  · have hc (a b : Fin 4) : Continuous (Function.uncurry
        (fun z φ => (Λ μ a * Λ ν b) * (left Q z φ a * right Q z φ b))) :=
      continuous_const.mul ((left_continuous Q a).mul (right_continuous Q b))
    have ha (a : Fin 4) :
        average (fun z φ => ∑ b, (Λ μ a * Λ ν b) * (left Q z φ a * right Q z φ b)) =
          ∑ b, (Λ μ a * Λ ν b) *
            (1 / (96 * Real.pi) * metric a b * Q ^ 2 +
              1 / (48 * Real.pi) * restMomentum Q a * restMomentum Q b) := by
      rw [average_sum _ _ (hc a)]
      simp_rw [average_const_mul, rest_tensor]
    simp_rw [ha]
    have hg := congrFun (congrFun (PairTransport.lorentz_transpose h) μ) ν
    rw [← hg]
    simp [Matrix.mul_apply, Fin.sum_univ_four, metric, restMomentum, Matrix.mulVec, dotProduct]
    ring
  · intro a
    have hc (b : Fin 4) : Continuous (Function.uncurry
        (fun z φ => (Λ μ a * Λ ν b) * (left Q z φ a * right Q z φ b))) :=
      continuous_const.mul ((left_continuous Q a).mul (right_continuous Q b))
    fun_prop

/-- Products of continuous vector fields are integrated component by component. -/
theorem average_bilinear (F G : ℝ → ℝ → Fin 4 → ℝ)
    (hF : ∀ i, Continuous (Function.uncurry (fun z φ => F z φ i)))
    (hG : ∀ i, Continuous (Function.uncurry (fun z φ => G z φ i)))
    (x y : Fin 4 → ℝ) :
    average (fun z φ => MuonRate.mdot x (F z φ) * MuonRate.mdot y (G z φ)) =
      ∑ i, ∑ j, (metric i i * x i) * (metric j j * y j) *
        average (fun z φ => F z φ i * G z φ j) := by
  have he : (fun z φ => MuonRate.mdot x (F z φ) * MuonRate.mdot y (G z φ)) =
      (fun z φ => ∑ i, ∑ j, ((metric i i * x i) * (metric j j * y j)) *
        (F z φ i * G z φ j)) := by
    funext z φ
    simp [MuonRate.mdot, Fin.sum_univ_four, metric]
    ring
  have hc (i j : Fin 4) : Continuous (Function.uncurry
      (fun z φ => ((metric i i * x i) * (metric j j * y j)) * (F z φ i * G z φ j))) :=
    continuous_const.mul ((hF i).mul (hG j))
  rw [he, average_sum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [average_sum _ _ (hc i)]
    simp_rw [average_const_mul]
  · intro i
    fun_prop

theorem transported_left_continuous (Λ : Matrix (Fin 4) (Fin 4) ℝ) (Q : ℝ) (i : Fin 4) :
    Continuous (Function.uncurry (fun z φ => (Λ *ᵥ left Q z φ) i)) := by
  have hc := left_continuous Q
  simp only [Matrix.mulVec, dotProduct]
  fun_prop

theorem transported_right_continuous (Λ : Matrix (Fin 4) (Fin 4) ℝ) (Q : ℝ) (i : Fin 4) :
    Continuous (Function.uncurry (fun z φ => (Λ *ᵥ right Q z φ) i)) := by
  have hc := right_continuous Q
  simp only [Matrix.mulVec, dotProduct]
  fun_prop

/-- The full continuum angular integral of the contact amplitude's two
Minkowski products. -/
theorem pair_contraction {Λ : Matrix (Fin 4) (Fin 4) ℝ}
    (h : PairTransport.IsLorentz Λ) (Q : ℝ) (p pe : Fin 4 → ℝ) :
    average (fun z φ => MuonRate.mdot pe (Λ *ᵥ left Q z φ) *
      MuonRate.mdot p (Λ *ᵥ right Q z φ)) =
      1 / (96 * Real.pi) * MuonRate.mdot pe p * Q ^ 2 +
        1 / (48 * Real.pi) * MuonRate.mdot pe (Λ *ᵥ restMomentum Q) *
          MuonRate.mdot p (Λ *ᵥ restMomentum Q) := by
  rw [average_bilinear _ _ (transported_left_continuous Λ Q)
    (transported_right_continuous Λ Q)]
  simp_rw [transported_tensor h]
  simp [Fin.sum_univ_four, metric, MuonRate.mdot]
  ring

/-- Both the massive-daughter spectrum and its previously proved width now
have an actual continuum pair integral behind them. Parent flux and the
charged-daughter radial measure still retain their supplied normalizations. -/
theorem massive_density (G m μ E : ℝ) (hμ : 0 ≤ μ) (hm : μ < m)
    (hE : μ < E) (hEnd : E < MassiveDaughterSpectrum.endpoint m μ) :
    let p : Fin 4 → ℝ := ![m, 0, 0, 0]
    let pe : Fin 4 → ℝ := ![E, MassiveDaughterSpectrum.momentum μ E, 0, 0]
    let q := p - pe
    ∃ Λ, PairTransport.IsLorentz Λ ∧
      (∀ z φ, Λ *ᵥ left (Real.sqrt (MuonRate.mdot q q)) z φ +
        Λ *ᵥ right (Real.sqrt (MuonRate.mdot q q)) z φ = q) ∧
      1 / (2 * m) * (MassiveDaughterSpectrum.momentum μ E / (4 * Real.pi ^ 2)) *
        (64 * G ^ 2 * average (fun z φ =>
          MuonRate.mdot pe (Λ *ᵥ left (Real.sqrt (MuonRate.mdot q q)) z φ) *
            MuonRate.mdot p (Λ *ᵥ right (Real.sqrt (MuonRate.mdot q q)) z φ))) =
              MassiveDaughterSpectrum.rate G m μ E := by
  intro p pe q
  have hm0 : 0 < m := lt_of_le_of_lt hμ hm
  have hP := MassiveDaughterSpectrum.momentum_shell μ E (by nlinarith)
  have hq := (MassiveDaughterSpectrum.kinematics m μ E
    (MassiveDaughterSpectrum.momentum μ E) hP).2
  have hs : 0 < MuonRate.mdot q q := by
    rw [hq]
    have he := (lt_div_iff₀ (by positivity : 0 < 2 * m)).mp hEnd
    nlinarith
  have hq0 : 0 < q 0 := by
    have := (MassiveDaughterSpectrum.threshold m μ hm0 hμ hm).2
    dsimp [q, p, pe]
    linarith
  obtain ⟨Λ, hΛ, hboost⟩ := PairTransport.boost_to q hq0 hs
  refine ⟨Λ, hΛ, fun z φ => ?_, ?_⟩
  · rw [← Matrix.mulVec_add, pair_sum, hboost]
  · rw [pair_contraction hΛ, hboost, Real.sq_sqrt hs.le]
    have hc := MassiveDaughterSpectrum.rest_contraction G m μ E
      (MassiveDaughterSpectrum.momentum μ E) hP
    dsimp only at hc
    have hcoef : (1 : ℝ) / (48 * Real.pi) = 2 / (96 * Real.pi) := by ring
    rw [hcoef, hc]
    exact MassiveDaughterSpectrum.density G m μ E hm0.ne'

end PMElementaryParticles.ContinuumPair
