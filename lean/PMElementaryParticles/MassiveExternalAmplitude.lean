import PMAction.AmplitudeTrace
import PMElementaryParticles.MuonAmplitude

/-!
# V−A spin sums with all four external masses retained

Paper II supplies completeness and the bilinear-to-trace bridge. Chirality also
removes the mass in the *first* slot of each current trace, by cyclicity. Thus
the squared contact amplitude retains its dot-product form for arbitrary real
external masses. This does not make the rate mass-independent: the momenta,
thresholds and phase-space measure still depend on those masses.

The vertex, positive on-shell energies, complete kernel bases, and the initial
spin average remain explicit inputs. No substrate interaction is selected here.
-/
noncomputable section
namespace PMElementaryParticles.MassiveExternalAmplitude
open Matrix PMAction ConcreteFermion VATrace SpinorCompleteness AmplitudeTrace

/-- The terminal chiral factor can be cycled to kill a first-slot scalar mass. -/
theorem first_mass_zero (X : Spin) (μ ν : Fin 4) :
    (g μ * L * X * g ν * L).trace = 0 := by
  rw [trace_mul_comm]
  have h : L * (g μ * L * X * g ν) = (L * g μ * L) * X * g ν := by
    simp only [Matrix.mul_assoc]
  rw [h, MassiveVATrace.chiral_vertex_zero]
  simp

/-- Both explicit masses cancel independently, including their cross term. -/
theorem current_masses_cancel (a b : Fin 4 → ℂ) (ma mb : ℂ) (μ ν : Fin 4) :
    ((sl a + ma • (1 : Spin)) * g μ * L *
      (sl b + mb • (1 : Spin)) * g ν * L).trace = W a b μ ν := by
  have hm : ∀ X : Spin,
      ((ma • (1 : Spin)) * g μ * L * X * g ν * L).trace = 0 := by
    intro X
    simp only [Matrix.smul_mul, Matrix.one_mul, trace_smul, first_mass_zero, smul_zero]
  rw [Matrix.add_mul, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul,
    Matrix.add_mul, trace_add, hm, add_zero]
  exact MassiveVATrace.mass_cancels a b mb μ ν

variable {ιk ιp ιe ιb : Type*} [Fintype ιk] [Fintype ιp] [Fintype ιe] [Fintype ιb]
  [DecidableEq ιk] [DecidableEq ιp] [DecidableEq ιe] [DecidableEq ιb]

/-- Actual bilinear amplitudes, now allowing masses for the electron and neutrino
as well as the muon and antineutrino. The antineutrino basis uses signed mass −mb. -/
theorem spin_averaged (G mk mp me mb : ℝ) (pk pp pe pb : Fin 4 → ℝ)
    (ek : ιk → Fin 4 → ℂ) (ep : ιp → Fin 4 → ℂ)
    (ee : ιe → Fin 4 → ℂ) (eb : ιb → Fin 4 → ℂ)
    (hk0 : 0 < pk 0) (hp0 : 0 < pp 0) (he0 : 0 < pe 0) (hb0 : 0 < pb 0)
    (hk : msq pk = mk ^ 2) (hp : msq pp = mp ^ 2)
    (he : msq pe = me ^ 2) (hb : msq pb = mb ^ 2)
    (bk : Basis pk mk ek) (bp : Basis pp mp ep)
    (be : Basis pe me ee) (bb : Basis pb (-mb) eb) :
    ((∑ x, Complex.normSq (amp G (norm pk ek) (norm pp ep)
        (norm pe ee) (norm pb eb) x) : ℝ) : ℂ) / 2 =
      64 * (G : ℂ) ^ 2 * mdot (cp pp) (cp pb) * mdot (cp pe) (cp pk) := by
  have hb' : msq pb = (-mb) ^ 2 := by rw [hb]; ring
  have Ok := outer_of_basis pk mk ek hk0 hk bk
  have Op := outer_of_basis pp mp ep hp0 hp bp
  have Oe := outer_of_basis pe me ee he0 he be
  have Ob := outer_of_basis pb (-mb) eb hb0 hb' bb
  push_cast
  simp only [← Complex.mul_conj]
  change (∑ x, amp G (norm pk ek) (norm pp ep) (norm pe ee) (norm pb eb) x *
    star (amp G (norm pk ek) (norm pp ep) (norm pe ee) (norm pb eb) x)) / 2 = _
  rw [amp_sum]
  simp only [current_trace, Ok, Op, Oe, Ob, A, reduce, P, current_masses_cancel]
  exact (muon_amplitude (G : ℂ) (cp pp) (cp pe) (cp pk) (cp pb)).2

/-- The same result in the real momentum convention consumed by the rate. -/
theorem rate_input (G mk mp me mb : ℝ) (pk pp pe pb : Fin 4 → ℝ)
    (ek : ιk → Fin 4 → ℂ) (ep : ιp → Fin 4 → ℂ)
    (ee : ιe → Fin 4 → ℂ) (eb : ιb → Fin 4 → ℂ)
    (hk0 : 0 < pk 0) (hp0 : 0 < pp 0) (he0 : 0 < pe 0) (hb0 : 0 < pb 0)
    (hk : msq pk = mk ^ 2) (hp : msq pp = mp ^ 2)
    (he : msq pe = me ^ 2) (hb : msq pb = mb ^ 2)
    (bk : Basis pk mk ek) (bp : Basis pp mp ep)
    (be : Basis pe me ee) (bb : Basis pb (-mb) eb) :
    (∑ x, Complex.normSq (amp G (norm pk ek) (norm pp ep)
      (norm pe ee) (norm pb eb) x)) / 2 =
      64 * G ^ 2 * MuonRate.mdot pp pb * MuonRate.mdot pe pk := by
  have h := spin_averaged G mk mp me mb pk pp pe pb ek ep ee eb
    hk0 hp0 he0 hb0 hk hp he hb bk bp be bb
  have hdot (a b : Fin 4 → ℝ) :
      mdot (cp a) (cp b) = (MuonRate.mdot a b : ℂ) := MuonAmplitude.mdot_cast a b
  rw [hdot, hdot] at h
  exact_mod_cast h

end PMElementaryParticles.MassiveExternalAmplitude
