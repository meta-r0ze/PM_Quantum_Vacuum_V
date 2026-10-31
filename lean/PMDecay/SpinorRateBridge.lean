import PMAction.AmplitudeTrace
import PMDecay.MuonAmplitude

/-! Paper II's actual bilinear amplitude in Paper V's real momentum conventions.
The vertex, on-shell external states and complete orthonormal kernel bases are
hypotheses. No phase-space measure or physical identification is inferred. -/
noncomputable section
namespace PMDecay.SpinorRateBridge
open PMAction

variable {ιk ιp ιe ιb : Type*} [Fintype ιk] [Fintype ιp] [Fintype ιe] [Fintype ιb]
  [DecidableEq ιk] [DecidableEq ιp] [DecidableEq ιe] [DecidableEq ιb]

/-- The real squared-amplitude input used by `MuonRate`, now from actual spinors.
The initial muon spin average is the explicit factor 1/2. -/
theorem spin_averaged (G m mb : ℝ) (pk pp pe pb : Fin 4 → ℝ)
    (ek : ιk → Fin 4 → ℂ) (ep : ιp → Fin 4 → ℂ)
    (ee : ιe → Fin 4 → ℂ) (eb : ιb → Fin 4 → ℂ)
    (hk0 : 0 < pk 0) (hp0 : 0 < pp 0) (he0 : 0 < pe 0) (hb0 : 0 < pb 0)
    (hk : SpinorCompleteness.msq pk = 0) (hp : SpinorCompleteness.msq pp = m ^ 2)
    (he : SpinorCompleteness.msq pe = 0) (hb : SpinorCompleteness.msq pb = mb ^ 2)
    (bk : AmplitudeTrace.Basis pk 0 ek) (bp : AmplitudeTrace.Basis pp m ep)
    (be : AmplitudeTrace.Basis pe 0 ee) (bb : AmplitudeTrace.Basis pb (-mb) eb) :
    (∑ x, Complex.normSq (AmplitudeTrace.amp G
      (AmplitudeTrace.norm pk ek) (AmplitudeTrace.norm pp ep)
      (AmplitudeTrace.norm pe ee) (AmplitudeTrace.norm pb eb) x)) / 2 =
      64 * G ^ 2 * MuonRate.mdot pp pb * MuonRate.mdot pe pk := by
  have h := AmplitudeTrace.spin_averaged G m mb pk pp pe pb ek ep ee eb
    hk0 hp0 he0 hb0 hk hp he hb bk bp be bb
  have hdot (a b : Fin 4 → ℝ) :
      VATrace.mdot (SpinorCompleteness.cp a) (SpinorCompleteness.cp b) =
        (MuonRate.mdot a b : ℂ) := MuonAmplitude.mdot_cast a b
  rw [hdot, hdot] at h
  exact_mod_cast h

end PMDecay.SpinorRateBridge
