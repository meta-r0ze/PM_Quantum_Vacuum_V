import PMAction.WeakVertex
import PMDecay.MuonRate

/-!
# The rate's amplitude from W exchange

`SpinorRateBridge` takes the V−A contact vertex as given. Paper II's `WeakVertex` derives it as the
zero-momentum-transfer limit of W exchange with the charged-current vertex `(g/√2) γ^μ P_L`.

* `exchange_rate_input`: the spin-averaged squared W-exchange amplitude at `q = 0` is Paper V's
  input `64 G² (p·k̄)(pₑ·k)`, with `G = √2 g²/(8 m_W²)`, in `MuonRate`'s real momentum convention.
* `exchange_rate_fermi`: with `m_W² = g²v²/4`, `G = 1/(√2 v²)`.
* `bases_exist`: the orthonormal kernel bases that the amplitude theorem assumes exist for every
  momentum (`WeakVertex.basis_exists`).

Still inputs: on-shell external states and their identification with substrate carriers, and
the decay probability rule and phase-space measure.
-/

noncomputable section
namespace PMDecay.WExchangeRate
open PMAction

lemma mdot_cast (a b : Fin 4 → ℝ) :
    VATrace.mdot (SpinorCompleteness.cp a) (SpinorCompleteness.cp b) = (MuonRate.mdot a b : ℂ) := by
  simp [VATrace.mdot, SpinorCompleteness.cp, MuonRate.mdot]

variable {ιk ιp ιe ιb : Type*} [Fintype ιk] [Fintype ιp] [Fintype ιe] [Fintype ιb]
  [DecidableEq ιk] [DecidableEq ιp] [DecidableEq ιe] [DecidableEq ιb]

theorem exchange_rate_input (gw mW m mb : ℝ) (hm : mW ≠ 0) (pk pp pe pb : Fin 4 → ℝ)
    (ek : ιk → Fin 4 → ℂ) (ep : ιp → Fin 4 → ℂ) (ee : ιe → Fin 4 → ℂ) (eb : ιb → Fin 4 → ℂ)
    (hk0 : 0 < pk 0) (hp0 : 0 < pp 0) (he0 : 0 < pe 0) (hb0 : 0 < pb 0)
    (hk : SpinorCompleteness.msq pk = 0) (hp : SpinorCompleteness.msq pp = m ^ 2)
    (he : SpinorCompleteness.msq pe = 0) (hb : SpinorCompleteness.msq pb = mb ^ 2)
    (bk : AmplitudeTrace.Basis pk 0 ek) (bp : AmplitudeTrace.Basis pp m ep)
    (be : AmplitudeTrace.Basis pe 0 ee) (bb : AmplitudeTrace.Basis pb (-mb) eb) :
    (∑ x, Complex.normSq (WeakVertex.exchange gw mW 0
      (AmplitudeTrace.norm pk ek) (AmplitudeTrace.norm pp ep)
      (AmplitudeTrace.norm pe ee) (AmplitudeTrace.norm pb eb) x)) / 2 =
      64 * WeakVertex.fermiG gw mW ^ 2 * MuonRate.mdot pp pb * MuonRate.mdot pe pk := by
  have h := WeakVertex.exchange_spin_averaged gw mW m mb hm pk pp pe pb ek ep ee eb
    hk0 hp0 he0 hb0 hk hp he hb bk bp be bb
  rw [mdot_cast, mdot_cast] at h
  exact_mod_cast h

theorem exchange_rate_fermi (gw v mW : ℝ) (hg : gw ≠ 0) (hv : v ≠ 0)
    (hm : mW ^ 2 = gw ^ 2 * v ^ 2 / 4) : WeakVertex.fermiG gw mW = 1 / (Real.sqrt 2 * v ^ 2) :=
  WeakVertex.exchange_fermi gw v mW hg hv hm

theorem bases_exist (p : Fin 4 → ℝ) (m : ℝ) :
    ∃ (k : ℕ) (e : Fin k → Fin 4 → ℂ), AmplitudeTrace.Basis p m e :=
  WeakVertex.basis_exists p m

end PMDecay.WExchangeRate
