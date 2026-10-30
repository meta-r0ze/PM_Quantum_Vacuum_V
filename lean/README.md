# PM-5-Decay: routing and decay formalization

Lean 4.34.1, with mathlib pinned through the sibling PM-1-Arch/lean package.
Keep the paper directories as siblings. With elan available, run `./check.sh`.
The initial dependency setup may need the mathlib cache; this Mac reuses the
existing cache and needs no additional installation. `.lake/` is ignored.

## Mathematical scope

| Module | Checked results |
| --- | --- |
| `PMDecay/Routing.lean` | Conserved labels along transitions, terminal latency minima, finite natural-valued latency descent, exclusion of infinite descent; a positive cost sequence without a positive uniform gap. |
| `PMDecay/Survival.lean` | Constant-hazard survival bounds, memoryless identity, addition of competing hazards, zero-rate survival, the exponential time constant and half-time relation; deterministic updates can remain stationary. |
| `PMDecay/Widths.lean` | Positive lifetimes, reciprocal width scaling, branching normalization and positivity, equal-channel multiplicity, reference-width positivity, phase suppression lengthening lifetimes, exact neutron factor 215/213 and its conditional lifetime relation. |
| `PMDecay/SubstrateBridge.lean` | Conditional scaling bridge to the earlier baseline; positive E8-invariant candidate widths and an exact cubic/quintic independence witness. |
| `PMDecay/MassScaling.lean` | Kinematic dimension versus phase-space mass dimension, canonical fermion and four-fermion coupling dimensions, tree-level mediator matching algebra, the fifth-power exponent, mass rescaling and unit covariance, and the combined scaling factors. |

## Internal M^5 derivation program

`SubstrateBridge.lean` is the primary dependency check. It derives the fifth
power from three explicitly stated kinetic, four-field vertex and rate-scaling
relations, using the earlier four-dimensional baseline. Those scaling relations
have not been derived from E8 in this project. An E8-internal witness shows that
positive norm-invariant cubic and quintic laws can have the same root calibration;
symmetry and normalization alone therefore do not select the exponent.

`ScalingObligations.lean` now gives each relation a derived source: the kinetic operator of Paper
II's Hamiltonian is first order (`momentum_linear`, `dispersion`), `G_F = 1/(√2 v²)` has degree −2
(`fermi_scaling`), and the derived width has degree 5 with dimension one (`rate_scaling`,
`rate_dimension_one`); `obligations_met` checks `(3/2, −2, 5)`. The action's dimension count stays
an input.

The remaining internal work is to derive the transition/current operator,
mediator limit, continuum normalization and counting/measure rule from the
substrate. No external weak-interaction theorem is used as a substitute.

### External comparison target

For comparison, the standard calculation assumes a four-dimensional, local,
derivative-free four-fermion
interaction, low energies relative to the mediator mass, effectively massless
daughters (or fixed mass ratios), and fixed dimensionless couplings.

1. A canonical Dirac kinetic term gives 2[ψ]+1=4, hence [ψ]=3/2.
2. Four fermions have operator dimension six; the coupling has dimension -2.
3. A massive W can supply this operator at low momentum. Given M_W=g v/2,
   the algebra gives g²/(8 M_W²)=1/(2 v²). The current and mediator approximation
   are physical inputs, not consequences of counting labels.
4. Each d³p/(2E) scales as M², so n-body invariant phase space scales as M^(2n-4).
   Three-body phase space therefore scales as M², although it has five kinematic
   degrees of freedom.
5. The squared amplitude scales as G_F² M⁴. Parent normalization contributes
   M^-1, giving G_F² M^5.

Lean checks the dimension bookkeeping, matching and rescaling algebra. It does
not construct the spinor amplitude or integrate Lorentz-invariant phase space;
192π³ is the known massless V-A coefficient; `MuonRate` derives it from the amplitude, covariance and the phase-space measure.
The spectrum's nonnegativity and primitive endpoint values are simple scalar
checks; no formal phase-space integration is claimed.

## Assumption boundary

Routing steps, labels, latency and their laws are supplied in `Routing.Model`.
A terminal state is stable within that model. Identifying it with an electron
or proton, or deriving a nonzero hazard for every allowed exit, needs dynamics.
A stationary exponential law is assumed rather than derived from deterministic
background traffic. The time constant 1/rate is checked algebraically; a
probability-distribution expectation integral is not included.

The reference-width formula requires independent masses, mixing, equal-channel
weights, phase-space factors and a calibration. Its successful algebra does
not certify the original mass ledger, all lifetime estimates, an exact four-gear
classification, or a quantum Yang-Mills mass gap. Strict positivity of individual
routing costs does not supply a uniform spectral gap.

## Primary physics references

* [PDG kinematics](https://pdg.lbl.gov/2024/reviews/rpp2024-rev-kinematics.pdf).
* [PDG muon decay](https://pdgaws.lbl.gov/2024/reviews/rpp2024-rev-muon-decay-params.pdf).
* [PDG electroweak matching](https://pdg.lbl.gov/2024/reviews/rpp2024-rev-standard-model.pdf).

`AuditStrict.lean` audits all project declarations by source module and namespace,
including private helpers. Only `propext`, `Classical.choice`, and `Quot.sound`
are allowed as transitive axioms. Physical assumptions are definitions or
hypotheses; there are no custom physical axioms or admitted proofs.

## Verification on 2026-10-27

`./check.sh` completed successfully: 3218 build jobs and a strict audit of
123 PMDecay declarations. Only the standard three allowed axioms occur
transitively. The manuscript was compiled separately and its rendered pages
were inspected.

## Weak matching from Papers II and III

`PMDecay/WeakMatching.lean` (requires `pm_nested`): Paper III's reference gives `M_W² = g²v²/4`
(`mediator_mass_derived`), so `mediator_matching`'s identity holds with the mass derived
(`matching_from_reference`), and `G_F = 1/(√2 v²)` follows with Paper II's contact limit and vertex
factor (`fermi_from_reference`). The V-A spectrum is normalized, `∫₀¹ 2x²(3−2x) dx = 1`
(`spectrum_normalized`), with mean energy fraction `7/10` (`spectrum_mean`). The `192π³` is derived in
`MuonRate` (below).

## Mass formulas against CODATA 2022 and PDG 2024

Units of `m_e`; `α⁻¹` is Paper I's derived value.

- `CompositeMasses`: proton `m_p/m_e` within `0.6σ` of CODATA (`proton_ratio`), neutron within
  `0.1σ` (`neutron_ratio`), `π⁰` within `0.9σ`, `K⁰` within `0.2σ`, `K⁺` within `0.1σ`, and
  `r_p = Dħ/(m_p c)` within `0.8σ` of CODATA 2022 `0.84075(64)` fm (`proton_radius`). The baryon
  ledger counts are pinned exactly by the data: the proton fits within `1σ` iff its Toll count is 5
  and Margin divisor 2 (`proton_counts`); the neutron iff 3 and 1 (`neutron_counts`).
- `LeptonMasses`: `π⁺` within `0.2σ`; splittings `m_K⁰ − m_K⁺ ∈ (3.93, 3.94)` MeV
  (`kaon_inversion`) and `m_π⁺ − m_π⁰ ∈ (4.5933, 4.5935)` MeV (`pion_splitting`). **Tensions:**
  the muon formula is `2.3–2.5σ` low (`muon_tension`, CODATA `206.7682827(46)`) and the tau
  `2.0–2.1σ` low (`tau_tension`, PDG `1776.93(9)` MeV).
- `QuarkMasses`: pulls of the six quark formulas (`pulls`); the charm and bottom formulas are the
  thresholds Paper III's `StrongRunning` uses (`threshold_match`).
- `ChargeProtocols` (from Paper III's packet): charges are `2/3, −1/3, 0, −1`; `3Q` is an integer;
  `Q` is an integer exactly on the colourless carriers (`integer_iff_colourless`), with the `3` the
  colour axes orthogonal to the reference.

These certify the stated formulas' values; they do not derive the ledgers' term assignments.
The paper's proton-radius comparison quotes `0.8414(19)` fm, the CODATA 2018 value; CODATA 2022
is `0.84075(64)` fm.

## Muon decay rate (`MuonRate`)

`Γ = G_F² m⁵/(192π³)` from three stated inputs: the spin-averaged V-A amplitude
`64 G_F²(p·k̄)(p_e·k)`, the covariant form of the neutrino-pair tensor, and the massless phase-space
measure. Proved: massless pair kinematics (`pair_kinematics`), tensor coefficients `A = Φ₂/12`,
`B = Φ₂/6` (`tensor_coeffs`), `Φ₂ = 1/(8π)` (`two_body`), the rest-frame contraction
(`rest_frame`), the electron measure, `dΓ/dE` (`rate_density`), the integral (`muon_rate`), and the
spectrum `2x²(3−2x)` in `x = 2E/m` (`spectrum_form`). The amplitude itself is derived in Paper II's `VATrace` (trace algebra of the actual Dirac matrices,
`muon_amplitude`) and matched to `MuonRate`'s conventions in `MuonAmplitude.amplitude_matches`; the
massless spin sums are reduced to the projector properties of `p̸γ⁰` (`spin_projector`,
`spin_solutions`, `spin_hermitian`, `spin_trace`).

## Tau lifetime (`TauLifetime`)

The `m⁵` law cancels `G_F` and `192π³` between leptons (`rate_ratio`), so
`τ_τ = τ_μ (m_μ/m_τ)⁵ B_e`. With the derived `m_μ`, `m_τ`, measured `τ_μ` and `B_e = 17.82 %`:
`291.15–291.17` fs at tree level (`tau_lifetime_tree`); with standard corrections as a factor
`c ∈ [0.9995, 0.9997]`, `+0.8` to `+1.0σ` from PDG `290.3 ± 0.5` fs (`tau_lifetime_pull`). The
tau-mass tension shifts this by only ~0.15 fs, so the lifetime does not decide it.

## Massive muon and contextual neutrinos

- `MassiveMuon`: `(1−γ⁵)γ^ν(1−γ⁵) = 0` (`chiral_sandwich`), so the muon factor `p̸ + m_μ` gives the
  same V−A trace as `p̸` (`massive_trace`, `massive_amplitude`).
- `NeutrinoContext`: with `M_rest` at the thermal floor and `M_weak = 6 M_rest`,
  `M_weak² − M_rest² ∈ (2.967, 2.969)·10⁻³ eV²` (`weak_minus_rest`), more than `17σ` above NuFIT
  6.0's `(2.534 ± 0.025)·10⁻³` (`weak_minus_rest_excluded`); `M_weak²` is more than `20σ` above
  (`weak_squared_excluded`). A fitting common factor would be `5.55–5.57`, not 6
  (`atmospheric_factor`).
