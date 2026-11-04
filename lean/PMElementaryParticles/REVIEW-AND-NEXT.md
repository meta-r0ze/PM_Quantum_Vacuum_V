# PMElementaryParticles — open work (todo)

Checked mathematics and the module map are in [`OVERVIEW.md`](OVERVIEW.md). This
file is only what remains, split by what a Lean proof can close (**Part A**) and
what needs a physical model law or measured/selected input (**Part B**). Paper V's elementary-particle library builds clean; run `./check.sh` for current
counts. The sibling `PMAtoms` library has its own `REVIEW-AND-NEXT.md`.

## How to test the draft paper

The paper's checkable content decomposes into four layers: (1) the **stipulated
protocol inventory** (16 channels, four base protocols, sterile vacancy) — now
formalized in `ProtocolInventory`, with `SubstrateLedger.substrate_has_components`
showing the substrate actually contains each component (chirality, colour,
charge, protocols, sterile vacancy, tier ladder); (2) the
**routing dynamics** (allowed transitions, latency descent, terminal states) —
the generic `Routing` model, the concrete charge-conserving `Decay` relation
(`ProtocolDynamics`), and the paper's routing caveats (`ProtocolCaveats`:
lower latency need not be reachable; routing does not force stability) exist; the
*specific* allowed routes and rates remain inputs; (3) the **quantitative
rates** (`MuonRate`, `MassiveWidth`, `InclusiveMixing`, `TauLifetime`) — done,
modulo the measure gaps in Part A; (4) the **physical identifications**
(pillars→spin/colour/charge, neutrino duality, CPT, particle ledger, physical
interaction/measure) — model inputs, in Part B. So the remaining *protocol* work is
layer 2 plus tiers; the remaining *decay* work is Part A's measure construction.

## Part A — mathematical gaps fillable in Lean

These are analysis/probability tasks: the physics input is the standard
Lorentz-invariant measure, and the goal is to **construct** it rather than supply
its value. Each names the current placeholder to replace.

### A1. Two-body phase space from a delta function
`MuonRate.two_body` currently proves only the arithmetic
`4π/(2π)²·(1/4)·(1/2) = 1/(8π)`; it does **not** construct a measure. Target:
build the massless two-body integral
`Φ₂ = ∫ d³k/((2π)³ 2E_k) · d³k̄/((2π)³ 2E_k̄) · (2π)⁴ δ⁴(q − k − k̄)`
and **compute** `Φ₂ = 1/(8π)` from it, then re-derive `pair_coeffs`
(`A = 1/(96π)`, `B = 2A`). Note Mathlib's `integral_dirac` handles point masses,
not a surface delta, so this likely needs an energy-shell/fiber (coarea)
construction plus `MeasureTheory` change of variables. **Started:** `PhaseSpace.solidAngle_one` derives the `4π` angular weight from the
iterated direction integral over `(z,φ)`, `average_one` normalizes it, and
`electron_measure_radial` records the massless radial measure. Remaining: the
energy-shell **delta** reduction and the full two-body measure. This is the "not a
constructed delta-function measure" gap.

### A2. Radial energy-shell reduction of the electron measure
`MuonRate.electron_measure` is an algebraic identity. Target: derive
`4π E²/((2π)³ 2E) = E/(4π²)` from `∫_{ℝ³} d³p` in spherical coordinates (surface
measure of `S²` times `p² dp`, `p = √(E²−m²)`), for the massless case first, then
the massive one. **Status:** the angular area `4π` (`PhaseSpace.solidAngle_one`), the massless radial
identity (`PhaseSpace.electron_measure_radial`) and the massive radial Jacobian
(`MassiveDaughterSpectrum.radial_measure`) are proved. Only the global `∫_{ℝ³}`
spherical change of variables remains, and Mathlib has **no** spherical-coordinate
integral, so this item is blocked on that infrastructure rather than on our work.

### A3. Three-body phase-space factorization
The three-body measure is used but not factored. Target: factor it into
(pair invariant mass) × (pair angular measure) × (spectator energy), and derive the
`MassiveDaughterSpectrum` density `pair_density` as a *consequence* rather than an
input. This is the concrete mathematical content of former review item 2.
Depends on A1–A2.

### A4. Massive neutrino pair (extend the daughter spectrum)
`MassiveDaughterSpectrum`/`MassiveWidth` treat a massless neutrino pair. Target:
extend `pair_density`/`closed_width` to a massive neutrino pair (at least equal
masses or one massive leg), with positivity and endpoint limits, reusing the
transported pair tensor with `q² ≠ 0`. Closed form or a controlled integral.

### A5. Rotation invariance of the continuum angular average
`ContinuumPair` proves moments and linearity on *continuous* test functions but not
full rotation invariance for every integrable test function. Target: prove the
uniform-sphere average is invariant under rotations on `L¹` (change of variables /
Haar invariance of the sphere), so the pair tensor's covariance is a consequence of
the measure, not only of degree-≤2 moments.

Suggested order: **A1 → A2 → A3**, then **A5**, then **A4** (A4 reuses A1–A3).

## Part B — physical model inputs (not Lean-provable)

### B1. Physical interaction and final states
Connect the substrate update / reference / charged-current operators to the contact
vertex used in `AmplitudeTrace`, and state which carrier transitions give the
external one-particle states and decay channels. Paper II supplies conditional
operator bridges; the identification and normalization need a model law.

### B2. Select the measure and normalizations from the substrate
Independently of A1–A2 (which construct the *standard* measure), the **choice** of
counting measure, reduced angular density `1/(32π²)`, electron measure, parent flux
`1/(2m)` and overall normalization must be derived from the selected physical
readout — they are currently supplied.

### B3. Decay law from the chosen dynamics
Specify subsystem, environment/readout and the controlled approximation giving
constant hazard; relate the width to `Γ = width/ħ` and the physical tick. `DecayLaw`
proves the consequences of a supplied per-tick cost; persistence alone does not
force a nonzero hazard or an exact exponential.

### B4. Particle protocols, routing dynamics and mass ledger
The channel inventory/counting is checked (`ProtocolInventory`: 16 channels, four
base protocols, sterile vacancy, charges). Now proved in `ProtocolDynamics`: charge-conserving decay `Decay`, finite descent
(`no_infinite_chain`), tier-0 terminality, and the muon `e+ν+ν̄` example; tier labels are
`Tier = Fin 4`: a point (`Δ⁰`), then 1D (`Δ¹`), 2D (`Δ²`), 3D (`Δ³`). Each protocol's
mass ledger occupies a subset (leptons/down 0,1,2; up-type 0,2,3). The draft's
"three generations" prose was corrected to this "point then 1,2,3 dimensions"
phrasing in `4_protocols.tex`; no tier beyond the volume (`Δ⁴`) exists. What remains
is only the per-protocol tier subset, which is a ledger input. Still open: the **specific** allowed routes and their rates (model
inputs), which routing histories represent the particles, their resource costs,
and why the mass ledger is selected. Charge/
conservation/mass checks are constraints, not a selection. The muon/tau mass formulas are recorded as ≈2.4σ and
≈2.1σ tensions; the factor-six contextual neutrino prescription is excluded. Do not
promote a numerical fit or a symmetry-class count to a particle classification.

### B5. Absolute coupling and corrections
Radiative corrections, hadronic final states, bound-state matrix elements, and an
absolute coupling/lifetime prediction remain inputs. The tau lifetime uses the
measured muon lifetime and branching fraction; the neutron rescaling is a
conditional arithmetic identity.

## Scope of the fifth-power result
`MuonRate.muon_rate`'s `m⁵` is a consequence of the specified four-dimensional
contact interaction, state normalization and massless/fixed-ratio phase-space model
at fixed dimensionless couplings — not a universal rule for every persistent
excitation (`SubstrateBridge` contains distinct cubic and quintic laws). The
remaining work is to select the physical law, not to hide its hypotheses.

## Verification

Run `./check.sh`. No Paper VI imports; permitted axioms `propext`, `Classical.choice`, `Quot.sound`.
