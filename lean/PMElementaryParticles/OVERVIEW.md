# PMElementaryParticles — overview of checked results

The single map of what Paper V proves and what later work can reuse. Open work is
in [`REVIEW-AND-NEXT.md`](REVIEW-AND-NEXT.md); build instructions are in
[`README.md`](README.md). Sources are under `PMElementaryParticles/`, imported by `PMElementaryParticles.lean`.
Theorem names are entry points, not exhaustive lists; the Lean source is ground
truth. Paper V builds on Papers I–IV and imports nothing from Paper VI.

## Scope

Paper V models **elementary-particle protocols and their decay** on the E8
substrate. It supplies: the V−A contact amplitude and its `W`-exchange origin, the
muon and massive-daughter decay widths, the pair/phase-space tensor machinery, the
decay-law relation to Paper I survival, and the particle/mass/charge protocol
checks against data (recorded as tensions, not fits). It does **not** select the
physical interaction, the phase-space normalization, the absolute coupling, or the
particle ledger; those remain model inputs.

## Amplitude, rate and width

| Modules | Checked result | Retained inputs |
| --- | --- | --- |
| `SpinorRateBridge` | Paper II's actual bilinear amplitude in Paper V's real-momentum convention: initial-spin-averaged square `64 G²(p·k̄)(p_e·k)` | V−A vertex, on-shell states, complete orthonormal kernel bases |
| `MuonAmplitude`, `MassiveMuon` | V−A trace algebra; the muon's mass cancels between chiral vertices (`chiral_sandwich`, `massive_trace`, `massive_amplitude`) | — |
| `MassiveExternalAmplitude` | Same `64 G²(p·k̄)(p_e·k)` for **arbitrary real masses** on all four legs (`spin_averaged`, `rate_input`) | Contact vertex, signed antiparticle convention |
| `WExchangeRate` | Contact amplitude as the `q→0` limit of tree `W` exchange; `G=√2g²/(8m_W²)`, `G=1/(√2v²)` (`exchange_rate_input`, `exchange_rate_fermi`, `bases_exist`) | That this exchange is the substrate interaction |
| `WeakMatching` | Mediator matching `M_W²=g²v²/4`, `G=1/(√2v²)`, normalized spectrum | Physical coupling/mediator |
| `MuonRate` | `192π³` derived: `pair_kinematics`, `tensor_coeffs`, `two_body`, `electron_measure`, `rate_density`, `muon_rate = G_F²m⁵/(192π³)`, `spectrum_form` | `Φ₂=1/(8π)` and the electron measure/flux (see Review A1–A2) |
| `MassiveDaughterSpectrum` | Massive charged daughter, massless neutrino pair: `threshold`, `kinematics`, `radial_measure`, `pair_density`, `massless`, `rate_positive`, `width_scaling` | Contact vertex, transported pair average |
| `MassiveWidth` | Closed massive-daughter width `G²m⁵/(192π³)·[1−8r+8r³−r⁴−12r² log r]`; `closed_width`, `phase_zero/one/continuous`, `phase_positive`, `threshold_width` | Tree contact spectrum, normalizations |
| `InclusiveMixing` | Unresolved orthogonal channels: `amplitude_weight`, `equal_kinematics` (sum = 1 for any unitary mixing), `pmns_muon_width` (uses Paper IV PMNS), `kinematic_bounds` | Orthogonal final states, common kinematics |

## Pair tensor and continuum angular integral

| Modules | Checked result | Retained inputs |
| --- | --- | --- |
| `PairIsotropy` | Rest-frame pair moments from sign flips / axis swaps / unit length: vanishing first and off-diagonal moments, diagonal `Φ/3`; `rest_covariant`, `normalized_rest` | Volume `1/(8π)` |
| `PairTransport` | Concrete `axisAverage`; Lorentz transport `transported_tensor`, `frame_independent`; `boost_lorentz`, `boost_to`, `timelike_pair`; `muon_density`, `axis_muon_density` | `Φ=1/(8π)`, electron measure, flux |
| `ContinuumPair` | Iterated Lebesgue angular integral with reduced density `1/(32π²)`: `volume=1/(8π)`, `first_moment`, `second_moment`, linearity on continuous test functions, `pair_massless`, `pair_contraction`, `massive_density` | Angular parametrization/density specified, not substrate-derived |

## Decay law, survival and routing

| Modules | Checked result | Retained inputs |
| --- | --- | --- |
| `Survival` | `survive=exp(−Γt)`, positivity, bounds, time constant, half-life | Exponential law |
| `DecayLaw` | Constant per-tick cost from Paper I survival (`ticks_exact`, `ticks_are_survive`), `hazard_pos_iff`, `compounded_limit` (finite→continuum) | Per-tick cost, `Γ=width/ħ`, tick, time homogeneity |
| `Widths` | `lifetime=ħ/Γ`, rescaling, reference-width positivity | Width input |
| `Routing` | `Model` with latency descent and label preservation (recursive routing) | The routing model |

## Scaling bookkeeping and substrate bridge

| Modules | Checked result | Retained inputs |
| --- | --- | --- |
| `MassScaling` | Dimensional exponents `phaseSpaceExponent`, `kinematicDimension`; `three_body_dimensions`; spectrum polynomial | Stipulated contact interaction |
| `ScalingObligations` | Each of the three `M⁵` scaling relations from a derived homogeneity of an actual formula (`momentum_linear`, `dispersion`, …) | The formulas |
| `SubstrateBridge` | `conditional_exponent`: the three scaling relations force the fifth power for `D=4`; E8-internal independence witness; distinct positive cubic/quintic laws | The three relations are proof *inputs* |

## Particles, masses and charges (recorded as tensions)

| Modules | Checked result |
| --- | --- |
| `ChargeProtocols` | Charges from Paper III packets; `thirds`; `integer_iff_colourless` |
| `CompositeMasses` | Proton, neutron, π⁰, K⁰, K⁺ formulas vs CODATA 2022 / PDG |
| `LeptonMasses` | `m_μ`, `m_τ`, `m_π⁺`; muon/tau recorded as ≈2.4σ / ≈2.1σ *tensions*, not agreements |
| `QuarkMasses` | Six quark formulas vs PDG 2024 |
| `NeutrinoContext` | Contextual neutrino masses excluded by oscillation data (`weak_minus_rest_excluded`, `no_moderate_gap_ratio`) |
| `TauLifetime` | `τ_τ = τ_μ (m_μ/m_τ)⁵ B_e` (`rate_ratio`, `tau_lifetime_tree`, `tau_lifetime_pull`) |

## External states

`ExternalStates.persistent_on_shell`: a persisting state (Paper IV
`persistent_single_frequency`) has one energy and one mass on its support, i.e. is
an on-shell mass eigenstate; `branches_do_not_persist` shows cross-branch
superpositions beat. Identifying an external particle with a persisting substrate
state remains a model input.

## Protocols and the 16-channel inventory

Paper V's §4 reads the 16-channel substrate as four base routing protocols, two
routing modes, three anchors and a single sterile vacancy. `ProtocolInventory`
proves the *stipulated* inventory is internally exact and agrees with Paper III:

- `channels_card`: 16 channels (`ν = 16`).
- `two_routing_modes`: 12 route through the colour bulk, 4 do not.
- `hand_split`: 8 active (left-handed boundary), 8 static.
- `anchor_split`: 12 manifold (D=4), 2 boundary (χ=2), 2 unanchored.
- `inventory_split`: up 6, down 6, electron 2, neutrino 1, sterile 1 (= 16).
- `baseProtocol_cases`: exactly four base protocols (`electron`, `up`, `down`, `neutrino`).
- `sterile_iff_no_base`: the sterile vacancy is the unique uncoloured, static,
  unanchored channel.
- `baseProtocol_charge`: the structural classification reproduces Paper III's
  generator charges (`up=2/3`, `down=-1/3`, `electron=-1`, `neutrino=0`).
- `colourBulk_false_iff_leptonic`: the no-colour channels are exactly the
  integer-charge (leptonic) ones (`ChargeProtocols.integer_iff_colourless`).

This checks the paper's enumeration/counting; it does **not** derive the physical
identification of those channels with particles (the paper calls the inventory
stipulated).

**Decay dynamics as routing change (`ProtocolDynamics`).** The paper models decay
as a change of routing protocol. `ProtocolDynamics` makes that concrete on the
inventory: resonant tier labels `Tier = Fin 4` (`Δ⁰…Δ³`), `baseCharge` per base protocol
(up 2/3, down −1/3, electron −1, neutrino 0), and `Decay p ds` = a nonempty exit
cohort with the parent's total charge and every daughter strictly lower-tier.
Proved: `decay_charge` (charge conservation), `decay_tier_lt`, `no_infinite_chain`
(finite descent, matching "at most `L(s₀)` steps"), `tier_zero_terminal`, and the
muon example `muon_decay` (`e+ν+ν̄`, charge `−1 = −1+0+0`). Partial-width addition
and branching normalization are in `Widths` (`branching_normalized`, `total`,
`identical_channels`); competing hazards are in `Survival.competing_hazards`.
**Routing caveats (`ProtocolCaveats`).** The paper states that routing alone does
not force stability or reachability; both are proved as countermodels:
`lower_latency_not_reachable` (a strictly lower-latency, same-label state that is
not a step) and `routing_not_terminal` (a non-terminal state). Together with
`Routing.minimum_terminal` and `Routing.no_infinite_descent` these pin down exactly
what the routing axioms buy. The **specific** allowed routes and rates remain model
inputs. **Tier ladder:** the
tiers are a point (`Δ⁰`), then 1D (`Δ¹`), 2D (`Δ²`), 3D (`Δ³`) — four geometric
tiers. Each protocol's mass ledger occupies a subset (leptons/down 0,1,2; up-type
0,2,3). The draft's earlier "three generations" wording was corrected in
`4_protocols.tex` to this "point then 1,2,3 dimensions" phrasing; no tier beyond
the volume (`Δ⁴`) exists.

## Substrate existence ledger

`SubstrateLedger.substrate_has_components` answers the prior question *does the E8
substrate even have the objects Paper V identifies?* Each conjunct is an existence
witness from the actual Paper II/III constructions: a nontrivial chirality
involution and a rank-two chiral projector (`chirality_exists`,
`chiral_sector_dim_two`); three colour axes and a traceless colour generator
(`colour_axes_exist`, `colour_generator_exists`); the charge spectrum
`{2/3,−1/3,0,−1}` (`charge_values_attained`); all four base protocols plus the
sterile vacancy (`protocols_attained`); and the four-tier ladder
(`tier_ladder_exists`). The physical particle identification remains a proposed
correspondence, not an assertion of this ledger.

## Interpretation boundaries (what is *not* selected)

Proved physics here is **conditional** on a tree-level V−A contact interaction,
massless or specified external states, supplied phase-space normalizations and a
supplied coupling. Not selected: that the contact vertex is the substrate's
physical interaction; the phase-space counting measure, angular density
`1/(32π²)`, electron measure and flux from substrate readout; the absolute
coupling / radiative corrections; the particle/mass ledger; fermionic statistics
and asymptotic-particle interpretation; the decay-law subsystem/environment. The
`M⁵` law is a consequence of the contact model, not a universal rule for every
persistent excitation.

## Verification

Run `./check.sh` for current counts. The sibling `PMAtoms` library is documented
separately in `PMAtoms/`; this file covers only the elementary-particle `PMElementaryParticles`
library.
No Paper VI imports; permitted axioms `propext`, `Classical.choice`, `Quot.sound`.
Run `./check.sh` for current numbers.
