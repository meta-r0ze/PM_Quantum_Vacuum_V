# PMAtoms — overview of checked results

The map of what the atomic/composite extension proves. Open work is in
[`REVIEW-AND-NEXT.md`](REVIEW-AND-NEXT.md); build instructions are in
[`README.md`](README.md). Sources are under `PMAtoms/`, imported by
`PMAtoms.lean`.

## Hierarchy

```
elementary protocols (PMElementaryParticles)
        │  three colour-axis protocols
        ▼
     Nucleon            (uud / udd, Q = +1 / 0, B = 1)
        │  Z protons + N neutrons
        ▼
     Nucleus            ((Z,N), decay channels, persistence)
        │  electrons = Z for a neutral atom
        ▼
      Atom / Shells     (2n² capacities, hydrogen readouts)
        │  hazards / channels
        ▼
     MeanLife           (τ = 1/λ from the persistence survival)
```

## Modules

| Module | Checked result | Retained inputs |
| --- | --- | --- |
| `Nucleon` | three colour-axis protocols (`slotChannel`); `ChargeProtocols.Q` on the actual channel equals the quark charge (`Q_slotChannel`, `charge_eq_channels`); three colour axes give `B=1` (`baryon_from_three_colours`); proton `uud` `Q=+1`, neutron `udd` `Q=0`, spin `2`, isospin gap `1` | spin-1/2, one protocol per colour axis |
| `Nucleus` | `Q=Z`, `B=Z+N` as sums of nucleon values (`charge_eq_nucleons`, `baryon_eq_nucleons`); `β⁻`, `β⁺`, capture, `α`, fission conserve `Q`/`B` with lepton number on the lepton side; conservation permits a channel from every `(Z,N) ≠ (0,0)` (`conservation_permits_all`); `Persists` is local minimality of a supplied cost; lower-cost daughters vanish by `PersistenceMechanics.Selection` | binding/cost order, allowed routes and rates |
| `NuclearGraph` | `NucleonLabel`, `LinkType` (`pp/pn/nn`), `completeEdgeCount`; `h3_counts` (0,2,1), `he3_counts` (1,2,0), `he4_counts` (1,4,1); `tetrahedron`/degree cap 4; `bindingComplete` decomposition | link weights, tetrahedron closure, packing |
| `NuclearFolding` | `Folding`, `coulombEnergy`, `coulombEnergy_scale`; `softenedKernel a r = 1/√(r²+a²)` with `softenedKernel_scale`, `softenedKernel_le_inv`; `e8ChargeCoupling = πD/(2σ)`; `sphereCoulomb` | actual folded positions | `Folding (A)` positions in `Fin 3`; `dist`; `coulombEnergy`; `dist_scale`; `coulombEnergy_scale : E(λF)=E(F)/λ`; `coulombEnergy_folded` at radius `A^{1/3}` | absolute charge coupling |
| `NuclearCharge` | `qH3/qHe3/qHe4`; `chargeEnergy3_H3 = 3/4`, `chargeEnergy3_He3 = 11/4`, `chargeEnergy4_He4 = 16/5`; `mirror_charge_difference = 2` | absolute coupling scale |
| `NuclearLine` | `lineCounts` gives H-3 `(0,2,1)`, He-3 `(1,2,0)`, He-4 `(1,4,1)`, C-12 `(3,12,3)`, O-16 `(4,16,4)`; `lineBinding_*` decompositions | Coulomb valley, boundary term |
| `TwoLedger` | `nuclearMass`/`nuclearMassCapped`; `mirror_h3_he3` and `mirror_h3_he3_capped` prove the mirror is the free `n−p−e` gap |
| `TwoLedger` | two-ledger mass `nuclearMass`; link asymmetry `±c/2` cancels the charge term; `mirror_h3_he3` proves the mirror is exactly the free `n−p−e` gap |
| `LatticeGreen3D` | `greenCube`/`cubeLap` on the `2×2×2` Dirichlet cube; `cubeLap_green`; diagonal `58/315`, nearest `11/315` |
| `LatticeGreen` | `pathGreen N i j = min(i,j)(N+1−max)/(N+1)`; `pathGreen_diag` self-energy; `pathGreen_symm`; exact agreement with `green3`/`green4` | 3D folded lattice |
| `NuclearTopology` | `closed_min_edges` (handshake: min degree 2 ⇒ `A ≤ edges`), `triangle_degree`, `triangle_edges`, `triangle_is_minimal_closed`; `tree_edges` for open lines |
| `AxisSplit` | `axisB` split: reference axis unique (`reference_axis_card = 1`), three colour axes (`colour_axis_card = 3`), `axis_split`, `three_plus_one_axes` |
| `LinkWeights` | `mapWeight = πD`, `boundaryWeight = σ/2`; `ppWeight`, `pnWeight`, `nnWeight`; `base_eq`, `neutron_boundary` tie them to `CompositeMasses` |
| `Invariants` | `Δ,ν,σ,χ,D`; `colour_axes`, `reference_axes`, `three_plus_one`, `homo_pair`, `radius_exponent`, `sphere_factor`, `charge_coupling` |
| `NuclearCoordination` | 4 channels = 3 `pn` + 1 homo; `pnCapacity z = (σ−χ)z`, `homoCapacity z = z/χ`; `one_proton_max_neutrons = 3`, `two_proton_max_neutrons = 6`, H-3/He-3/He-4 within capacity |
| `NuclearBinding` | `he4_pairwise_shortfall` (pairwise He-4 predicts 0.017392 u; measured 0.030377), `he4_closure_gap = 0.012985 u`, `mirror_link_difference = 0.000820 u` | link weights |
| `NuclearPacking` | `cliqueEdges`; face sharing `(3/3/9)`, vertex sharing `(7 vertices, 12 edges)`, edge sharing `(6 vertices, 11 edges)`; `packing_laws`; `shared_closure_once` | packing geometry |
| `NuclearSelection` | `GraphCandidate`, `exists_least_graph_cost`, `selectedGraph_min`, `GraphPersists`; `graphs4` enumerates degree-≤4 graphs on 4 vertices, `tetrahedron_mem_graphs4` | cost weights |
| `LinkModes` | `linkSpectrum = [4,1,1]`, row sum 4; `effectiveLinks A light = A + light/2`; `residual_eq_light` identifies the residual with half the light-mode weight | colour/generation light-mode occupation |
| `SystemTower` | `Level` (particle/nucleon/nucleus/atom), `LevelBudget` (toll/margin/sharedLinks, positive cost magnitudes subtracted), `latticeSum`, `boundMass`; `gap_eq_level_budgets` identifies the periodic-table gap with the nucleus+atom budget | the numeric per-level budgets |
| `NuclearMass` | `latticeMass n = Z m_p + N m_n`; `PersistsMass` = no decay lowers it; beta lowers it (`latticeMass_betaMinus_lt`), so `N>0` fails mass-persistence (`not_persistsMass_of_neutron`); α and fission conserve lattice mass (`alpha_mass_eq`, `fission_mass_eq`) | full persistence needs the channel rate/selection |
| `Particle` | `Species` with certified masses and `Q/B/L`; `ParticleDecay` = conserved numbers + lighter products; **`proton_stable`** (baryon number forbids a lighter channel); allowed `neutron_beta`, `muon_decay`, `pionPlus_decay`, `tau_decay` | certified PM-5 mass enclosures; tree-level channels |
| `ElectronCloud` | `SpinOrbital`, `Cloud = Finset SpinOrbital` (Pauli), `orbitalEnergyEV = −R∞/n²`, `fillCloud` (lowest-n), `AtomSystem.massME` = nucleons + electrons + cloud binding/c² | screening/exchange, electron correlations |
| `Shells` | `orbitalCapacity l = 2(2l+1)`, `shellCapacity n = 2n²`, `shell_capacities : 2,8,18,32` | spin-1/2, angular-momentum degeneracy |
| `Hydrogen` | `rydbergEV_bounds : 13.6056930–13.6056931 eV`; `bohrRadius_bounds : 0.5291772–0.5291773 Å`; `hydrogenLevel_ratio`; `ground_is_lowest` | electron rest energy and `ħc` as unit inputs; certified `α` |
| `ProtocolCandidates` | finite set cohorts (`candidateCohorts`), weak-partner filter (`candidateCohortsWeak`), least-cost selection | set version (multiplicity lost) |
| `ListCohorts` | multiplicity-preserving list cohorts; `charge3`/`listCharge3`, odd fermion parity, weak partner; `muon_list_mem`, `electron_list_not`, `electron_neutrino_list_not` | nuclear candidate set and E8 rates |
| `TransitionSelection` | `TransitionFamily`, `familyCost`; every nonempty candidate set has a least-cost family (`exists_least_cost`); `selectedFamily_min` and `selectedRate_le`; `selected_is_persistence_optimum` | the candidate set of substrate families |
| `RateModel` | `channelCost = expectedCost c0 E`; `channelRate_eq : rate = β·c0·Σ prob`; `channelMeanLife = MeanLife (channelRate …)`; zero-probability channels have zero rate | the event family per channel, and the toll/hazard coefficients |
| `PersistenceRate` | `RateSystem`, `totalRate`, `Persists` = total hazard zero, `not_persists_of_pos`, `MeanLife = 1/totalRate`; least-hazard selection (`exists_least_totalRate`, `selectedSystem_min`) | E8 channel rates |
| `MeanLife` | `MeanLife lam = 1/lam`; `MeanLife_eq_integral` (integral of `exp(−lam T)`); `MeanLife_eq_survival_integral` (same with `ExponentialFilter.survival`); `persistenceRate = β·costRate`; `meanLife_from_persistence` | the three persistence premises of `HazardForm`; the cost rate and `β` |

## E8 provenance audit

| item | status |
| --- | --- |
| spin factor `2` | **derived** from PM-2 `PL.trace = 2` (`Shells.spinStates_eq_trace`); `Nucleon.spinStates` reuses it |
| orbital degeneracy `2l+1` | supplied angular-momentum representation, not derived from E8 |
| `m_e`, `ħc` | supplied unit inputs |
| isotope masses, standard mass numbers, Aufbau order | frozen comparison/display data |
| muon/tau/pion/kaon/quark mass formulas | E8 formulas, but not the six-pillar ledger |
| link-mode occupation | open derivation |

## Mass-formula pillar audit

| particle | formula terms | TOL/MAR counted? | all six pillars? |
| --- | --- | --- | --- |
| proton | `Δ², πD, 1/D, α(D+1/D), Z_TOL, Z_MAR` | yes | **yes** |
| neutron | same + `σ/2` | yes | **yes** |
| muon | `Δσ, χ, π, α` | no | no |
| tau | `Δ²χ, Δσ, χ, D` | no | no |
| π⁰, π⁺ | `α⁻¹, σχ, 1/(ν−χ), …` | no (uses α⁻¹ sum) | no |
| K⁰, K⁺ | `(σ+χ)α⁻¹, σ, Dπ, …` | no | no |
| quarks | `η` and integer counts | no | no |
| electron | supplied `m_e` | no | no |

So the elementary-particle audit is uneven: **only the proton and neutron use the
full six-pillar mass ledger including TOL/MAR**. The leptons, mesons and quarks
use separate E8 formulas (`α⁻¹`, `η`, integer counts) and match experiment, but
they are not the same six-pillar accounting. Re-deriving them in the proton/
neutron ledger is the open unification task.

## What is derived vs input

- Derived: nucleon charge/baryon from substrate channels; shell combinatorics;
  hydrogen readouts from `α`; nuclear conservation and selection structure;
  proton stability; allowed tree-level particle decays.
- Input: spin-1/2, one protocol per colour axis, the `ħc`/`m_e` unit conversions,
  and — crucially — the **nuclear binding/cost order and channel rates**.
- Not yet derived: which `(Z,N)` are stable (the valley), nuclear lifetimes,
  shell filling order, and numeric particle lifetimes (deferred).
