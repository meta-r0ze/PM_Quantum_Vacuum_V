# PMAtoms — the system ladder above elementary particles

`PMAtoms` is a sibling Lake library to `PMElementaryParticles` in the same package. It is an
experimental extension: take the elementary protocols, combine them into
nucleons, then nuclei, then atoms, and ask what persists and what decays. The
point is to produce **testable lifetime/mass comparisons**, not to restate
textbook atomic physics.

Sibling library: `PMElementaryParticles` — [README](../PMElementaryParticles/README.md), [OVERVIEW](../PMElementaryParticles/OVERVIEW.md), [REVIEW-AND-NEXT](../PMElementaryParticles/REVIEW-AND-NEXT.md).

Build:

```
cd PM-5-Decay/lean
lake build PMAtoms
./check.sh          # builds PMElementaryParticles + PMAtoms, then runs the axiom audits
```

`e8p` consumes the library: its `Atoms` section reports `rydberg_ev`,
`bohr_radius` and `shell_capacity_n4`. Numeric lifetimes are not reported:
PM specifies channels/persistence, not a per-channel time scale.

## Modules

| Module | Role |
| --- | --- |
| `Nucleon` | assemble proton/neutron from three substrate colour-axis protocols; charge via `ChargeProtocols.Q`, baryon via `BaryonNumber` |
| `NuclearGraph` | typed nucleon graph (`p/n`, `pp/pn/nn`), complete-graph counts for H-3/He-3/He-4, tetrahedron (K4) closure, degree cap 4 | binding weights, packing, persistence selection |
| `NuclearFolding` | `Folding`, `coulombEnergy`, `coulombEnergy_scale`; `softenedKernel` (homothetic, ≤1/r); `e8ChargeCoupling = πD/(2σ)`, `sphereCoulomb` | actual folded positions | 3D folding `Folding` (positions in `Fin 3`), `dist`, `coulombEnergy`; `dist_scale`; `coulombEnergy_scale` (energy ∝ 1/λ); `coulombEnergy_folded` (radius A^{1/3}) | absolute charge coupling |
| `NuclearCharge` | Paper II path Green function + Paper III charge: `chargeEnergy3_H3 = 3/4`, `chargeEnergy3_He3 = 11/4`, `chargeEnergy4_He4 = 16/5`, `mirror_charge_difference = 2` | absolute E8 coupling scale |
| `NuclearLine` | `lineCounts` (alternating ring + alpha diagonals); H-3/He-3/He-4/C-12/O-16 counts; `lineBinding_*` | Coulomb valley, boundary term |
| `TwoLedger` | `nuclearMass` = free − link binding + charge; `nuclearMassCapped` (homo cap); `mirror_h3_he3`, `mirror_h3_he3_capped` |
| `TwoLedger` | `nuclearMass` = free − link binding + charge; `massLinkWeight` (`pp=πD+c/2`, `nn=πD−c/2`), `chargeTerm`; **`mirror_h3_he3`**: `M(H3)−M(He3)=m_n−m_p−m_e` |
| `LatticeGreen3D` | `greenCube` (rational 3D inverse), `cubeLap`, `greenCube_symm`, `cubeLap_green : L G = δ`; self-energy `58/315` |
| `LatticeGreen` | general path Green `pathGreen N i j`; `pathGreen_diag` (definite self-energy), `pathGreen_symm`; `green3_eq_pathGreen`, `green4_eq_pathGreen` | 3D lattice kernel |
| `NuclearTopology` | `closed_min_edges` (min degree 2 ⇒ ≥A edges), `triangle_is_minimal_closed`, `tree_edges` (open tree = A−1) |
| `AxisSplit` | `lepton_axis_unique`, `reference_axis_card = 1`, `colour_axis_card = 3`, `axis_split`, `three_plus_one_axes` — the 3+1 split from `BaryonNumber.axisB` |
| `LinkWeights` | `ppWeight = πD`, `pnWeight = πD − σ/2`, `nnWeight = πD + σ/2`; `base_eq`, `neutron_boundary` connect them to `CompositeMasses` |
| `Invariants` | `Δ,ν,σ,χ,D`; `colour_axes = 3`, `reference_axes = 1`, `three_plus_one`, `homo_pair = 2`, `sphere_factor = 3/5`, `charge_coupling = πD/(2σ)` |
| `NuclearCoordination` | 3 hetero + 1 homo channel split; `pnCapacity`, `homoCapacity`; H-3/He-3/He-4 within-capacity proofs; one proton ≤3 neutrons, two protons ≤6 |
| `NuclearBinding` | `he4_pairwise_shortfall`, `he4_closure_gap`, `mirror_link_difference` |
| `NuclearPacking` | `cliqueEdges`, `shared_vertices`/`shared_edges`/`union_edges`, `shared_closure_once` |
| `NuclearSelection` | `GraphCandidate`, `exists_least_graph_cost`, `selectedGraph_min`, `GraphPersists`, `graphs4` enumeration |
| `LinkModes` | `linkOverlap` spectrum `4,1,1`; `effectiveLinks A light = A + light/2`; `residual_eq_light` | the numeric light-mode occupation |
| `SystemTower` | explicit level budgets (`Level`, `LevelBudget`, `latticeSum`, `boundMass`); `gap_eq_level_budgets` says the periodic-table gap is exactly the nucleus+atom budget | numeric nucleus/atom budgets |
| `NuclearMass` | E8 lattice mass `Z m_p + N m_n`; `PersistsMass` = no channel lowers it; `latticeMass_betaMinus_lt`, `not_persistsMass_of_neutron`, `alpha_mass_eq`, `fission_mass_eq` | channel rates for full persistence |
| `Nucleus` | `(Z,N)` ledger; `β⁻`, `β⁺`, capture, `α`, fission; conservation; persistence as local minimality of a supplied cost |
| `Particle` | generic mass-ordered decay ledger; **`proton_stable`**; allowed `neutron_beta`, `muon_decay`, `pionPlus_decay`, `tau_decay` |
| `ElectronCloud` | spin-orbital cloud (`Finset SpinOrbital`), Pauli by construction; hydrogenic `ε_n = −R∞/n²`; `fillCloud` = lowest-`n` variational filling; `AtomSystem` = nucleus + cloud | electron–electron screening/exchange |
| `Shells` | `orbitalCapacity l = 2(2l+1)`, `shellCapacity n = 2n²`, first shells `2,8,18,32` |
| `Hydrogen` | Rydberg energy and Bohr radius from the certified `α`; `E_n = E_1/n²`; ground state lowest |
| `PersistenceRate` | dynamical persistence: `Persists` = total hazard zero, else `MeanLife = 1/λ`; least-hazard selection (`exists_least_totalRate`, `selectedSystem_min`) | the E8 channel rates |
| `MeanLife` | `τ = 1/λ` as the integral of the persistence survival `exp(−λT)`; multiple channels add hazards; `λ = β·(cost rate)` from `PersistenceMechanics.HazardForm` |
| `ProtocolCandidates` | finite set cohorts (`candidateCohorts`); weak-partner filter (`candidateCohortsWeak`) | set version, for reference |
| `ListCohorts` | multiplicity-preserving list cohorts: `e ν ν̄` is length 3; charge in thirds, odd fermion parity, weak partner; `muon_list_mem`, `electron_list_not`, `electron_neutrino_list_not` | nuclear candidate set with the same rule |
| `TransitionSelection` | a channel fixes the payload; persistence selects a least-cost transition family (`exists_least_cost`, `selectedFamily_min`, `selectedRate_le`) | the candidate set of substrate families |
| `RateModel` | reads the per-channel cost from `PMSubstrate.NetCost` (toll × expected transitions) and proves `rate = β·costRate` on the actual event family; lifetime follows from `MeanLife` |

## The rule

Lifetimes must come from **E8/persistence**, not from an inserted measured rate.
`MeanLife` therefore takes the hazard `λ = β · (operational cost rate)`: `β` is
the common coefficient derived in `PersistenceMechanics.HazardForm`, and the cost rate is
the substrate/persistence ledger's quantity. A concrete nuclear rate is still an
open E8 derivation; the library fixes the `rate → lifetime` step and proves the
structural decays in the meantime.

Open work is in [`REVIEW-AND-NEXT.md`](REVIEW-AND-NEXT.md); proved results are in
[`OVERVIEW.md`](OVERVIEW.md).
