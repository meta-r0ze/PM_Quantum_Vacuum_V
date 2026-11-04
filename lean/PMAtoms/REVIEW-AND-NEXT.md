# PMAtoms — open work (todo)

Topology selection: `NuclearTopology.closed_min_edges` proves a closed system
(min degree 2) needs at least `A` links, and the triangle attains 3; `tree_edges`
gives `A−1` for an open line. So the ring/line topology is persistence-selected,
not assumed.

The 3+1 split is now derived from `BaryonNumber.axisB`: one reference axis and
three colour axes (`AxisSplit`). The link weights are tied to `CompositeMasses`:
`base_eq` shows `−πD`, `neutron_boundary` shows `+σ/2` (`LinkWeights`). The
remaining assumption is the line/ring topology, not the numbers.

The numeric factors are now expressed through `Δ,ν,σ,χ,D` with equality proofs:
`3 = σ−χ`, `1 = D−(σ−χ)`, `2 = χ`, `3/5 = (σ−χ)/σ`, `πD/(2σ) = πD/10`.
`lineCountsE8`, `pnCapacityE8`, `homoCapacityE8`, `e8ChargeCoupling`, and
`sphereCoulomb` use those invariants. The line/ring arrangement and persistence
selection remain model choices.

The line/ring arrangement model is a 4-channel model: 3 hetero + 1 homo,
line/ring topology, alpha diagonals, link masses `πD ± σ/2`, and the open
Coulomb/valley term.

Checked results are in [`OVERVIEW.md`](OVERVIEW.md); build instructions are in
[`README.md`](README.md). This file is only what remains.

## 1. The E8 rate/binding model (the main gap)

`MeanLife` shows how a hazard rate becomes a lifetime, and
`PersistenceMechanics.HazardForm` derives the exponential survival from persistence with a
common `β`. `RateModel` now reads the per-channel cost from `PMSubstrate.NetCost`
(toll × expected transitions) and proves `rate = β · costRate` on the actual
event family.

`TransitionSelection` closes the “which family?” question: a channel fixes the
payload, and persistence selects a **least-cost transition family** from the
candidates. So the family is not an outside choice; it is a persistence optimum.

`ProtocolCandidates` generates the finite cohorts, and `candidateCohortsWeak`
adds the PM-2 weak-doublet partner (`electron↔neutrino`, `up↔down`). This removes
the unphysical singleton `{e}` (`electron_singleton_not_weak`) while keeping the
observed muon cohort (`muon_cohort_weak`).

`ListCohorts` now keeps multiplicity (`e ν ν̄` is length 3) and applies the
ledger constraints: charge in thirds, odd fermion parity, and the weak partner.
`muon_list_mem` holds; `electron_list_not` and `electron_neutrino_list_not`
remove `e` and `e ν`.

Still missing:

- the **candidate set** for nuclear channels with the same rule applied;
- the **E8 rate per selected channel**;
- the **binding/cost order for nuclei** (which `(Z,N)` are local minima);
- hence a concrete nuclear lifetime (helium, tritium, …), and the stability valley.

Next: add the weak-vertex constraint to `ProtocolCandidates` (import the PM-2
`WeakVertex`/`ChargedCurrent` data), then `selectedFamily` +
`RateModel.channelMeanLife` give `τ`. Without that, particle lifetimes stay
tree-level and `Nucleus.Persists` stays relative to the candidate set.

## 1b. System weight (periodic-table column)

`e8p --periodic-table` now shows the **E8 lattice weight**
`Z m_p + N m_n + Z m_e` from the certified masses, the standard experimental
atomic weight, and the mass number used to pick `N`. In this framework there is
no separate SM binding energy to subtract: "binding" is the **persistence** of the
combined lattice system (`Stable`/`Persists`), and the E8 mass is the lattice sum.
`SystemTower` makes the hierarchy explicit. The periodic table now uses a
**shell-resolved link-layer counting**: each shell with `n≥2` nucleons
contributes `n` ring links (none for a singleton), each carrying map `πD` (from
`CAP/Δ`), protocol `1/D`, boundary `σ/2`, and toll/margin. This gives H exactly,
C-12 within ~0.002 u, O-16 within ~0.003 u, and residuals up to ~0.03 u for Ca.
The Li-7 residual improved from −0.017 to −0.008 u. The remaining systematic
residual is the colour/glue link-graph correction, not fitted; the numeric
per-level CAP/MAP counting remains the open E8 task.

`NuclearMass` now gives the first E8 persistence criterion: `PersistsMass` = no
allowed channel lowers the lattice mass. It shows the criterion is necessary but
not sufficient — `β⁻` lowers the mass, so every `N>0` nucleus fails it, while
`α` and fission conserve the mass. `PersistenceRate` now states that dynamical rule: a system persists iff its
total hazard is zero; otherwise its mean life is `1/λ`, and selection picks the
least-hazard system. Full nuclear persistence therefore needs the actual E8
channel rates, not just mass minimality. The `m_E8` vs `m_exp`
gap is the mass-defect comparison for that dynamical persistence.

## 1c. Electron cloud

`ElectronCloud` now has a real state: a set of occupied spin-orbitals, Pauli by
construction, filled by the lowest hydrogenic `−R∞/n²` (E8 α + supplied `m_e`).
`AtomSystem` combines nucleus + cloud. The cloud binding is eV-scale, so it does
not change the 6-decimal nuclear mass table; the MeV residual is the nuclear
mass excess. Missing: electron–electron screening/exchange, shell energy, and
coupling to nuclear decay beyond electron count.

## 2. Numeric lifetimes — deferred

PM/E8 specifies **which** decay channels exist and when a system persists; it
does not supply a clock or a per-channel time scale. The conditional tau result
remains in `PMElementaryParticles.TauLifetime` but is not reported by `e8p` because it uses the
measured muon lifetime and `B(τ→eνν)` as anchors. Numeric lifetimes are future
work and require an E8 clock calibration plus per-channel transition counts. The
structural pieces (`MeanLife`, `PersistenceRate`) stay; no SM width formula is
used.

## 3. Stability valley and the periodic table

- `conservation_permits_all` shows conservation alone allows a `β` channel from
  every nonempty nuclide.
- A real periodic table needs the E8 binding ledger: nuclear masses, magic
  numbers/shell closures, and the neutron-rich boundary.
- `e8p --periodic-table` now prints `Z`, symbol, configuration, K/L/M/N,
  mass number and a **leading E8 weight** `Z m_p + N m_n + Z m_e` from the
  certified masses (capacities proved; Aufbau order and `N=Z` are supplied
  placeholders). The nuclear binding/link term is omitted; that term is the same
  E8 link ledger needed for persistence and decay, and it will also select `N`.

## 4. Shell filling order

`Shells` proves capacities but not the Madelung/Aufbau order. That order is a
model input; if added, prove the resulting noble-gas closures.

## 5. Unified system type

`Nucleon`, `Nuclide`, `Atom` and `Particle.Species` are separate ledgers. A
single `System` record with mass, charge, `B`, `L`, channels and `MeanLife` would
let `e8p` present one table and one decay graph.
