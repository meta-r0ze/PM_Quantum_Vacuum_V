# PMElementaryParticles — Paper V decay library

Lean 4 proofs for *Persistence Mechanics V: Decay as a Conditional Routing Model*.
Paper V applies Paper II's shared dynamics and Paper IV's flavour input to an
**elementary-particle decay** example: elementary-particle protocols on the E8
substrate, and their conditional decay rates. It builds on Papers I–IV and
**rejects imports from Paper VI**.

## Main results

- **The `192π³` is not an input.** `MuonRate.muon_rate` derives the massless
  muon width `Γ = G_F² m⁵/(192π³)` from the V−A contact amplitude
  `64 G²(p·k̄)(p_e·k)`, the covariant neutrino-pair integral and the massless
  phase-space measure.
- **Massive daughter, closed form.** `MassiveWidth.closed_width` evaluates the
  massive-daughter contact width
  `Γ = G²m⁵/(192π³)·[1 − 8r + 8r³ − r⁴ − 12r² log r]`, `r=(μ/m)²`, with exact
  massless/threshold endpoints.
- **From W exchange.** `WExchangeRate` (via Paper II `WeakVertex`) derives the
  contact amplitude as the zero-momentum-transfer limit of `W` exchange.
- **Decay law.** `DecayLaw` ties Paper I's survival law to a constant per-tick
  cost, with a finite-tick exponential and its continuum limit.
- **Protocol inventory.** `ProtocolInventory` proves the paper's 16-channel
  routing model: four base protocols (up 6, down 6, electron 2, neutrino 1), one
  sterile vacancy, two routing modes, and charge classes matching Paper III.
- **Protocol dynamics.** `ProtocolDynamics` models decay as a routing change on
  the inventory: charge-conserving exit cohorts, strictly lower tiers, finite
  descent (`no_infinite_chain`), and the muon `e+ν+ν̄` example.
- **Substrate existence.** `SubstrateLedger.substrate_has_components` shows the E8
  substrate actually contains each object the paper identifies (chiral grading,
  colour structure, charge spectrum, four protocols, sterile vacancy, tier ladder).
- **Phase-space start.** `PhaseSpace.solidAngle_one` derives the `4π` angular
  weight from the direction integral (first step of the measure construction).
- **Routing caveats.** `ProtocolCaveats` proves the paper's caveats: lower latency
  need not be reachable, and routing alone doesn't force stability.
- **CP input** for the lepton sector comes from Paper IV (`Downstream`).

## Where to look

- **[OVERVIEW.md](OVERVIEW.md)** — the single map of what is proved and reusable
  (module-by-module) and what remains a physical input. **Start here to find a
  theorem you can use.**
- **[REVIEW-AND-NEXT.md](REVIEW-AND-NEXT.md)** — the remaining work, split into
  **mathematical proof gaps fillable in Lean** and **physical model inputs**.
- The paper source is under `../../paper/`.

## Sibling library

`PMAtoms` is a separate library in the same package: [README](../PMAtoms/README.md), [OVERVIEW](../PMAtoms/OVERVIEW.md), [REVIEW-AND-NEXT](../PMAtoms/REVIEW-AND-NEXT.md).

## Build and audit

Lean 4.34.1; dependencies pinned through sibling `PM-1-Arch/lean`,
`PM-3-Nested/lean` and `PM-4-Dynamics/lean`. Keep the papers as siblings, then:

```sh
source ~/.elan/env
./check.sh
```

`check.sh` builds the `PMElementaryParticles` library, strictly audits transitive axioms against
`propext`, `Classical.choice`, `Quot.sound`, and rejects Paper VI imports. A
successful audit certifies the statements under their hypotheses; it does **not**
select the physical interaction, measure normalization or coupling.

## Verification

Run `./check.sh`. No Paper VI imports; permitted axioms `propext`, `Classical.choice`, `Quot.sound`.
