# Nuclei arrangement: the 3 + 1 channel line/ring model

## Summary

The E8 link capacity is 4. It splits as

```
4 = 3 hetero (pn) + 1 homo (pp or nn)
```

A nucleus is an **alternating line/ring** of nucleons:

- hetero channels make the `p–n` chain;
- the homo channel makes the `p–p` / `n–n` line or ring;
- a `2p2n` block (alpha) closes into a tetrahedron by adding one `pp` and one
  `nn` diagonal;
- the line may be folded/wrapped in the 3D substrate, but its topology is the
  line/ring.

This explains the molecule-like picture: nuclei are not 3D clumps; they are
wrapped lines/rings.

## Channel rule

Each nucleon has:

- up to **3 `pn` links**,
- up to **1 `pp` or `nn` link**.

Consequences:

- one proton → at most **3 neutrons**;
- two protons → **1 `pp` link + at most 6 `pn` links**;
- He-4 → each nucleon uses **2 `pn` + 1 homo = 3 of 4 channels**.

## Counts

For `Z` protons and `N` neutrons, set

```
m = min(Z,N),  d = |N−Z|,
pn = 2m,
pp = (d if Z>N else 0) + floor(m/2),
nn = (d if N>Z else 0) + floor(m/2).
```

The `floor(m/2)` term is the alpha diagonal.

This gives:

| nucleus | pp | pn | nn |
|---|---|---|---|
| H-3 | 0 | 2 | 1 |
| He-3 | 1 | 2 | 0 |
| He-4 | 1 | 4 | 1 |
| C-12 | 3 | 12 | 3 |
| O-16 | 4 | 16 | 4 |

## What is an alpha diagonal?

Take four nucleons in the alternating ring `p–n–p–n`. That is a 4-cycle with four
`pn` edges. Closing it into a tetrahedron adds two more edges:

- one `p–p` edge,
- one `n–n` edge.

Those are the **alpha diagonals**. In E8 terms they are the **homo-channel
links**: the `pp`/`nn` links that use the one same-species channel of each
nucleon. They are not a new force; they are what turns the 4-cycle into the first
closed 3D cell (the tetrahedron). The count `floor(m/2)` in `lineCounts` is
exactly one `pp` and one `nn` diagonal per `2p2n` block.

So:

```
4-cycle:  4 pn  (hetero channels)
tetrahedron: 4 pn + 1 pp + 1 nn  (adds the two homo diagonals)
```

## What is the Coulomb/valley term?

In the line model, `pp` is cheaper than `pn` by `σ/2`:

```
pp = πD,   pn = πD − σ/2,   nn = πD + σ/2.
```

That makes the model prefer `Z ≈ A/2`, i.e. proton-rich heavy nuclei. Real heavy
nuclei are neutron-rich, so the `pp` link must carry an extra **charge cost**.

In E8 this is not the Standard-Model Coulomb potential inserted by hand. It is
the **charge protocol** `ChargeProtocols.Q` acting at the link level: a link
between two protons has two `+1` charges, so its charge load is higher than a
`pn` or `nn` link. The link weight should depend on the charge pair, not only on
the species. The collective `pp` cost then grows with `Z` and pushes the
minimum toward neutron-rich `(Z,N)` — the **valley of stability**.

The local mirror difference (`w_nn − w_pp ≈ 1.5 m_e`) and the collective valley
term are different pieces: the mirror is the low-`Z` endpoint difference; the
valley needs the charge load summed over the whole proton line/ring.

## Boundary/end term

An open line has two ends; a ring has none. The end cost is taken as one `pn`
link (`wpn = πD − σ/2`), subtracted from the binding. In Lean:
`lineBindingEnds`, `lineBindingEnds_ring`, `lineBindingEnds_open`. This improves
the line-table RMS from `0.0096` to `0.0087 u`.

## Homo saturation

The raw alpha-diagonal counts can exceed the homo capacity for very asymmetric
nuclei. The capped counts are

```
cappedLineCounts: pp = min(Z/2, raw_pp), nn = min(N/2, raw_nn)
```

with `capped_pp_le : pp ≤ Z/2`, `capped_nn_le : nn ≤ N/2`. For heavy
neutron-rich nuclei the raw `nn` exceeds `N/2`, so the alpha gas cannot continue;
the arrangement must switch to a saturated/neutron-line structure. That is the
same place the valley/Coulomb term is needed.

## E8 link weights

```
pp = πD
pn = πD − σ/2
nn = πD + σ/2
```

So a hetero link is cheaper than a homo link by `σ/2`.

## Numeric check

With these weights and **no fitted parameters**, the binding of Z=1..20 is
reproduced with RMS `≈0.008 u`. A free fit of the same counts lands on
`12.0 / 10.5 / 16.4 m_e`, close to `12.57 / 10.07 / 15.07`.

The model predicts `Z ≈ A/2` at fixed `A`, so it is proton-rich for heavy
nuclei. The missing valley term is a `pp` Coulomb/charge penalty (order
`10–15 m_e` per `pp` link), which pushes heavy nuclei neutron-rich.

## E8 grounding

- `PMDynamics.SubstrateLink.linkOverlap` row sum `4` → four channels.
- `D = 4` → the 3D simplex (tetrahedron) is the first closed cell.
- The 3+1 split is `colour axes (3) + reference/lepton axis (1)`.
- `ChargeProtocols.Q` / `BaryonNumber` give the `p/n` labels.
- `PMFramework.Selection` selects the least-cost arrangement.

## Lean objects

| file | content |
|---|---|
| `NuclearGraph.lean` | labels, link types, H-3/He-3/He-4 counts, tetrahedron, degree cap |
| `NuclearCoordination.lean` | 3+1 capacity, one/two-proton maxima, light-nucleus bounds |
| `NuclearBinding.lean` | He-4 pairwise shortfall, closure gap, mirror difference |
| `NuclearPacking.lean` | face/vertex/edge tetrahedron joins, shared closure |
| `NuclearSelection.lean` | least-cost graph, `GraphPersists`, small-graph enumeration |

## Open work

1. **Coulomb/charge link** to select the neutron-rich valley.
2. **Boundary/end term** for open lines (small, `~0.007 u`).
3. **Heavy saturation**: alpha diagonals exceed the homo capacity, so the
   arrangement must change for neutron-rich nuclei.
4. **3D folding**: how a line/ring embeds in the substrate without changing the
   topology.
5. **Promote to `e8p`** once the Coulomb/valley term is derived.

## Relation to standard physics

Alpha clustering, line/ring states, and the liquid-drop/shell descriptions are
known in nuclear physics. The specific E8 derivation here — 4 channels split
3 hetero + 1 homo, link masses `πD ± σ/2`, and the alternating line/ring with
alpha diagonals — is not the standard treatment. It is an E8 construction, not a
rephrasing of the shell model.
