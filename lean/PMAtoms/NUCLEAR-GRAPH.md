# The nuclear graph system

## Why this file exists

The periodic-table mass residual is not a simple shell count. The data force a
**typed, coordination-capped graph**:

- vertices are nucleons, labelled `p` or `n`;
- edges are links, typed `pp`, `pn`, `nn`;
- a nucleon has at most **4** links (the substrate `linkOverlap` row sum / `D=4`);
- a closed 4-vertex subgraph (a **tetrahedron**) is a persistent subsystem and
  carries a **closure budget**;
- larger nuclei are packings of tetrahedra with shared faces;
- stability is the persistence selection: the least-cost graph for `(Z,N)`.

This is the candidate missing description behind the nuclear mass excess.

## E8 grounding

- `PMFlavor.SubstrateLink.linkOverlap` has row sum `4`, so the link capacity is 4.
- `D = 4` makes the 3D simplex (tetrahedron) the first closed cell.
- `Nucleon` is a colour singlet; `Nucleus` gives the `(Z,N)` ledger.
- `ChargeProtocols.Q` / `BaryonNumber` give the `p/n` labels and charges.
- `PersistenceMechanics.Selection` supplies the least-cost persistence choice.

## What the data says

Pairwise-only fits fail at He-4:

```
H-3 : 2 w_pn + w_nn          = 0.009106 u
He-3: w_pp + 2 w_pn          = 0.008286 u
He-4: w_pp + 4 w_pn + w_nn   = 0.030377 u   (pairwise gives 0.017392)
```

so He-4 needs `≈0.013 u` of 4-body closure. The mirror pair gives
`w_nn − w_pp ≈ 1.5 m_e`. A per-alpha closure is not additive: C-12 and O-16
would overbind. Hence the closure is context-dependent — a packing/geometry
effect.

## Lean objects (target)

```lean
inductive Species | proton | neutron
inductive LinkType | pp | pn | nn

structure NucleonGraph where
  A : Nat
  graph : SimpleGraph (Fin A)
  label : Fin A → Species

def degreeCap (G : NucleonGraph) : Prop := ∀ v, G.graph.degree v ≤ 4
def edgeType (label) (u v) : LinkType
def edgeCounts (G) : LinkType → Nat
def Tetrahedron (G) : Prop          -- 4 vertices, K4, degree 3
def binding (weights) (G) : ℝ        -- Σ edge weights + closure
def Persists (weights) (G) : Prop   -- local minimum under edge changes/decay
```

## Proofs to fill

1. **K3 / K4 counts** — done in `NuclearGraph.lean`.
   - H-3 label `(p,n,n)`: `pp=0, pn=2, nn=1`.
   - He-3 label `(p,p,n)`: `pp=1, pn=2, nn=0`.
   - He-4 label `(p,p,n,n)`: `pp=1, pn=4, nn=1`.
2. **Tetrahedron** — done: `tetrahedron_neighbors`, `tetrahedron_degreeCap`, `tetrahedron_closed`.
   - K4 has 4 vertices, 6 edges, every degree 3, so `degreeCap` holds.
   - `Tetrahedron` is closed: no vertex has an unused internal link slot beyond
     the 4-cap.
3. **Binding decomposition** — done: `he4_binding`, `h3_binding`, `he3_binding`, `he4_pairwise_shortfall`, `he4_closure_gap`.
   - `binding K4 = w_pp + 4 w_pn + w_nn + closure`.
   - Pairwise-only He-4 misses `closure`.
4. **Mirror** — done: `mirror_link_difference` (`w_nn − w_pp = 0.000820 u`).
   - `w_nn − w_pp` is the H-3/He-3 displacement.
5. **Persistence** — done: `exists_least_graph_cost`, `selectedGraph`, `GraphPersists`.
   - A finite family of labelled graphs has a least-cost member.
   - A closed tetrahedron is a local minimum under adding/removing an internal edge.
6. **Packing** — done: face-sharing `(3/3/9)`, vertex-sharing `(1 vertex, 12 edges)`,
   edge-sharing `(2 vertices, 11 edges)`, `packing_laws`, `shared_closure_once`;
   enumeration `graphs4` and `tetrahedron_mem_graphs4`.
   - Two tetrahedra sharing a face share 3 vertices/3 edges; the shared closure is
     counted once, not twice.
   - C-12 = 3 tetrahedra, O-16 = 4 tetrahedra, with shared-face reductions.

## What is still a model input

- the numerical weights `w_pp, w_pn, w_nn`;
- the closure budget of a tetrahedron;
- the packing geometry (which faces are shared);
- the selection rule among packings (least cost).

These must come from the E8 link/toll ledger, not from fitting.

## Build order

1. `NuclearGraph.lean`: types, counts, K3/K4, tetrahedron, degree cap.
2. `NuclearBinding.lean`: binding decomposition, mirror difference.
3. `NuclearPacking.lean`: tetrahedron packing, shared-face closure.
4. `NuclearSelection.lean`: persistence minimum over graphs/packings.
