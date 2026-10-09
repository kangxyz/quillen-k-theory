# Classification-diagonal comparison and row full-faithfulness review

Date: 2026-10-09. Lean 4.34.0 and the repository's pinned mathlib.

## Checked generic classification-diagonal theorem

`Quillen/Topology/Realization/Classification.lean` and
`ClassificationHomotopy.lean` prove, for an arbitrary category `D`, an actual
homotopy equivalence between the realization of its classification-grid
simplicial set and the realization of its ordinary nerve. The forward map is
exactly diagonal evaluation. The theorem has no equivalence, contraction,
rowwise-invariance, or homotopy assumption.

The source simplicial set has genuine functors from the square ordinal grid
`Fin(n+1) × Fin(n+1)` to `D`; only arrows in the first coordinate are required
to be isomorphisms. Both coordinates are reindexed by every simplex map.
`constant` sends an ordinary chain to a vertically constant diagram, and
`constant_evaluation` is the strict section identity.

Vertical transport between any two rows is defined through their common
initial row. Composition of the original diagram arrows proves its cocycle
law and identifies transport on an ordered pair with the original map.
`transport_precomp` proves its compatibility with every ordinal map,
including maps identifying two distinct indices. Thus the chosen initial
row does not introduce an unjustified naturality assumption.

The cylinder moves each object `F(s,i)` to `F(s,i)` or `F(i,i)`, according to
the interval simplex at `s`. Every morphism is conjugated by the corresponding
vertical isomorphisms. This constructs an actual functor and preserves the
vertical-isomorphism condition even without a monotonicity assumption on the
selection function. Its simplex naturality is proved, not inferred from
pointwise homotopies. At the two endpoints it is precisely the identity and
`evaluation ≫ constant`; the latter equality follows from the original grid
commutation law and cancellation of invertible vertical arrows.

The resulting `SSet.Homotopy` is realized through the previously proved
cylinder-realization theorem. `realizationHomotopyEquiv` uses diagonal
evaluation and the constant-diagram inclusion as its actual forward and
inverse maps. `realizationHomotopyEquiv_toFun` is `rfl`.

`constant_cylinder` proves the deformation fixes the entire image of the
constant-nerve inclusion. `realizationHomotopy_fixed_vertex` supplies the
corresponding actual fixed-point equation at every chosen vertex in that
image. Thus the zero vertex needed by Q/S comparison is retained; no
unpointed replacement map is introduced.

This discharges the generic classification-diagonal-to-nerve obligation
identified in `REVIEW_20261009_Q_S_STRATEGY.md`. It does not by itself establish
essential surjectivity of the exact-row comparison or the final Q/S theorem.

## Verification of the generic theorem

Both current sources were actually elaborated with `lake env lean -j1`,
serialized under `/tmp/quillen-lean-slot-1.lock`, and importable Lean outputs
were produced. Logs are `logs/classification-grid.log` and
`logs/classification-homotopy.log`. Only style/deprecation warnings remain.

`audits/ClassificationIndependentAudit.lean` selects every declaration by
its exact source-module origin, including private/generated declarations,
and recursively traverses axiom dependencies. It passed **81 declarations**:
47 from Classification and 34 from ClassificationHomotopy. Only `propext`,
`Classical.choice`, and `Quot.sound` are allowed. It also compiled independent
arbitrary-object/morphism-universe consumers for the simplicial homotopy,
realization equivalence, forward-map equality by `rfl`, and fixed-vertex
theorem. Log: `logs/classification-independent-axioms.log`.

The three-entry source/audit manifest is
`logs/classification-independent-sources.sha256`, SHA-256
`7e139f6706a18be7c5dee7a701a14ae2b4db60d5598d6204a9549e4a4a151210`.
The hashes still match after the audit, as recorded in
`logs/classification-independent-final-hash-check.log`. The project
source-token scan also passed:
`logs/classification-independent-source-token.log`.

## Independent semantic inspection of row full faithfulness

The Q/S author's nine-module scope was inspected separately:
RowGroupoid, RowSimplicial, RowFaithful, SpanLifting, InitialFlag,
InitialFlagIso, RecoverSubobjects, SparseRows, and RowFull. Frozen source
hashes are in `logs/q-s-full-faithful-semantic-review-sources.sha256`,
manifest SHA-256
`ac602e3b6564f5e1f7a0a2b4448508adfa3279bffd5c3f9a66b57c74f901c959`.

No semantic blocker was found:

- `Row` contains an actual interval functor and precisely the original
  S-construction conditions, expressed with a constant nerve coordinate.
  Its morphisms are actual natural isomorphisms of the quotient diagrams.
- `rowNatTrans_ext_top` uses monic inclusions into the top object to recover
  the initial-subobject components, then epic quotient maps to determine
  all other components. Faithfulness therefore does not discard kernel
  information or assume that the row functor is already faithful.
- `SpanLifting` transports endpoints by original isomorphisms and applies
  the actual Q equivalence relation to obtain the commuting apex
  isomorphism. Uniqueness follows from the monic right leg.
- `RecoverSubobjects` obtains the upper endpoint from that apex and the lower
  endpoint from the actual kernel of its deflation. Both are necessary:
  retaining only the apex would not reconstruct the initial flag.
- The left and right central endpoints cover the whole edgewise ordinal.
  `SparseRows` recovers every initial subobject. Monicity of its inclusion
  into the top object forces the recovered components to be compatible,
  rather than requiring arbitrary classical choices to be coherent.
- `InitialFlag` extends the resulting flag isomorphism to every quotient
  using actual cokernel universal properties. Naturality is proved by
  precomposition with epic quotient maps.
- `RowFull` explicitly transports the last central interval to the whole
  row, recovers the originally prescribed quotient components by epi
  cancellation, and proves the resulting row isomorphism maps to exactly
  the supplied Q-natural isomorphism. It uses the independently checked
  `qIsoOfIso_bijective`, with no abelian or balancedness assumption.

This section records a source-level semantic review. The author owns the
focused Lean checks of those nine row modules; this report does not replace
the final defining-module axiom audit or claim essential surjectivity.
