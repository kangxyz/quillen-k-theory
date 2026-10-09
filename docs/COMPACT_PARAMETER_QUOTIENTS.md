# Quotient descent over the actual compact test

## Source-checked boundary

The three sources in `logs/compact-parameter-quotient-sources.sha256` prove:

1. `Maps/CompactParameterQuotient`: restriction of a quotient to a closed
   target subset is quotient; product by a locally compact parameter preserves
   quotient; restriction to the explicitly closed matching locus gives the
   literal map `(x,d) ↦ (q x,d)` between original pullback subspaces.
   A closed graph of the displayed test map suffices. Hausdorffness of the
   entire base is an optional sufficient condition, not a general assumption.
2. `Realization/CompactGraph`: a compact-source continuous map into an actual
   simplicial realization has closed graph in the original product topology.
   The map factors through a finite realized subcomplex. That subcomplex is
   Hausdorff and its original inclusion is a closed embedding. The graph is
   closed there, and its image under the product closed embedding is exactly
   the original graph. No global realization Hausdorff instance is assumed.
3. `Pushout/CompactParameter`: the literal sum of the two outgoing maps of a
   displayed topological pushout is quotient, by the actual colimit topology.
   Its matching pullback over a compact locally compact realization-valued
   test is the actual quotient map asserted above.

All generic source, target, parameter and base universes are independent.
The pushout's objects share the ordinary TopCat universe; its parameter has
an independent universe. No nonemptiness or positive dimension is required.

## Use and limits

This proves the finite-test quotient descent needed for a continuous
piecewise mapping-cylinder lift. It does not assert preservation by arbitrary
products or arbitrary pullbacks, and does not itself construct a homotopy
lift. A base merely homotopy equivalent to a realization does not obtain this
closed-graph property from these statements. An actual homeomorphism does.

`SumSubtype` and the mapping-cylinder finite-lift modules remain a separate
construction boundary and are not included in this manifest.

## Checks

All three production sources compiled warning-free in the final focused
checks. `audits/CompactParameterQuotientAudit.lean` imports `Quillen.Library`,
recursively audits every declaration by defining module, and checks13 actual
map consumers, including independent universes, empty parameters and a point
parameter. Its fixed11 defining-origin audit and all13 consumers passed warning-free
at13:08:36Z in `logs/compact-parameter-quotient-fixed11.log`. Recursive axioms
are limited to `propext`, `Classical.choice`, and `Quot.sound`; source hashes
were rechecked unchanged. The successful combined umbrella-import run is
retained as integration evidence. Independent review uses narrow imports
to avoid loading unrelated library declarations.
