# Independent review: original relative-row realization lifting

Accepted on 2026-10-09 at 10:33 UTC. All three production sources are unchanged.

## Frozen scope

The manifest `logs/row-realization-lifting-sources.sha256` has fingerprint
`908cfbf29bc4e17ec42e38f60315d4d2bb91c252481d72511f4d69e23c584d37`.
Its modules are:

- `Quillen.Waldhausen.Fibration.RelativeRows.FiberTransport`
- `Quillen.Topology.HELP.SquareRealizationLifting`
- `Quillen.Waldhausen.Fibration.RelativeRows.RealizationLifting`

## Semantic findings

The all-point fiber HELP theorem uses an individual path from the genuine
chosen zero in the actual connected row realization and the accepted
arbitrary-square path-transport theorem. It never selects a continuous family
of paths or inverses.

The normalized comparison is the original map of mapping-path endpoint
fibrations. Its strict fiber is identified with the original square's
homotopy-fiber map by the actual endpoint and strict-pullback fiber
homeomorphisms. These identify the entire path, not merely its endpoints.
Full compact HELP is transferred by these maps and retains the prescribed
boundary homotopy.

The final realized-monomorphism lifting theorem invokes the proved relative
skeletal lifting argument using actual contracted simplex tests. Its sole
structural input in the row instance is `NestedWeakEquivalences`; it assumes
neither the sought global fiber conclusion nor a homotopy equivalence of the
row transition comparison. The degree-zero empty boundary is included.

## Fresh validation

The complete local import root was copied to the isolated overlay
`/tmp/quillen-row-realization-lifting-independent`. All three target oleans
were excluded before their source rebuilds, which passed warning-free.
The live source/import outputs were not changed.

`audits/RelativeRowRealizationLiftingIndependentAudit.lean` scans all defining
module origins in one traversal, requires every module to occur, and fixes the
total at nine (4, 2, 3). Recursive axiom collection accepted only `propext`,
`Classical.choice`, and `Quot.sound`. Fifteen consumers passed, including:

- literal source and entire postcomposed-path formulas;
- chosen-zero specialization and all-point full-boundary HELP;
- the entire strict-fiber homeomorphism square by definitional equality;
- actual normalized source/path coordinates;
- all realized simplicial monomorphisms and explicit zero-dimensional boundary;
- an actual diagonal filler with both triangle equations.

The first added consumer used the nonexistent field `Homeomorph.toContinuousMap`.
That audit-only spelling error was corrected to `toHomotopyEquiv.toFun`; the
initial source/log remain preserved. No production repair was required.
The final audit and source/dependency hash rechecks passed with terminal exit 0.

Evidence is indexed by `logs/row-realization-lifting-independent/artifacts.sha256`.

## Boundary

This proves actual lifting against realized simplicial test pairs. It does not
supply an inverse family on arbitrary path-space pullbacks, finite weak
pushout gluing, or the connected-row global diagonal fiber theorem.
