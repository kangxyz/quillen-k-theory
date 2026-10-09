# Independent review: cubical HELP and the original weak equivalence

Accepted on 2026-10-09 at 10:48 UTC. No production source was changed.

## Frozen scope

`logs/cubical-help-sources.sha256` freezes `HELP/CubeBoundary`,
`HELP/CubicalLifting`, and `HELP/FiberwiseWeakEquivalence`, with fingerprint
`490e4357237238a0907983d5d5569c020e8e6aa466fc324f70fbd8fc4ffaf02b`.

## Semantic findings

The boundary presentation is built from the genuinely empty zero-dimensional
boundary by the actual cylinder-boundary pushout and the explicit coordinate
homeomorphism. The proof establishes compactness, HEP, and equality of its
image with the entire original cube boundary. It does not assume the
presentation is a boundary homeomorphism.

Surjectivity lifts actual generalized loops and uses coverage of the entire
boundary to retain the original basepoint. Injectivity glues the two original
loops on the caps and the constant basepoint on the side by the genuine
pushout universal property. The lifted cylinder yields the original relative
homotopy. Pointwise boundary coverage suffices; no continuous choice of
preimages is made. Both arguments work in dimension zero without using a
group structure there.

The separate empty-boundary point test supplies actual component surjectivity,
so the empty-source case is not hidden behind vacuous based hypotheses.
`ContractedStrictHELP` is a genuine lifting condition with a displayed
contraction, not the weak-equivalence conclusion in disguise. Its input is
proved from the accepted contracted-test theorem using genuine HLP of both
original projections and compact HELP of the actual strict-fiber maps.
Consequently `isWeakHomotopyEquivalence_of_fiberHELP` concerns the original
total map, including its original zero-dimensional map and components, with
arbitrary total spaces in one common universe.

## Independent validation

All three target oleans were removed from a complete isolated copy of the
import root before fresh source compilation. All fresh builds passed
warning-free. `audits/CubicalHELPIndependentAudit.lean` scans each defining
module origin in a single environment traversal, requires all three origins,
and fixes the total at 65. Recursive axiom collection found only `propext`,
`Classical.choice`, and `Quot.sound`.

Twenty-four consumers passed with the combined public library import. They
cover exact boundary/cylinder/contraction maps, component surjectivity,
all finite homotopy-set maps with explicit degree zero, empty source and
empty zero-boundary cases, the genuine chosen-fiber path-transport application,
and a whole prescribed-boundary homotopy stated at every time. The source and
frozen prerequisite hashes matched before and after checking.

Evidence: `logs/cubical-help-independent/artifacts.sha256`.
The initial source-review and final audit run terminated successfully; no
production repair or weakening of a hypothesis was needed.

## Boundary

This does not prove weak equivalence implies compact HELP, finite weak
pushout gluing, or the global connected-row diagonal fiber theorem. Those
remain separate obligations.
