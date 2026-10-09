# Independent review: change of cofibrations for complex K-theory

The 15-source realization endpoint was independently accepted on
2026-10-09 at 04:46 UTC. The later based K-group wrappers have a separate
acceptance boundary below. None of this work is in the delivered 04:11 archive.

## Proven realization endpoint

For an actual replete full subcategory P of cochain complexes in an abelian
category, containing zero and closed under extensions, finite products and
mapping cones, the identity comparison from globally degreewise-split
cofibrations to ambient monomorphisms with quotient in P induces a genuine
homotopy equivalence of the existing S-construction realizations.

`splitDeloopingHomotopyEquiv P hcone` has precisely the original
`deloopingMap` as forward map, by `splitDeloopingHomotopyEquiv_toFun`.
Both weak-equivalence classes are the actual quasi-isomorphisms.
Mapping-cone closure is a structural condition on objects, not a disguised
approximation or K-equivalence assumption. Its strict-perfect and
locally-perfect instances have already been constructed geometrically.

## Semantic checks

- The actual arrow-category factorization uses Cone(id K) ⊞ L, with its
  proved inclusion and quasi-isomorphic projection. Functoriality is proved
  on arbitrary commutative squares. The accepted earlier factorization
  theorem identifies the quotient as Cone(-f), so it remains in P.
- The finite-filtration replacement is an actual functor. Its first vertex
  is unchanged; every successive map is a smaller cofibration. Its projection
  is objectwise weak, and two-out-of-three proves that it preserves
  objectwise weak natural transformations.
- Two actual natural weak comparison transformations give the homotopy
  inverse for the inclusion of finite-flag categories. These categories use
  arbitrary pointwise quasi-isomorphisms, not just natural isomorphisms.
- Canonical completion uses actual cokernels. Its horizontal maps stay in
  the smaller cofibration class by pushout stability, and its quotient
  transformations are weak by genuine Waldhausen gluing of cokernel squares.
- Initial-flag and row-completion maps have actual natural comparisons.
  Epic cancellation proves naturality for all weak natural transformations.
  The composite equivalence is straightened to have exactly the original
  row inclusion as forward map.
- The grid/row-nerve maps are strictly inverse simplicial maps. Their
  inclusion naturality preserves the original S-map exactly. The separately
  reviewed generic rowwise diagonal theorem requires no coherent row inverse.
- The extra joint-endpoint and relative-split-mono lemmas have explicit
  retractions. They are not silently treated as a complete cylinder-functor
  theorem. The special finite-flag argument does not assume the general
  Waldhausen approximation theorem.

## Independent Lean validation

All 15 manifest sources were read. The exact endpoint closure was rebuilt
with `lake --rehash` (2,301 jobs). The source hashes matched before and after.
A separate audit enumerated every declaration originating in all 15 modules,
required each module to contribute declarations, and recursively collected
its axioms. All 377 declarations, including private/generated ones, use only
`propext`, `Classical.choice`, and `Quot.sound`.

Arbitrary-universe consumers instantiate the equivalence for the actual
`StrictPerfect` and `Perfect` categories and check the exact existing forward
continuous map. Both generic source check and consumer audit exited 0.
The rehash produced non-failing existing style/unused-variable warnings.

- Source manifest: `logs/split-approximation-checked-sources.sha256`
- Manifest SHA256: `7928b8dbaf4882bdd9e2f6b3fa8dcc8cc996fcc545deadcced2a71f9e57840ce`
- Independent audit: `audits/SplitApproximationIndependentAudit.lean`
- Evidence: `logs/split-approximation-independent-{build,audit,hashes}.log`

The shared exact quotient-row machinery is covered by the independent
26-source Q/S stable review, and the earlier split structures and
factorizations by their nine-source review. The generic bisimplicial
realization theorem has its own seven-source review.

## Scope

This changes the cofibration convention on the same actual object categories.
It does not compare strict-perfect objects with all locally-perfect objects,
prove Gillet–Waldhausen, or establish perfect localization/nonconnective
spectra. On non-quasi-compact schemes it does not identify pointwise local
perfectness with a convention imposing uniform global Tor-amplitude.

## Based K-group wrapper

Accepted 2026-10-09 04:50 UTC. The two additional sources were read and
independently compiled into an isolated output overlay, without replacing
live dependency artifacts. The canonical identity comparison has the same
chosen zero in both structures. Uniqueness of a zero-object self-isomorphism
makes its rebasing functor the actual identity. Thus the generic based
homotopy-group theorem proves bijectivity of the previously defined
`splitComplexSubcategoryKMap`, rather than a substituted comparison.

`splitStrictKEquiv` and `splitPerfectKEquiv` instantiate this for every scheme
and nonnegative degree. Their forward homomorphisms are definitionally
`splitStrictToStrictKMap` and `splitPerfectToPerfectKMap`.

The independent full 17-source audit passed all 417 source-origin declarations.
Arbitrary-universe strict/local K-equivalence, bijectivity and exact forward-map
consumers passed. Both new source checks were warning-free, and all 17 hashes
matched before and after the checks. A first isolated-path setup lacked the
shared dependency overlay; that harness error is retained in
`logs/split-k-independent-initial-path-diagnostic.log`. The corrected complete
run exited 0 without modifying implementation sources.

- Full manifest: `logs/split-k-independent-sources.sha256`
- Manifest SHA256: `c145f53f8b951c168efd2718e3bf1ad39254419b32fc676cd64ce377cd477791`
- Audit and consumers: `audits/SplitKComparisonIndependentAudit.lean`
- Evidence: `logs/split-k-independent-{generic-check,scheme-check,audit,hashes}.log`

This acceptance does not assert an archive-wide rebuild. Public integration
and exact-source checkpoint validation are separate checks.
