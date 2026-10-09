# Independent review: original mixed finite-chain replacement

## Scope

Reviewed frozen `Fibration/MixedChainReplacement` and
`Fibration/ComplexChainReplacement`, identified by
`logs/mixed-chain-replacement-sources.sha256`.

The endpoint is the unchanged finite cylinder replacement on actual
`ComposableArrows C n`. It preserves pointwise fine-weak transformations
under a structural middle-square condition, resolves coarse-weak arrows by
actual fine cofibrations that are coarse-weak, and retains the original
coarse-weak projection and first object. There is no nerve/realization,
fibration, strict ordinal-reindexing, or fine-projection conclusion.

## Semantic inspection

Both sources and their actual factorization dependencies were read.

- Fine preservation is induction on the actual recursive stages. Each
  successor uses exactly the given middle-functor fine-square property.
  No fine saturation or fine projection premise is used.
- Coarse arrow weakness uses the original projection naturality square,
  the proved pointwise coarse projection, and coarse two-out-of-three.
  Actual fine cofibrancy follows from the literal equality of cofibration
  classes, separately from weak-arrow preservation.
- The complex factorization keeps the accepted identity-cone middle,
  inclusion, and projection. Its inherited ambient cofibration is obtained
  from the proved split cofibration, whose actual quotient remains in the
  same full complex subcategory.
- Fine weak maps in the concrete model are isomorphisms. Two isomorphic
  endpoints give an actual arrow isomorphism, preserved by the unchanged
  middle functor. Coarse weak maps remain genuine quasi-isomorphisms.
- The concrete scope requires zero, repleteness, extension closure, finite
  products and actual cone closure. It adds no kernel or shift closure and
  no global projectivity. Object/hom universes remain independent because
  no realization comparison is present.

## Independent verification

A separate first-path overlay was created with all target artifact families
excluded before rebuilding. Unchanged dependencies are linked from the
accepted artifact tree; target outputs are rebuilt only into the separate
overlay. No live sources or artifacts are modified.

The independent audit retains the fixed28 all-origin guard and all16
original consumers, adding5 original-factor/degree-zero/arbitrary-scheme
consumers. The stronger scheme consumers retain the actual quasi-isomorphic
projection and the actual inherited cofibration/quasi-isomorphism
replacement arrows. Recursive axioms are restricted to `propext`,
`Classical.choice`, and `Quot.sound`.

The replay script is `logs/verify-mixed-chain-replacement-independent.sh`.
Evidence is under `logs/mixed-chain-replacement-independent-20261009/`.
Accepted at 2026-10-09 09:51:24 UTC. Both fresh source rebuilds, the fixed28
recursive-origin audit and all21 consumers passed with no warnings, errors,
or unsupported axioms. Exact source hashes, all304 dependency-source hashes,
and all304 linked dependency-artifact hashes rechecked unchanged. Dependency
listings verify the fresh import chain, and both target artifacts are actual
new overlay files rather than links to live outputs.

`deliverables.sha256` in the evidence directory records the source/dependency
manifests, before/after checks, fresh-path verification, compile/audit logs,
independent audit, replay script, and this report.

The quotient-presentation and actual mixed-model comparisons remain
separate obligations; a coarse projection alone is not a fine-category
natural comparison.
