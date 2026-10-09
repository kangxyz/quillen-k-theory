# Independent review: weak fibers and genuine right properness

## Scope and semantic finding

The seven unchanged sources in
`logs/weak-fiber-equivalence-independent-20261009/sources.sha256` were read
completely, together with the relevant actual mapping-path, strict-fiber,
homotopy-pullback, fiber-map, and pointed-set LES prerequisites. **Accepted for this scope.** No semantic issue was found; final fixed-count
verification passed.

The original `IsWeakHomotopyEquivalence` separately requires surjectivity on
actual path components, so the based conditions cannot become vacuous for
an empty source with nonempty target. Both cancellation directions preserve
this clause. Cancellation of the second map uses the actual degree-zero
map to reflect component paths. `ComponentCriterion` proves degree-zero
bijectivity by the genuine quotient homotopies, without a group on π0.

`WeakFibers` uses the genuine mapping-path endpoint fibration and its
strict-fiber homeomorphism to transfer the LES calculation to every point
of every actual homotopy fiber. Fiber nonemptiness comes separately from
component surjectivity. The converse `WeakCriterion` proves component
reflection by projecting actual fiber paths and proves positive-degree
bijectivity by the original LES, including its pointed-set tail.

`WeakPullback` applies this criterion to the unchanged homotopy-pullback
base projection using its already constructed actual fiber equivalences.
`ProjectionFibration` identifies the original homotopy-fiber projection with
a genuine homotopy-pullback base projection through an actual source
homeomorphism; path reversal occurs only in this auxiliary presentation.
The HLP is the covering-homotopy property for all parameter spaces in the
displayed universe, not a fiber-equivalence hypothesis.

The final right-properness theorem retains the original second projection
of the strict pullback. It is the composite of the genuine strict/homotopy
pullback comparison, symmetry, and the weak homotopy-pullback projection.
`sourcePullbackHomeomorph` then identifies source change on fibers with
this literal strict pullback. Consequently
`HomotopyFiber.mapOver_isWeakHomotopyEquivalence` proves the full weak
property for the unchanged `mapOver`; its source coordinate is the original
source map and its complete original path coordinate is retained literally.
Every original finite homotopy-set map is bijective, explicitly including
n = 0. Empty fibers and empty ambient spaces are covered.

The cancellation and component lemmas allow independent object universes.
The HLP/fiber/right-properness boundary explicitly uses a common universe,
matching the actual universal parameter-space lifting API. There is no
separation, compactness, CW-type, or global inverse-family assumption.
Simultaneous weak changes of both total and base spaces and the global
weak-cartesian cube are outside this seven-source boundary.

## Validation

- All seven production sources rebuilt warning-free into the isolated
  first-`LEAN_PATH` overlay
  `logs/weak-fiber-equivalence-independent-20261009/olean`.
- Reviewed source artifacts were excluded from the overlay's prerequisite
  symlinks; the ordered rebuild created fresh local artifacts. `deps.log`
  confirms the audit's final import resolves to this overlay.
- The recursive declaration-origin scan passed all **40** origins, including
  generated/private declarations. Per module in manifest order:
  **5, 1, 5, 2, 1, 12, 14**. Only `propext`, `Classical.choice`, and `Quot.sound`
  occur recursively.
- The audit has **30** strengthened consumers for independent universes,
  actual component paths, full fiber criterion, genuine HLP and right
  properness, original source/path formulas, explicit π0, empty source,
  empty target, empty strict pullback, and both directions of empty-fiber
  transport.
- The reviewer's initial empty-target consumer needed an explicit False
  elimination for elaboration. Only the audit was repaired; no production
  source was changed. The fixed40/30-consumer rerun passed warning-free.

Audit: `audits/WeakFiberEquivalenceIndependentAudit.lean`.
Scripts: `logs/verify-weak-fiber-equivalence-independent.sh` and
`logs/audit-weak-fiber-equivalence-independent.sh`.
Evidence directory: `logs/weak-fiber-equivalence-independent-20261009/`.
Frozen manifest fingerprint:
`6477a450a39e4f3f559c14264e4ed26e09b18a2e6bd062f8f9a83a13c5e71faa`.
All Lean checks use the shared slot1 lock and `-j1`; no live Lake rebuild.

Final audit: `logs/weak-fiber-equivalence-independent-20261009/audit-final.log`.
Source hashes were checked before and after the final audit; the inspected
accepted prerequisites were also rehashed unchanged. No production source
or production artifact was modified by this review.

A further combined `import Quillen.Library` plus weak7 check passed
warning-free using the same fresh overlay. Its three consumers check the
original weak `mapOver` endpoint, the explicit degree-zero map, and the
literal retained path. No cross-branch declaration-name collision appeared.
See `audits/WeakFiberEquivalenceLibraryConsumer.lean`, `library-consumer.log`,
and `hashes-after-library.log` in the same evidence directory.
