# Independent review: simultaneous weak transport of actual homotopy fibers

## Semantic scope

The two unchanged sources in
`logs/weak-square-transport-independent-20261009/sources.sha256` have been
read completely, with their actual mapping-path functor, pullback HLP,
strict-fiber, and accepted weak right-properness prerequisites. No semantic
issue was found. **Accepted for this scope:** all independent checks passed.

`StrictWeakTransport` reuses the existing `strictBaseProjection` and genuine
HLP base-change lemma. Its new homeomorphism identifies the actual strict
fiber of a strict pullback with the original strict fiber. Its `strictMapOver`
is literally the supplied total-space map. When both projections are genuine
fibrations, its weak property follows from the accepted original homotopy-
fiber map, genuine strict-fiber inclusions, and empty-aware cancellation.
There is no repeated definition of the old projection or base-change lemma.

`WeakSquareTransport` first proves that functorial mapping-path replacement
preserves a weak total map, using its exact naturality with the actual
inclusion homotopy equivalences. This step needs no weak condition on the
base map. When the base map is also weak, genuine right properness makes
the original strict-pullback projection weak. Cancellation then makes the
actual strict comparison weak; no cartesian comparison premise is assumed.

For each supplied base point, the source endpoint fiber is homeomorphic to
the original homotopy fiber. The target strict-pullback fiber is likewise
homeomorphic to the original target homotopy fiber. Both projections are
genuine Hurewicz fibrations by the proved mapping-path and base-change
constructions. Transporting the strict-fiber result through these actual
homeomorphisms yields **exactly the original `HomotopyFiber.map`**: source
coordinate `u(x)`, entire path `v ∘ γ`. The final composite agrees
definitionally, including its proof-irrelevant endpoint equations.

The theorem concludes the empty-aware weak property, hence surjectivity on
actual path components and bijectivity of every finite homotopy-set map at
every source-fiber point, including π0. It permits empty spaces and empty
fibers. There are no connectedness, compactness, separation, CW-type, or
cartesian hypotheses. The common object universe is explicit, matching the
genuine all-parameter HLP API. Genuine homotopy equivalences are a proved
special case, without assumed based inverses.

This boundary concerns weak invariance under a strict square. It does not
prove compact-parametric gluing or the global weak-cartesian cube theorem.

## Validation

The isolated first-`LEAN_PATH` overlay is
`logs/weak-square-transport-independent-20261009/olean`. The two reviewed
artifact stems were excluded from prerequisite symlinks; the seven accepted
weak-fiber prerequisite modules resolve to the preceding fresh independent
artifacts. Both target sources rebuilt warning-free.

`audits/WeakSquareTransportIndependentAudit.lean` includes the combined
`Quillen.Library` import to detect cross-branch declaration-name collisions.
Its 22 consumers check original replacement/strict-comparison/fiber maps,
all finite degrees and all supplied basepoints, explicit π0 and π1, literal
source and complete path formulas, constant-path basepoints, component
surjectivity, empty fibers in both directions, strict-fiber π0, and the
full final homeomorphism composite by `rfl`.

The fixed **19** defining-origin audit (15 + 4), including private/generated
declarations and recursive dependencies, passed with only `propext`,
`Classical.choice`, and `Quot.sound`. All 22 consumers and the combined
public import passed warning-free; no declaration-name collision appeared.
Source and prerequisite hashes were rechecked after the final pass.
Evidence is in
`logs/weak-square-transport-independent-20261009/`.
Frozen manifest fingerprint:
`a5def0470dd70262b16e11e9faf0e78b3f30706445f74bc4aa1454a9c1176815`.
Scripts: `logs/verify-weak-square-transport-independent.sh` and
`logs/audit-weak-square-transport-independent.sh`.
Final audit: `audit-final.log` in the evidence directory.
Checks use the shared slot1 lock and `-j1`, without a live Lake rebuild.
No production source has been modified by this review.
