# Independent review: the actual first-pushout endpoint collar

**Accepted, 2026-10-09 14:45:11 UTC.** The fresh source rebuild, fixed-51
recursive-origin audit, all 21 strengthened consumers, and before/after
provenance checks passed warning-free. Production source was unchanged.

## Frozen source and scope

`Quillen/CategoryTheory/TheoremB/NormalizedFirstCollar.lean`

Source SHA-256:
`a322c18eaf75d753cfedf0dac46bc6bbd47ed0ce13d8ec74f0df3c55b93f9edb`.
Manifest `logs/normalized-first-collar-sources.sha256`, fingerprint
`efd9c2d87169c3873e780cdcf2f72468eb43eba7a42bdfbc34ab8ac67113117e`.
The implementation remained unchanged throughout this review.

The input is the existing genuine `NormalizedOpenGluing.Data`, a continuous
height on its bridge equal to one on the original left attaching map, and a
cutoff strictly below one. No fibration, homotopy equivalence, or injectivity
assumption is needed to construct the open collar, its actual pushout square,
or the complement-fiber property.

The deformation endpoint additionally takes a genuine local strong deformation
retraction of the attaching end into that bridge collar. Preservation of the
original base by this local deformation is an explicit additional hypothesis
for the base-preservation conclusion. This is local geometric data; it is not
an assumed deformation of the entire bridge.

## Semantic findings

- The height on the original `First` is an actual pushout-descended continuous
  map. Its values on the bridge and unchanged end are proved exactly.
- The collar is the literal open upper-height subset of `First`, with its
  actual subspace topology. The bridge collar is the corresponding original
  subset of the bridge.
- `firstEndCollar_isPushout` uses the proved open-restriction colimit theorem,
  then actual homeomorphisms of the restricted source, bridge, and end.
  The attaching map and all original coordinate maps are preserved. No
  arbitrary pushout/pullback interchange is invoked.
- The local SDR is extended by the existing genuine pushout SDR construction.
  This glues the relative homotopy using product with the compact interval,
  whose colimit preservation is available. The complete deformation fixes
  the unchanged end, and its base equation holds for every point and time.
- Every bridge point projects into the original overlap `V`. Actual pushout
  representatives therefore show that a point whose original base lies
  outside `V` must come from the unchanged end and belongs to the collar.
  No endpoint-only argument is used to control a whole path.
- An independent consumer applies the accepted `BoundaryTrackCover` to this
  literal collar and complement property. It derives the exact open cover
  of compact-boundary test parameters, retaining every prescribed track
  time. No compactness of the ambient test parameter or injectivity of its
  boundary map is added.

I also inspected the relevant primitive `Data` definitions, `OpenPushout`'s
actual continuous descent/colimit proof, `OpenAttachment`, and the pushout
SDR/base-preservation constructions.

## Lean verification

The fresh first-`LEAN_PATH` overlay excludes all target artifacts. The source
was independently recompiled there, and the audit's dependency output checks
that it imports this regular fresh artifact rather than the live one.
The dependency capture starts from the target, independent audit, and explicit
implicit `Init` source closure. It pins 3,858 prerequisite source files,
18,223 prerequisite `.olean*` artifacts, and the toolchain/project files.

The independent audit is `audits/NormalizedFirstCollarIndependentAudit.lean`.
It recursively checks every defining-module origin, including private and
generated declarations, with a fixed count of 51 and only the standard axioms
`propext`, `Classical.choice`, and `Quot.sound` permitted.

Its 21 consumers cover the original height and inclusion formulas, actual
collar pushout, local SDR's exact forward map, retraction, both homotopy
endpoints, fixed unchanged-end points at all times, the unchanged local bridge
homotopy, original base retention, empty overlap and empty original base,
whole-track complement control, and the exact bad-set/cover application with
independent test-space universes.

The first harness copy captured an author-side provisional count guard and
used an unavailable empty-set lemma in two consumers. These audit-only issues
were repaired without touching production source. The initial logs remain
preserved; the final replay uses exactly the intended count and explicit
transport of the empty-set membership proof.

## Evidence and limits

Evidence directory: `logs/normalized-first-collar-independent-20261009`.
The fresh build is in `check.log`; final origin/consumer results are in
`audit.log`. Before/after source, dependency, fresh-artifact, audit-driver,
and toolchain hashes are recorded separately. The final terminal driver is
`logs/normalized-first-collar-independent-final2-driver.log`; its successful
result is copied to `terminal.log` in the evidence directory. The consolidated
evidence manifest is `artifacts.sha256` in that directory.

The checker is Lean 4.34.0, commit
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`.

This boundary does not supply the local bridge SDR from weak inputs, a whole
bridge equivalence, HLP of the first attachment, finite lifting of `firstEnd`,
or a weak-equivalence theorem for `firstProjection`. The concrete bridge
collar construction and mixed finite attachment assembly are separate scopes.
