# Complete original-map weakness from strict finite cube HELP

Status: the single source compiled warning-free at 2026-10-09 14:53:32 UTC
and is frozen in `logs/strict-finite-criterion-sources.sha256`, fingerprint
`4f238b7ba92af2549d8e1a0d9cbd8811093ffb7540c21d6ae7e48801fa3bcd3c`.
The fixed 8-origin recursive audit and all 13 consumers passed warning-free
at 2026-10-09 14:57:13 UTC, using only `propext`, `Classical.choice`, and
`Quot.sound`. Source hashes match. Independent acceptance is not yet claimed.

## Exact hypothesis and endpoint

`Quillen.CubicalSubdivision.StrictBoundaryHELP f` says precisely:
for every literal unlifted finite cube, every original boundary map `a`, and
every target cube map `b` satisfying the pointwise strict square, there is a
continuous filler `c` with `c|boundary = a` and an ordinary homotopy
`f∘c ~ b` relative to the entire original cube boundary.

`StrictBoundaryHELP.isWeakHomotopyEquivalence` concludes the complete,
empty-aware weak-equivalence property of the original continuous map `f`.
`isWeakHomotopyEquivalence_of_strictBoundaryHELP` accepts the exact raw
quantified hypothesis directly. Source and target topological spaces retain
independent universes. There are no separation, compactness, fibration,
CW-type, equivalence, or positivity assumptions on these spaces or degrees.

The conclusion includes actual component coverage and bijectivity of every
original `homotopyGroupMap (N := Fin n) f`, for all basepoints and every
`n : ℕ`, including the ungrouped degree-zero homotopy set. It does not assert
point-surjectivity of `f`.

## Proof

1. The genuine empty boundary of the zero-cube gives a source point and an
   actual path from its image to each target point. This handles the empty
   source case without a vacuous based-only weak property.
2. For surjectivity, apply the hypothesis to each original `GenLoop`
   representative with its constant source boundary. The supplied relative
   comparison homotopy proves equality of the original quotient classes.
3. For injectivity, use the actual side-and-both-caps pushout to prescribe
   the two source loop representatives and their fixed boundary. Its
   canonical presentation is the next cube boundary, through the proved
   original boundary homeomorphism and first-coordinate homeomorphism.
   The exact boundary extension of the resulting filler is the required
   homotopy between the original representatives, fixed on every original
   boundary point. No comparison on arbitrary compact pairs is required.

The auxiliary `presentation_extension` and `cylinder_extension` transport
only these literal test parameters; they do not posit or derive lifting for
arbitrary compact spaces. No arbitrary prescribed boundary homotopy is an
input, and no full compact HELP assumption is introduced.

## Verification scope

Implementation: `Quillen/Topology/HELP/StrictFiniteCriterion.lean`.
Own audit: `audits/StrictFiniteCriterionAudit.lean`.
Initial replay/audit: `logs/strict-finite-criterion-initial-audit.log`.

The 13 exact-map consumers include distinct source/target/parameter universes,
the raw strict-square criterion, all-degree actual homotopy maps, explicit
zero-dimensional bijectivity, component coverage, empty-source consequences,
and the exact complete side/caps boundary extension, including its zero case.
This criterion is an input to the separate mixed-gluing assembly; it is not
itself an open-chart or global bar/fibration theorem.

Final guarded log: `logs/strict-finite-criterion-fixed8.log`.
Author evidence: `logs/strict-finite-criterion-evidence.sha256`.
No implementation or consumer repair was needed after the first source check.
