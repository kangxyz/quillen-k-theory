# Independent review: the genuine coarse-acyclic subcategory

Date: 2026-10-09. Result: **accepted for the frozen structural endpoint**.
No implementation source was changed.

## Exact input and category

`NestedWeakEquivalences V` supplies a second actual Waldhausen structure, equality
of the two cofibration classes and chosen zero objects, and inclusion of the fine
weak class into the coarse one. There is no realization, fiber, or equivalence
conclusion inside this input.

`AcyclicCategory N` is the original full subcategory of objects for which the
canonical coarse-zero map is coarse-weak. Object/hom universes remain independent.
The inherited structure has the literal inverse-image fine cofibrations and
**fine** weak equivalences. Its inclusion is unchanged on objects and maps; its
chosen zero maps definitionally to the fine chosen zero and propositionally to
the coarse one by the explicit input equality.

## Derived structural proofs

I read the entire source and checked its dependence on the previously reviewed
actual cofiber construction and weak-acyclic predicate.

- Repleteness uses composition with the actual isomorphism.
- Coarse gluing against the all-zero pushout proves closure of an actual pushout
  of three coarse-acyclic objects along a cofibration.
- The original fine structure's pushout therefore belongs to the full subcategory.
  Full faithfulness reflects its actual universal property.
- Every arbitrary displayed inherited pushout is an ambient pushout: comparison
  with the constructed one uses the actual unique pushout isomorphism.
- All inherited Waldhausen axioms, including gluing, follow from those genuine
  ambient squares and the fine structure. These axioms are proved, not supplied.
- The original inclusion into the fine structure, identity change to the coarse
  structure, and inclusion into the coarse structure are genuinely exact.
- `fine_cofiber_acyclic` proves closure of the already defined original fine
  cofiber; it permits the fine chosen zero via its actual zero-object property.

None of this requires saturation, an extension axiom, or a cylinder. Only the
separate `acyclicInclusion_map_coarse_weak` uses two-out-of-three to show that every
map between coarse-acyclic objects becomes coarse-weak. That theorem does not
change the inherited fine weak-equivalence class.

## Independent verification

A fresh isolated source rebuild used the preceding independently rebuilt
weak-cofiber dependency; other unchanged dependencies were linked. Lean 4.34.0
ran with `-j1` under slot1, with acquisition logged in
`logs/complex-acyclic-independent-session.log`. No production olean was replaced.

`audits/FibrationAcyclicSubcategoryIndependentAudit.lean` checks exactly **48
origins** from the defining module, including generated/private constants.
Recursive axiom checks allow only `propext`, `Classical.choice`, and `Quot.sound`.
All origins and arbitrary-independent-universe consumers passed warning-free.

Consumers inspect the actual object predicate, literal inclusion maps, fine
cofibration/weak classes, both zero identifications, genuine structural exactness,
arbitrary displayed pushout preservation, and the original fine cofiber. Added
independent consumers check saturation-free ambient pushout closure and actual
inherited-plus-ambient pushout existence, as well as equality of the inherited
weak property with the original fine inverse-image property. Frozen hashes match
before and after all checks.

## Limits and evidence

This is the genuine structural acyclic category required as input to a fibration
argument. No relative-realization fiber theorem, homotopy-fiber comparison,
localization, or based K-equivalence is established here.

Source: `Quillen/Waldhausen/Fibration/AcyclicSubcategory.lean`

SHA-256: `6f90b99f74773e36daf0dd5e835a07045e5fa03882cbb25d7e2291637c073693`

Evidence directory: `logs/fibration-acyclic-subcategory-independent-20261009/`.
`sources.sha256` has manifest digest
`3c906a0ba4a470259081abda5d02023ecd53875c37256aeae00851bea7f29c0a`.
`check.log`, `audit.log`, `deps.log`, and both `hashes-*.log` record fresh source,
recursive origin, consumer and hash checks. `artifacts.sha256` fixes the exact
audit, report, logs and fresh artifact.
