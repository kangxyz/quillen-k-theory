# Degreewise split complex models

Status: checked implementation, awaiting independent semantic review. The
six files below are separate from the previously accepted public endpoint;
no accepted source or public umbrella was changed.

## Frozen initial scope

- `Quillen/Waldhausen/SplitComplexes/Basic.lean`
- `Quillen/Waldhausen/SplitComplexes/Subcategory.lean`
- `Quillen/Waldhausen/SplitComplexes/ExactSequences.lean`
- `Quillen/Waldhausen/SplitComplexes/Factorization.lean`
- `Quillen/PerfectComplexes/SplitKTheory.lean`
- `Quillen/PerfectComplexes/SplitSupport.lean`

## Mathematical contract

Cofibrations split globally in each degree, but their retractions need not
be chain maps. For full subcategories the quotient must remain in the
selected object predicate. `splitSubcategoryCofibrations_iff` identifies
this condition exactly with actual degreewise split short exact sequences.
Weak equivalences remain actual quasi-isomorphisms.

Pushout stability is proved by constructing a retraction after pushout and
applying this degreewise; evaluation preserves the actual pushout. The
full-subcategory construction uses the previously proved extension closure
and pushout-preservation theorem. Quasi-isomorphism gluing follows from the
accepted ambient theorem. No Waldhausen axiom or comparison theorem is
postulated.

This gives split-cofibration Waldhausen structures and genuine connective
S-construction K-groups for strict-perfect, locally-perfect, and supported
complexes. The identity comparison into the ambient-monomorphism convention
is exact and induces actual K-homomorphisms. Strict-to-local, open-restriction,
and support-forgetting maps are constructed too.

Every ambient chain map `f : K → L` factors through `Cone(id K) ⊞ L`.
The first factor is degreewise split and the second is a proved chain
homotopy equivalence, using the standard contraction of the identity cone.
In this initial scope, membership of the factorization and its quotient in
a chosen full subcategory is not asserted.

## Deliberate exclusions

No change-of-cofibrations K-equivalence, approximation theorem,
Gillet–Waldhausen theorem, or localization theorem is asserted. The
pointwise-local object predicate is unchanged, so uniform global
Tor-amplitude on non-quasi-compact schemes remains a separate issue.
Ordinary vector-bundle exact sequences need not split globally; therefore
the accepted degree-zero vector-bundle comparison is not automatically an
exact functor into this split model.

## Verification

Each of the six source files compiled individually on the pinned toolchain,
serially under `/tmp/quillen-lean-slot-2.lock`. The source-token audit passed.
`audits/SplitComplexesAudit.lean` recursively audits every declaration whose
origin is one of these modules, including private/generated declarations.
All **95 declarations** passed, with only `propext`, `Classical.choice`, and
`Quot.sound`. The audit also prints the central endpoint axiom closures.

Evidence: `logs/split-complexes-axioms.log`.
Frozen source fingerprints: `logs/split-complexes-checked-sources.sha256`.
This is focused verification, not a clean full-library/archive verification.

## Factorization extension: three additional files

The initial six sources remain byte-for-byte unchanged. The following
additional files extend the checked endpoint and await independent review:

- `Quillen/Waldhausen/SplitComplexes/FactorizationQuotient.lean`
- `Quillen/Waldhausen/SplitComplexes/FactorizationSubcategory.lean`
- `Quillen/PerfectComplexes/SplitFactorization.lean`

`quotientMap` is the actual chain map from `Cone(id K) ⊞ L` to `Cone(-f)`.
The factorization inclusion followed by this map is zero. A retraction and
quotient section are constructed separately in each degree and proved to
satisfy all three short-complex splitting identities. Hence
`quotientSequence_shortExact` proves that this is the actual quotient short
exact sequence, not merely a derived or K-theoretic substitute.

For a cone-closed extension-closed object predicate, `middle_property`
proves membership of the middle object from identity-cone and biproduct
closure. The explicit quotient belongs by cone closure.
`exists_subcategory_factorization` therefore factors every map in that
full category as an actual split cofibration followed by a quasi-isomorphism.
Its cone-closure hypothesis is discharged for both geometric applications.

`locallyPerfect_mappingCone` is a new geometric closure theorem. Near each
point it chooses a common neighborhood carrying strict derived models of
the two endpoints, uses the proved local strict-model theorem for the
actual distinguished mapping-cone triangle, and transports the resulting
model through actual restriction/cone and restriction/composition
isomorphisms. It uses no global strict representative.

The final endpoints are `exists_splitStrict_factorization` and
`exists_splitPerfect_factorization`. Thus the factorization middle object
and its actual quotient stay strict perfect or locally perfect,
respectively. This supplies the map-factorization input for the identity
change-of-cofibrations comparison. No approximation theorem or induced
K-equivalence is asserted; supported-category factorizations are not added.

All three added files compiled serially without warnings. The expanded
recursive audit `audits/SplitFactorizationAudit.lean` passed all **128**
declarations from the nine source modules, including private/generated
helpers, with only `propext`, `Classical.choice`, and `Quot.sound`.
Evidence: `logs/split-factorization-build.log`,
`logs/split-factorization-axioms.log`, and
`logs/split-factorization-source-token.log`.
The nine-source fingerprint manifest is
`logs/split-factorization-checked-sources.sha256`; the initial six-source
manifest still verifies unchanged.
