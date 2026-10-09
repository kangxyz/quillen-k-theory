# Independent review: actual generic relative-row completion

Accepted 2026-10-09 10:39 UTC. All 407 source lines and the exact cofiber,
isomorphic-source Reedy cofibration and coarse cofiber-acyclicity prerequisites
were inspected. Three fresh excluded-target source rebuilds, the fixed-86
recursive-origin audit (32+33+21), and 21 consumers passed warning-free, with
source/prerequisite hashes unchanged. Only standard Lean logical axioms occur.

Frozen boundary: `logs/relative-rows-completion-sources.sha256`.

## Genuine construction

`zeroAugment` adjoins the actual chosen zero to the unchanged finite chain.
Its positive objects and arrows are the original ones, and its positive
natural-transformation components are literal. The functor preserves actual
cofibration chains and pointwise weak maps. Restriction to the successor
indices recovers the original chain strictly.

`cofibrationArrowDiagram` places each original inclusion in the genuine
extension category. Its horizontal arrows satisfy the actual Reedy condition:
the source map is an isomorphism, and the target map is the given cofibration.
Its displayed quotient squares are genuine componentwise identity pushouts,
reflected from the full arrow category. Applying the already proved exact
cofiber functor constructs the actual quotient row, including zero diagonals,
all horizontal cofibrations and all cofiber squares. The quotient projections,
arbitrary transformation maps, identity/composition laws and fine weakness
are retained through that original functor.

For a fine-cofibration/coarse-weak chain, applying this to its zero augmentation
produces an actual relative row. Every tail cofiber is coarse-acyclic by the
original coarse gluing axiom. This construction needs neither coarse extension
nor saturation. The original quotient-by-zero maps are actual isomorphisms
and give `relativeCompletionInitialIso`; its forward components are the
unchanged displayed quotient projections. These isomorphisms are natural for
all original chain transformations, and pointwise fine weakness is preserved.

The entire construction works for arbitrary Waldhausen structures with
independent object/morphism universes. No exact-category or abelian hypothesis
is used in the generic construction, and no desired row or quotient predicate
is assumed in place of the given fine-cofibration/coarse-weak chain.

## Limits

This proves the genuine completion direction and essential-image statement.
To identify every existing relative row with a coarse-weak initial chain, the
separately stated coarse extension hypothesis is still needed. The restricted
presentation equivalence is separate. No weak-class fibration, quasi-isomorphism
K-equivalence or global diagonal-fiber conclusion follows from this endpoint.

## Validation

The first-path overlay `/tmp/quillen-completion-independent-1033` excludes all
three target artifact families. The dependency listings show the final module
uses both freshly rebuilt prerequisites. The 14 original exact-map consumers
are retained, including actual inner quotient-row categories and bounded-term
complexes. Seven additional consumers expose strict zero augmentation, unchanged
successor components, original identity/composition laws and degree-zero
completion, giving 21 consumers total.

The initial audit driver needed an explicit `Array Nat` annotation for its
origin counters. The failed driver/log were preserved; no production source
was changed. The corrected fixed-86 audit and all consumers passed, followed
by matching source/prerequisite rehashes.

Script: `logs/verify-completion-independent.sh`.
Audit: `audits/RelativeRowsCompletionIndependentAudit.lean`.
Evidence: `logs/completion-independent-artifacts.sha256`.
This accepted boundary is outside the delivered 09:45 version6 archive.
