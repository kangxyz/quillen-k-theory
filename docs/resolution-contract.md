> Development scope: the exact public checkpoint source inventory is in CHECKPOINT.json. This document also records checked working-tree developments not yet independently integrated. The current released resolution facade is length-one; perfect-complex comparison endpoints are not claimed.

# Quillen resolution: proved contract and canonical maps

## Primary source

Charles Weibel, *The K-book*, Chapter V, Theorem 3.1 and Proposition 3.1.1,
chapter pages 20–21:
https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.V.pdf

The hypotheses are a full inherited exact subcategory closed under extensions
and kernels of admissible epimorphisms between its objects, and an actual finite
admissible resolution of every ambient object. Resolution lengths may depend
on the object. Closure under arbitrary ambient admissible subobjects is a
stronger condition, derived in the length-one case rather than assumed in the
general theorem.

## Public theorem module

Import `Quillen.Resolution.Theorem`.

For a small category `C`, its genuine exact structure `E`, and an object property
`P` containing zero and closed under isomorphisms, extensions, and kernels of
admissible epimorphisms, the hypothesis

`E.ResolutionHypothesis P`

is exactly the existence of an actual `E.FiniteResolution P X` for each `X`.
No common finite bound is required. The interface also takes finite-product
closure; this is already derived from extension closure and zero by
`E.extensionClosed_finiteProducts P`.

The completed endpoints are:

- `Resolution.classifyingHomotopyEquiv E P h`: actual homotopy equivalence
  between the inherited exact subcategory's Q-classifying space and the
  ambient Q-classifying space.
- `Resolution.classifyingHomotopyEquiv_toFun`: its forward map is exactly
  the realized Q-functor of the original exact inclusion.
- `Resolution.inclusionKMap_bijective E P h n`: bijectivity of the original
  zero-normalized inclusion K-map, for every nonnegative degree.
- `Resolution.KEquiv E P h n` and `Resolution.KEquiv_toMonoidHom`: the
  resulting group equivalence retains that same canonical homomorphism.

## Proof decomposition

1. `Finite` and `Transport` retain finite towers of actual conflations, their
   admissible kernels, middle terms, augmentation maps, and final resolving
   syzygy. Exact functors and isomorphisms transport those towers.
2. `Closure` derives ambient admissible-subobject closure in the length-one
   case by a genuine pullback comparison.
3. `QCalculus`, `Covers`, and `FullQ` construct the admissible-cover category,
   its pullback contraction, and its adjunction to the structured comma of
   the full ambient Q-subcategory on resolving objects. Dual Theorem A applies.
4. `InheritedQ` treats the inherited Q-construction separately. Its
   costructured comma reflects onto admissible subobjects, whose zero
   subobject is initial. No false fullness claim about the Q-inclusion is used.
5. `LengthOne` combines those two Theorem A equivalences and preserves the
   original forward maps, including their canonical zero normalization.
6. `Presentation` and `Strata` prove simultaneous extension and kernel closure
   of all finite-resolution-length strata. Kernel comparison and the kernel
   sequences of composite deflations replace any unsupported projective
   lifting assumption.
7. `SubcategoryComparison` and `Bounded` identify nested inherited categories
   by genuine exact equivalences and iterate the actual length-one comparisons.
   All ordered stratum transitions are actual homotopy equivalences with the
   precise canonical forward maps.
8. `Union` constructs the filtered Q-category diagram. Each ambient Q-arrow
   lifts by bounding five actual finite resolutions: source, target, apex,
   left kernel, and right cokernel. Faithful legs and object injectivity give
   a genuine filtered nerve colimit. The existing proved filtered realization
   theorem then supplies the stage-to-ambient homotopy equivalences.
9. `Theorem` combines the zero stratum with this filtered union and supplies
   the unbounded finite-resolution endpoints above.

No resolution input contains K-equivalence, inverse-map, homotopy-equivalence,
or comma-contractibility fields. This theorem does not by itself prove that
an arbitrary regular scheme has the vector-bundle resolution property; those
geometric hypotheses are handled separately by genuine resolution constructions.

## Verification and review boundary

All fourteen canonical modules were checked with Lean 4.34.0 and the pinned
mathlib checkout. The final theorem and the canonical forward-map identities
passed kernel checking. The all-module-origin dependency audit is
`audits/ResolutionFullAudit.lean`, with output in
`logs/resolution-full-all-axioms.log`; it admits only `propext`,
`Classical.choice`, and `Quot.sound`.

The frozen source fingerprints are in `logs/resolution-full-source-sha256.txt`.
This is the proof author's implementation and verification record. The separate
length-one independent review remains valid for its stated scope; independent
review of the full extension and integration into public facades are owned by
the integration reviewer.
