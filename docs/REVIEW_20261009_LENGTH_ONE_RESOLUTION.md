# Independent review: length-one Quillen resolution

Reviewed 2026-10-09 by the integration reviewer, separately from the proof author.

## Mathematical contract

The ambient category is small, preadditive, with finite biproducts and the project's genuine Quillen exact structure. The resolving class contains zero, is replete, is closed under finite products, extensions, and kernels of admissible epimorphisms between its objects. Every ambient object has an actual admissible resolution of length at most one. The conclusion concerns the inherited full exact subcategory and its original exact inclusion, in every nonnegative degree.

The resolution hypothesis stores actual conflations and intermediate syzygies. It contains no K-equivalence, comma contractibility, or inverse-map field. The zero-length case is genuinely class membership, and the length-one bound forces the first syzygy to lie in the class.

## Proof inspected

1. A pullback comparison of the resolution of a quotient with an admissible subobject sequence derives closure under all admissible subobjects of resolving objects.
2. The cover category uses genuine admissible epimorphisms and admissible comparison maps. Pullback against a chosen cover constructs a functor and two natural transformations contracting its classifying space.
3. The full ambient Q-subcategory is not confused with the inherited Q-construction. A span-apex universal property gives an actual adjunction for its structured comma, then dual Theorem A applies.
4. The inherited-Q comparison separately reflects its costructured comma onto a category of admissible subobjects with initial zero. Internal inflation and deflation conditions are proved, rather than inferred from mere fullness.
5. The composite forward Q-map is proved to equal the original inclusion. The zero-object natural isomorphism then identifies the normalized map used by the canonical K-map. The group equivalence retains that exact homomorphism.

No mathematical correctness blocker was found in these seven modules. This review does not promote the still-unproved arbitrary finite-length resolution theorem, or any geometric regularity-to-resolution claim.

Full declaration dependency audit evidence: `logs/resolution-independent-all-axioms.log`. The proof author's endpoint audit and source contract remain in `docs/resolution-contract.md` and `logs/resolution-axioms.log`.
