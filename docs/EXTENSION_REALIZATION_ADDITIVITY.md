# Extension-category additivity on realization

## Mathematical endpoint

`Quillen.Waldhausen.ExtensionCategory.realizationHomotopyEquiv W` compares

- the actual diagonal S-realization of the category of cofibration arrows, with its proved Reedy Waldhausen structure; and
- the actual diagonal S-realization of the componentwise product Waldhausen category `C × C`.

Its forward map is definitionally `deloopingMap (sourceCofiber_exact W)`, where the functor sends an extension to its original source and its actual cofiber. The inverse is induced by the literal split extension `(A,C) ↦ (A → C ⨿ A)`.

The realization endpoint is in the common-universe case `C : Type u`, `[Category.{u} C]`. This is required by the existing raw S-map interface: cofibration-arrow objects have universe `max u v`. The categorical constructions and exactness results retain independent object and hom universes. There is no cross-universe raw realization claim, no assertion that realization preserves arbitrary products, and no based homotopy or K-map naturality claim here.

## Genuine categorical and homotopical construction

1. `Product.lean` proves the product-category pushout universal property and its converse under both projections. These construct every axiom of the componentwise Waldhausen structure, exact projections, and exact pairing. In particular, `sourceCofiber_exact` uses the already proved actual source and cofiber exactness.
2. `ExactTransport.lean` transports structural exactness across an actual natural isomorphism with independent source and target universes. Cofibrations and weak equivalences are transported by actual isomorphisms; pushouts by the actual isomorphic square.
3. `Split.lean` constructs the literal split extension. Its universal property identifies it with the actual coproduct in the extension category of `(0→C)` and `(A→A)`. Exactness follows from the proved exact sum of the canonical embeddings, transported by this actual natural isomorphism.
4. `SplitQuotient.lean` identifies the actual cofiber of `A → C ⨿ A` with `C` by the unique pushout isomorphism. The exact quotient formula proves its naturality. Together with the literal source formula this gives `split ⋙ sourceCofiber ≅ identity`.
5. `Realization.lean` proves strict identity/composition laws for the original S-maps and realization maps. An actual natural isomorphism gives an actual weak-natural-transformation homotopy. The previously proved internal structural sequence `(A→A) → (A→B) → (0→cofiber)` and genuine functor additivity give the other inverse homotopy. These two homotopies assemble the equivalence with the exact original forward map.

No additivity conclusion, inverse homotopy, row equivalence, or desired commutative square is assumed in these modules.

## Verification artifacts

The five sources are listed in `logs/extension-realization-sources.sha256`. Ordered focused checks are recorded in `logs/extension-realization-final-*.log`. `audits/ExtensionRealizationAudit.lean` recursively audits all 81 declaration origins in the five sources and also checks actual functor formulas, genuine structural exactness, the split cofiber quotient formula, arbitrary categorical universes, and the exact common-universe realization forward map. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted as foundational axioms. All five final focused checks passed without warnings, the fixed-count audit and exact-map consumers passed, and source hashes were rechecked successfully. Final artifact and source rechecks are recorded beside the manifest.

This scope is separate from the eight previously frozen extension structure/internal-sequence sources and from the immutable 06:10 checkpoint.
