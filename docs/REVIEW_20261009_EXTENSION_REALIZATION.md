# Independent review: extension-category realization equivalence

Date: 2026-10-09. Result: **accepted for the frozen five-source endpoint**.
No production source was changed.

## Accepted endpoint and exact scope

For `C : Type u`, `[Category.{u} C]`, and an arbitrary genuine Waldhausen
structure `W`, `ExtensionCategory.realizationHomotopyEquiv W` is a proved
unbased homotopy equivalence from the actual diagonal S-realization of
cofibration arrows with the Reedy Waldhausen structure to the actual diagonal
S-realization of the componentwise product Waldhausen category `C × C`.

The forward map is **definitionally the original**
`(deloopingMap (sourceCofiber_exact W)).hom`. Its simplicial map literally
postcomposes by the functor taking an extension to its original source and its
actual categorical cofiber. The inverse is `splitRealizationMap W`, induced by
the literal split extension `(A,C) ↦ (A → C ⨿ A)` using coproducts constructed
from the Waldhausen axioms. No inverse map or inverse homotopy is an input.

The categorical layers retain independent object and hom universes. The final
realization theorem honestly requires the common-universe case: cofibration
arrow objects have universe `max u v`, so setting the hom universe to `u`
aligns the existing raw S-map interfaces. This is not a cross-universe
realization assertion.

## Semantic verification

I read all five implementation sources completely and checked their use of
the previously accepted eight extension-category prerequisites, the actual
functor-additivity theorem, and the genuine weak-natural-transformation
realization homotopy.

### Product and structural exactness

`Product.lean` proves both directions of the componentwise pushout statement
by explicit universal properties. Projection preservation uses the other
component of the given pushout as the auxiliary cocone component, and does not
assume terminal objects or global colimits. The componentwise zero, cofibration,
weak-equivalence, pushout, and gluing axioms then construct the product
Waldhausen structure. Source/cofiber pairing is genuinely exact from the
already proved source and cofiber exactness.

`ExactTransport.lean` transfers all four structural exactness conditions across
an actual natural isomorphism with independent source/target universe pairs.
It conjugates actual cofibration/weak arrows and transports the actual pushout
square; there is no K-theoretic premise.

### Literal splitting and actual quotient

`Split.lean` defines the split extension by the literal coproduct inclusion
`A → C ⨿ A`, with the original source map and coproduct map on morphisms.
Its universal property proves that it is the actual coproduct in the extension
category of the zero-source and identity-source embeddings. Exactness follows
from exactness of the true sum of these embeddings and transport through the
proved natural isomorphism.

`SplitQuotient.lean` identifies the actual cofiber of this split extension with
`C` by the unique pushout isomorphism. The quotient projection formula proves
naturality, and together with the literal source formula gives
`split ⋙ sourceCofiber ≅ identity` on the actual product category.

### The two genuine inverse homotopies

The original S-map and realization-map identity/composition laws are proved
strictly. Actual natural isomorphisms induce homotopies of those original maps
through the proved weak-transformation cylinder.

For the composite on extensions, the internal structural sequence
`(A→A) → (A→B) → (0→B/A)` gives the genuine functor-additivity homotopy from
the identity to the sum of its quotient and subobject functors. The actual
sum-to-split natural isomorphism then identifies the latter map with
source/cofiber followed by splitting. This does **not** assume original
extensions split, nor claim a categorical splitting of arbitrary extensions.

For the reverse composite, the actual natural identification of split
source/cofibers with the original pair gives the inverse homotopy directly.
The resulting `ContinuousMap.HomotopyEquiv` uses these two proved homotopies,
and its forward/inverse formulas are retained by `rfl`.

There is no additivity conclusion, equivalence, inverse homotopy, or desired
commuting square hidden in the hypotheses. The only additivity input is the
previously proved unconditional theorem applied to the actually constructed
internal structural sequence.

## Independent Lean verification

The five selected modules were rebuilt from the frozen sources in dependency
order into a new isolated overlay. The eight extension-category prerequisites
in that overlay point to the fresh artifacts from my preceding independent
core6/internal2 rebuilds. Other unchanged dependencies are linked. The five
reviewed artifacts are fresh regular files; no production olean was replaced.

Compilation used Lean 4.34.0, `-j1`, and the shared slot1 lock with acquisition
logged. All five source checks and the final audit are warning-free.
`lean --deps` confirms the final module selects the isolated `SplitQuotient`
artifact; the audit imports the fresh final module through the same overlay.

`audits/ExtensionRealizationIndependentAudit.lean` runs a fixed **81-origin**
audit including every private/generated declaration of the five modules.
Recursive `collectAxioms` permits only `propext`, `Classical.choice`, and
`Quot.sound`. All 81 pass.

Consumers verify arbitrary categorical universes, exact product classes,
structural exactness, the literal split/source/cofiber functor formulas, the
actual coproduct universal property and quotient formula, and the exact
common-universe realization endpoint. Additional independent consumers check
unconditional projection pushout preservation, the actual source/cofiber map
formula, literal simplicial postcomposition, and both inverse homotopies with
the specified forward and split maps.

All five new source hashes and all eight prerequisite source hashes matched
after checking. No source repair was required.

## Limits

The target is the realization of the actual product-category S-construction.
No identification with a product of two realized spaces is asserted or used.
The result is unbased: this boundary does not assert fixed-zero inverse
homotopies, canonical based K-map naturality, a product decomposition of
K-groups, or a fibration/Gillet–Waldhausen theorem. The stated common-universe
restriction is part of the accepted final theorem.

## Frozen sources and evidence

Manifest: `logs/extension-realization-independent-20261009/sources.sha256`

Manifest SHA-256:
`4d7a88027604d9933450bb872a1068430ee44beb29b33072c32832adb428b9c0`

- `Product.lean`: `e79309aad5b46471c12c7d517727fadeca6185f93971ca0519f07e8421195809`
- `ExactTransport.lean`: `78b53ad8f35e158939fbe778b021ab60926b3ea1c37c683845be3ef65e79b849`
- `Split.lean`: `518758d871a55563dd2e29ce566920c81f6b72fdb2efb6e66fcba08c2d98d011`
- `SplitQuotient.lean`: `b378267b3b3a3ea5e5be99f153286b883c1b91c0029f92ec8b66c39925750bc1`
- `Realization.lean`: `ce7da5dd788cccc9482a1ce8a475ed3053961b63edc0ad2e762a8e2ba5cc11c1`

Evidence directory: `logs/extension-realization-independent-20261009/`

- `check.log`: ordered fresh source rebuild
- `audit.log`: fixed81 recursive origin audit and strengthened consumers
- `deps.log`: selected dependency paths
- `hashes-before.log`, `hashes-after.log`, `core8-hashes-after.log`: rechecks
- `artifacts.sha256`: independent audit, report, logs and five fresh oleans

Independent audit SHA-256:
`1363923226efd41173b788837f034dfa575c86d88f0f88e099598ca5650965f8`

Audit log SHA-256:
`65bdef3710058490dc818c05c9445768f4bfd7d6bec9b3a085cbd68b67392958`
