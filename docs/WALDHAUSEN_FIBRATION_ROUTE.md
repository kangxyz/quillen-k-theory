# Route to the nested-weak-equivalence fibration theorem

## Recommended endpoint and scope

Start with one category `C : Type u`, `[Category.{u} C]`, a fixed cofibration class and chosen zero, and two genuine Waldhausen weak-equivalence structures `v ≤ w`. Sharing the cofibration/zero data avoids artificial equality transports. Let `C^w` be the actual full subcategory on objects for which `0 → X` belongs to `w`, carrying the inherited cofibrations and **v**-equivalences.

The first topological endpoint should be the canonical comparison

`|v S(C^w)| → HomotopyFiber (|v S C| → |w S C|) zero`.

Construct its path coordinate from the actual weak natural transformation `zero → inclusion`, reversed to match the repository's fiber-path convention. Prove bijectivity on all finite based homotopy sets, including degree zero, before upgrading to an actual continuous homotopy equivalence. The existing general Theorem B endpoint gives precisely such weak conclusions; it is not an automatic continuous inverse theorem. Retain the original inclusion/change-of-weak-equivalence maps and subsequently identify their normalized K-maps.

The common universe restriction is deliberate. Larger-category/small-model transport is a separate step, not a raw cross-universe realization identification.

## Structural inputs, without a homotopical conclusion

The classical localization hypothesis is a common cylinder for the two weak classes, its projection axiom for `w`, and saturation plus the extension axiom for `w`. See [Thomason–Trobaugh, 1.8.1–1.8.2](https://gwern.net/doc/math/1990-thomason.pdf). In repository terms:

- Both classes satisfy the actual `Structure` axioms with the same cofibrations; `v ≤ w`.
- `w.HasTwoOutOfThreeProperty`.
- `Fibration.ExtensionAxiom W`: a commuting map of actual cofiber pushout squares with weak source and quotient maps has weak middle map.
- A functor `T : Arrow C ⥤ C`, natural source/target inclusions and projection, factorization/section identities, joint-endpoint cofibrations, relative joint-endpoint cofibrations on cofibration squares, and preservation of pointwise `v` and `w` weak squares.
- For the direct pointwise quotient-row extension route, use genuine exactness of the joint-endpoint functor from the **pointwise** arrow Waldhausen structure to the **Reedy** extension structure, for both weak classes. This includes actual pushout preservation, beyond the displayed relative-cofibration condition. Alternatively, build row cylinders by successive pushouts and prove the quotient-row axioms separately. The raw factorization package supplies neither argument automatically. The new `Fibration/Rows/JointFactorization` module now proves the first route from actual exact base joint data; its fresh independent rebuild and fixed72 boundary audit have passed.
- The projections `T(f) → target(f)` belong to `w`. Do **not** require them to belong to `v`.
- A coherent zero-source projection isomorphism is enough for an iso-tolerant implementation. If a later simplicial definition requires literal chosen-zero equalities, normalize the functor and prove agreement; an existing isomorphism is not a literal equality.

Current `FunctorialFactorization` is weaker than this cylinder contract: it has no target section, joint/relative condition, preservation of `v` squares, or structural pushout-preservation field. The actual complex joint-cylinder functor is independently accepted; its concrete quotient-row factorization assembly is now independently accepted. For `v = isomorphisms`, preservation by any functor is immediate; for a general nested class it is a real condition.

`Structure` contains gluing, not the extension axiom. This structural gap is now discharged for actual complexes and inherited complex subcategories: `Quillen/Algebra/Homology/QuasiIsoExtension.lean` proves `quasiIso_middle_of_shortExact` from the actual neighboring long exact sequences and both four lemmas, and `Quillen/Waldhausen/Fibration/ComplexExtension.lean` proves `complexes_extensionAxiom` and `complexSubcategory_extensionAxiom` from actual cofiber squares. Both modules and the actual acyclic subcategory have passed independent review and belong to the immutable 07:00 boundary. This uses no assumed extension theorem and no nonexistent mathlib middle-map lemma.

Live progress as of 2026-10-09 09:38 UTC: the generic quotient-row/pointwise-arrow boundary, exact postcomposition, and actual pointwise/Reedy row-arrow interchanges are independently accepted (fixed96, fixed27, and fixed139 origin audits respectively). The concrete joint-cylinder functor is independently accepted for both isomorphism and quasi-isomorphism weak models. The actual relative rows, inherited fine structure, all exact ordinal reindexings, original first/tail functors, strict split fiber, and outer-natural S-map bridge are now independently accepted (fixed76, fixed35, and fixed55 boundaries). The actual cutoff/Reedy-arrow exactness and first-object identification, genuine cofiber/product section, and degreewise relative additivity are now independently accepted (fixed77, fixed26, and fixed24 boundaries). The first/tail realization map is a genuine homotopy equivalence with its exact original forward map; the original constant-path local fiber inclusion is bijective in all finite homotopy dimensions, including zero. The canonical global relative-realization homotopy-fiber theorem remains open. Accepted local product-fiber, compact lifting, and Cartesian detection results do not by themselves supply that global step.

Post-checkpoint structural progress as of 2026-10-09 10:49 UTC: original
initial-filtration weak-map detection and full faithfulness, the same-type
coarse quotient-row Waldhausen structure, and generic zero-augmented cofiber
completion are independently accepted. The original filtration/completion
categorical equivalence and its restriction to actual fine-weak morphisms
are independently accepted (fresh2, fixed59, 28 consumers). The actual row-cylinder
factorization, with genuine Reedy inclusion and original pointwise coarse
projection, is independently accepted (fresh2, fixed72, 30 consumers). The
separate row extension-axiom transport is also independently accepted
(fresh1, fixed2, 10 consumers), including actual iterated row categories.
These results supply concrete inputs for the mixed comparison. The coarse
cylinder projection is not a morphism in the fine-weak category in general,
so it does not by itself prove a fine-nerve equivalence in each outer degree.
The mixed comparison and the canonical global relative-realization fiber
lemma remain separate open obligations.


## Actual relative S-model

For the inclusion `C^w → C`, use a direct model `R_n` of quotient rows in `S_(n+1) C` whose tail quotients `A_(i,j)` are acyclic for `1 ≤ i ≤ j ≤ n+1`. The first row is a chain `A_(0,1) → ... → A_(0,n+1)` with arbitrary starting object. Reindex by the ordinal extension of `α` that fixes the new initial vertex and sends `i+1` to `α(i)+1`.

This is a concrete presentation of the usual relative S-construction. For a general exact functor `F : B → C`, that construction has rows of `B` and one-longer rows of `C`, identifying `F` of the former with the latter's tail quotient row. See [Weibel, IV.8.5.3](https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.IV.pdf). The special inclusion model avoids imposing strict equality on independently chosen quotient objects.

Implementation obligations:

1. **Completed and independently accepted:** the inherited `v`-Waldhausen category on `C^w`, with actual zero, repleteness, pushouts, quotient closure and exact inclusion, is implemented in `Fibration/AcyclicSubcategory.lean`.
2. **Completed and independently accepted:** `SConstruction/Rows` constructs the generic quotient-row Waldhausen categories with all natural transformations, pointwise weak maps, and the all-triples genuine Reedy cofibration condition. Component cofibrations follow from degenerate intervals; pushouts, quotient interchange, gluing and every ordinal restriction are proved. `GridBridge.lean` identifies these predicates with the original `bisimplicialSSet` grid predicates. Exact postcomposition by genuine exact functors is separately proved and independently accepted in two modules; `Approximation.WeakRow` is not used as a substitute for this generic construction.
3. **Structural part completed and independently accepted:** `R_n`, its actual fine structure, all ordinal reindexings, and the exact source `A_(0,1)` and acyclic-tail functors are implemented in `Fibration/RelativeRows`. The actual cutoff/identity/tail cofibration sequence, coproduct section, and degreewise relative-additivity comparison into the **actual product category** `C × S_n(C^w)` are now independently accepted. Its forward map is the original first/tail functor; the genuine product-S simplicial isomorphism yields the required simplicial-product realization endpoint.
4. **Completed and independently accepted:** `RelativeRows/FiltrationEquivalence` identifies `R_n` with the genuine full subcategory of original coarse-weak cofibration chains. The inverse is actual zero-augmented cofiber completion. `FiltrationWeakEquivalence` restricts this equivalence to the original fine-weak morphism categories, with the original forward and inverse classifying-space maps. The coarse extension axiom is used to recognize original relative filtrations as coarse-weak; completion itself needs neither extension nor saturation.

## Comparison and fiber obligations

Use independent directions: an S-degree, a nerve direction of `v` maps, and a direction of `w` maps. Replace the latter by genuine `w`-trivial cofibrations through the common cylinder. This replacement must preserve the `v` direction and genuine row cofibrations, including all quotient maps. Existing finite replacement plus `w`-saturation alone does **not** prove preservation of `v`-maps. Forgetting/reintroducing quotient choices must be an actual equivalence or a proved contractible-comma comparison.

The classical proof compares this mixed grid with the relative S-model, then uses relative additivity to identify the fiber. [Weibel, V.1.7 and V.2.1](https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.V.pdf) provide this organization. The repository still needs the corresponding canonical **relative-realization fiber lemma**. It cannot be inferred from degreewise equivalences alone.

Concrete reuse points:

- `TheoremA.contractibleCommaClassifyingHomotopyEquiv` for quotient-choice and cylinder comparison functors, after constructing their actual comma contractions.
- Generic `BisimplicialRealization.diagonalRealizationHomotopyEquiv` repeatedly for the verified multi-direction equivalence comparisons.
- `TheoremB.vertexFiberComparison_bijective_of_transitions`, or its categorical counterpart `fiberComparison_bijective`, only after a genuine replacement/Grothendieck presentation is constructed and every actual transition equivalence is **proved** from relative additivity. Generic Grothendieck-to-diagonal and presentation compatibility are not supplied merely by the current comma-specific Grothendieck module.
- Theorem B's finite cartesian skeletal and sequential compactness proofs are the starting point if proving the specialized relative-realization fiber lemma directly is shorter than constructing that presentation.
- The identity relative S-model has an actual extra-degeneracy contraction. Its compatibility identifies the connecting map with the original exact inclusion, rather than an unrelated map.

Do not import an arbitrary ordinary-TopCat product homeomorphism: `ProductSimplex`/`MapEquivalence` currently establish the comparison with a locally compact factor. The relative argument either needs a separately proved product weak-comparison/connected-base realization theorem, or a categorical/replacement proof that avoids that assertion. There is also no available general topological Whitehead upgrade that can be inserted without proof.

## First concrete file

`Quillen/Waldhausen/Fibration/WeakEquivalenceCofiber.lean` defines the structural extension axiom on displayed cofiber squares and `Acyclic W X := W.weq (W.isZero.to_ X)`. It proves:

- genuine zero objects are acyclic;
- `weak_iff_acyclic_of_isPushout` for an actual cofibration and any displayed cofiber pushout;
- `cofiber_acyclic_iff` for the existing actual `ExtensionCategory.cofiber` functor.

The forward implication is gluing against the identity cofiber sequence. The reverse implication is precisely the structural extension axiom applied to that same genuine sequence. Neither saturation nor a cylinder is needed here. This is an independently checkable first layer, not a fibration theorem packaged as an assumption.

Recommended order after it: acyclic subcategory; generic quotient-row structures; relative rows and relative additivity; common-cylinder mixed-grid comparison; separately proved relative-realization fiber lemma; exact canonical fiber/K-map assembly. The fiber-realization lemma remains the largest topology obligation.
