# Abelian families and finite support

This is the canonical implementation owner for the general category-family
construction migrated from R5 revision
`1b7c3945394bcc27a94d1ebf86df702b0291ee18`. The intended upstream modules are
`Aglib.CategoryTheory.Pi.Abelian`, `Aglib.CategoryTheory.Pi.FiniteSupport`, and
`Aglib.CategoryTheory.Pi.FiniteStages`, and
`Aglib.CategoryTheory.Pi.Equivalence`. Public declarations use the native
`CategoryTheory.Pi` namespace. Current consumers are Quillen's finite-product
and finite-support K-theory comparisons.

[Abelian.lean](Abelian.lean) equips the existing dependent product category
`∀ i, C i` with pointwise preadditive, limit, colimit, and abelian structures.
`shortExact_pi_iff` tests a short exact sequence at every actual evaluation
functor. `exactEvaluation C i` bundles that evaluation for the standard
abelian exact structures. The index, object, and hom universes are independent.

[FiniteSupport.lean](FiniteSupport.lean) defines `finiteObjectSupport C` by
finiteness of `{i | ¬ IsZero (M i)}` and `FiniteCategoryFamily C` as its full
subcategory. This is the same object predicate and ambient category as the
supplying R5 candidate. The former R5 application namespaces are replaced by
`CategoryTheory.Pi`; the underlying families, morphisms, and evaluations are
preserved. The property is a Serre class, so existing full-subcategory APIs
supply its canonical abelian structure. `finiteCategoryInclusion` is the exact
literal inclusion and `finiteCategoryEvaluation C i` is exact coordinate
evaluation.

[FiniteStages.lean](FiniteStages.lean) defines `FiniteStage C s` as the full
subcategory of the original product on families zero outside the finite set
`s`. Objects may use arbitrary zero objects outside `s`.
`stageInclusion C h` for `h : s ⊆ t` retains the original family and morphism;
its identity and composition equations are literal functor equalities.
`stageExactInclusion`, `stageExactToFiniteFamily`, and `stageEvaluation` bundle
the corresponding exact functors. Every finite-support family lies in a finite
stage, and every zero family lies in every stage.

`stageProductEquivalence C s` identifies this actual stage with
`∀ j : s, C j.1`. Its forward functor is `stageRestriction`, and its inverse is
`stageZeroExtension`, using the chosen zero object of each coordinate category
off `s`. The unit uses the unique isomorphism between zero objects off support.
`stageExactRestriction` and `stageExactZeroExtension` give the same maps as exact
functors. Restriction, stage inclusion, and evaluation commute by the stated
literal equations. `emptyStageEquivalence` identifies the empty stage with
`Discrete PUnit`, and `emptyStage_isZero` covers every object of that stage.

`finiteFamilyStageObjectProperty C s` presents the same stage inside
`FiniteCategoryFamily C`. The literal nested transitions are
`finiteFamilyStageInclusion` and `finiteFamilyStageExactInclusion`.
`stageNestedEquivalence`, `stageNestedExactFunctor`, and
`stageNestedInverseExactFunctor` compare the two presentations while retaining
the ambient family. Their inclusion and transition equations support filtered
constructions using this nested presentation.

`singletonExactInclusion C i` inserts one coordinate through singleton zero
extension into `FiniteCategoryFamily C`. Its underlying `singletonInclusion`
followed by evaluation at `i` is literally the identity. Evaluation at `j ≠ i`
is literally constant at the chosen zero object of `C j`, by
`singletonInclusion_comp_evaluation_zero`. The natural isomorphism
`singletonInclusionCompEvaluationOfNe` additionally compares it with the
chosen zero object of the functor category.

The Serre, abelian, and exactness results assume each `C i` is abelian. The
index set itself need not be finite. These are categorical foundations; the
Q-construction and K-group comparisons are maintained in their Quillen owners.

[Equivalence.lean](Equivalence.lean) restricts coordinatewise categorical
equivalences to the original finite-support families. `IsZero` preservation
retains the actual support predicate. The original inclusion and evaluations
commute literally, while singleton inclusion has its specified natural
isomorphism. Additive coordinate equivalences give exact directions. The
explicit common-universe SmallModel specialization is used by native
Dedekind primary support; it asserts no cross-universe K-group equality.
