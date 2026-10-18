# Fibers and cocartesian sections

The strict-section and cocartesian-section categories retain the actual base
functor and literal index restriction. Their maps and evaluation equations use
the original vertical arrows and the strong cocartesian universal property.

For a Cat-valued pseudofunctor, the `Grothendieck` files identify its actual
fiber, construct its original cocartesian lifts and sections, and prove the
evaluation equivalence. Composition, pseudonatural maps, coslice restriction
and normalization retain the original unit/composition comparisons. Zero
sections require the stated transition-preserved chosen fiber zeros.

The `IsoFiber` files retain specified structure isomorphisms. Their comma
comparisons require the displayed cartesian lifts; `CocartesianComma` treats
the strict-fiber version with cocartesian lifts. None of these interfaces
asserts a topological fiber theorem.

## Change of index

[SectionChangeIndex](SectionChangeIndex.lean) constructs actual restriction along an
arbitrary functor `K : C ⥤ D` for a Cat-valued pseudofunctor on `D`.
The restricted cocartesian section uses `Under.post K`, the original vertical
arrows and their cocartesian transitions. It does not require `K` to be
cofinal, fully faithful or essentially surjective.
[SectionChangeIndexLaws](SectionChangeIndexLaws.lean) gives literal evaluation and
reindexing equations, together with `restriction_isEquivalence` for these
section categories at every `K`. [SectionChangeIndexZero](SectionChangeIndexZero.lean) preserves
the same global chosen-zero family, assuming each transition carries the
chosen fiber zero to a zero object.
[SectionChangeIndexUnit](SectionChangeIndexUnit.lean) preserves identity actions lifted
through that actual evaluation. These declarations use the native namespace
`CategoryTheory.SectionChangeIndex`.

Waldhausen adapters live in
[SectionChangeIndexModel](../../../Waldhausen/SConstruction/Iterated/SectionChangeIndexModel.lean),
[SectionChangeIndexLargeModel](../../../Waldhausen/SConstruction/Iterated/SectionChangeIndexLargeModel.lean) and
[SectionChangeIndexMixedModel](../../../Waldhausen/SConstruction/Iterated/SectionChangeIndexMixedModel.lean). They transport the given
fiber cofibrations and weak equivalences along the original evaluation
equivalence, retain the chosen section zero, and require exact transition
functors for a Model diagram. Both restriction and its categorical inverse are
exact. The forward restriction is a literal zero-preserving Model map; a
strictly zero-preserving inverse Model map is not assumed.
The small adapter's declarations use
`Quillen.Waldhausen.IteratedS.SectionChangeIndex`; the large and mixed adapters
use the respective `SectionChangeIndexLargeModel` and
`SectionChangeIndexMixedModel` namespaces under `Quillen.Waldhausen.IteratedS`.

The small adapter uses `C,D : Type u` with small categories and
`Cat.{u,u}` fibers, producing `Model.{u}`. For index morphisms in universe
`v`, the large adapter uses `Cat.{max u v,max u v}` and produces
`Model.{max u v}`. The mixed adapter uses `Cat.{w,max u v w}` and produces
`Model.{max u v w}`. These bounds are part of the interfaces.
[SectionChangeIndexStable](../../../KTheory/Bass/SectionChangeIndexStable.lean) applies the small adapter to
actual finite Bass stages. The geometric global application and its larger
section categories remain in the perfect-complex owners.

## Global sections and finite Bass interchange

| Import after `Quillen.` | Principal interface |
| --- | --- |
| `Aglib.CategoryTheory.FiberedCategory.SectionChangeIndex`, `SectionChangeIndexLaws`, `SectionChangeIndexZero`, `SectionChangeIndexUnit` | `CategoryTheory.SectionChangeIndex.underFunctor`, literal evaluation/reindexing, same chosen zero and lifted identity actions |
