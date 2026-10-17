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
