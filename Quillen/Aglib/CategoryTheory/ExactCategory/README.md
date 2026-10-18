# Exact-category constructions

[Product](Product.lean) provides `CategoryTheory.ExactCategory.ExactStructure.prod`
for two preadditive categories with finite biproducts and specified exact structures.
Its conflations are tested by both ordinary projections. Its admissible maps are
exactly pairs of admissible maps; no abelian hypothesis is required.

The same leaf supplies the componentwise additive and limit constructions for
ordinary binary product categories. `fstExact`, `sndExact`, `ExactFunctor.pair`,
`ExactFunctor.zero`, `inlExact`, and `inrExact` retain the actual projection,
pairing, chosen-zero, and insertion functors. The four insertion/projection
composition equations are literal exact-functor equalities.

The intended upstream module is `Aglib.CategoryTheory.ExactCategory.Product`.
Its current consumer is
[the original-map K-theory product comparison](../../../KTheory/FiniteSupport/FiniteProduct.lean).
