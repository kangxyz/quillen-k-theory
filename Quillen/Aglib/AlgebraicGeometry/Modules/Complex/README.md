# Ordinary scheme-module complex operations

These local general candidates reuse the pinned Aglib native cochain-complex interfaces.
They provide actual extension by zero and base change, injective open models, pushforward
comparisons, quasicoherent-homology and unit-cone operations, homology cover detection,
restriction bounds, single/cycle maps, and mapping-cone naturality. All-sheaf targets, exact
term/cohomology bounds, lower-bounded injectivity, and compact/affine assumptions remain only
where present on the original statements.

QuasiIsoOnBasis detects actual sheaf-complex quasi-isomorphisms on a topological basis,
including principal affine opens. Affine/ holds the actual associated-sections/counit and
localization/reconstruction operations; OpenGluing/ holds the literal homotopy gluing maps.
BoundedQuasicoherentModels retains the original affine/two-affine cover and finite-bound input.
Derived functors and Hom interfaces have their own Modules/DerivedCategory owner.
