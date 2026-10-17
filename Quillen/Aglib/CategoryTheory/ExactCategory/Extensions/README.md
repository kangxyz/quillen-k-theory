# Admissible extensions

`Basic` represents an extension with fixed quotient by its actual admissible
epimorphism and uses its categorical core for isomorphisms. Kernel data and
the zero-quotient equivalence come from the specified exact structure.

`Pullback` uses only pullbacks of admissible epimorphisms, without assuming
ambient finite limits. `Product` gives the original fixed-quotient pullback
product and its diagonal. `ProductKernel` identifies its actual kernel with
the biproduct of the two supplied kernels. Q-span transport and Grayson
total-extension projections remain downstream.
