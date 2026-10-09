# Actual cylinder cofibrations in inherited subcategories

The actual ambient cokernel of an inherited admissible monomorphism belongs
to the subcategory: this follows from the unique isomorphism between its
specified conflation cokernel and the chosen ambient cokernel. It does not
assert closure under arbitrary cokernels, and the lemma applies to general
exact categories with only that particular ambient cokernel available.

For actual cone- and shift-closed complex subcategories, the original joint
endpoints of the mapping-cylinder factorization form an inherited split
cofibration. The genuine relative endpoint map has quotient equal to the
shifted actual source cokernel, so the inherited-admissibility lemma and shift
closure prove its membership and its split-cofibration property. The map on
sources is required to be a split cofibration; no corresponding assumption
on the map on targets is needed for this relative statement.

Both implementation sources passed warning-free checks and a fixed11-origin
standard-axiom audit with exact-forward-map consumers. Independent fresh
review and stronger arbitrary-universe consumers also passed; see
`REVIEW_20261009_CYLINDER_SUBCATEGORY.md`.

Strict zero normalization, a full fibration theorem, and Gillet–Waldhausen are
not conclusions of these modules. The separate zero-source endpoint module
is under review and is not included in this acceptance boundary.
