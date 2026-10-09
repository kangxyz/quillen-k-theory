# Actual relative complex cylinder quotient

Two leaf modules prove the quotient needed for the genuine joint-endpoint
cylinder map. They are post-05:00 work, outside the delivered archive.

`RelativeQuotient.lean` proves a categorical cokernel lemma from two actual
cokernel universal properties and the epimorphic source quotient. It does
not assume the desired cokernel property for the relative middle map.

`ComplexQuotient.lean` applies it to the original functorial complex cylinder.
For a map of arrows alpha and the actual relative endpoint pushout, the
relative map k has quotient exactly the shifted actual cokernel of alpha.left.
The projection is the original joint projection followed by the shifted
cokernel projection. Its zero composite is derived by pushout extensionality.
The cokernel universal property is proved via the joint short exact sequence
and preservation of cokernels by the shift. If alpha.left is degreewise split
monic, the resulting displayed sequence is genuinely short exact. No split
condition on alpha.right is needed for this particular relative inclusion.

This does not assert subcategory membership, chosen-zero normalization, a full
Waldhausen cylinder structure, fibration, or Gillet–Waldhausen. Those require
additional theorems. Both modules compiled warning-free; all 25 recursive
source-origin declarations and arbitrary-universe exact-formula consumers
pass the three-standard-axiom audit. Independent review passed; see `REVIEW_20261009_CYLINDER_QUOTIENT.md`.

Evidence: `logs/cylinder-quotient-sources.sha256`,
`audits/CylinderQuotientAudit.lean`, `logs/cylinder-quotient-audit.log`.
