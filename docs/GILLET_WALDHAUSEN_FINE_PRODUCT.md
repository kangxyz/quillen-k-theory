# Actual fine product decomposition and coarse projection

The new module `Waldhausen/GilletWaldhausen/FineProductDecomposition.lean`
packages the proved unique global factorization as
`boundedTermsAcyclicSingleKEquiv P k`.

Its source is the product of the original isomorphism-model K-group of
bounded acyclic termwise-P complexes and the original inherited exact-category
K-group of P. Its target is the original isomorphism-model K-group of bounded
termwise-P complexes. Its forward map is literally the product of the two
original public normalized KMaps: acyclic inclusion and degree-zero single
insertion. The inverse is obtained from the proved bijectivity, not assumed.
All statements include K₀.

The original coarse composite of acyclic inclusion is proved trivial by
transporting the already constructed actual weak-natural-transformation null
composite through the original exact fiber-object identification. This uses
no fibration theorem. Consequently changing weak equivalences after the
actual product equivalence equals the original coarse single KMap after the
second product projection. Coarse surjectivity, coarse injectivity and
fibration exactness are not asserted.

A is abelian with `A : Type (max u v)` and `Category.{v} A`. P contains zero,
is replete and extension-closed. The raw product map and null/coarse formulas
need no kernel closure. The actual product equivalence additionally uses
structural kernel closure through the proved global unique factorization.
Arbitrary schemes specialize through the accepted finite-locally-free
kernel-closure instance; no extra geometric hypothesis is introduced.

The source focused build passed warning-free. The final fixed34 recursive
source-origin audit and all consumers in
`audits/GilletWaldhausenFineProductAudit.lean` passed with no warnings,
errors, or `sorryAx`; only the three standard logical axioms occur.
Consumers check literal forward maps, both inverse identities, actual K₀
embeddings, the inverse coarse-value formula, and the original scheme
`vectorBundleSComparison` on arbitrary schemes.

The frozen source manifest is
`logs/gillet-waldhausen-fine-product-checked-sources.sha256`; the terminal
raw audit is `logs/gillet-waldhausen-fine-product-axioms.log`. This source
and the prior fifty-one frozen source hashes all match in
`logs/gillet-waldhausen-fine-product-prior-hashes.log`. Final artifact hashes
are in `logs/gillet-waldhausen-fine-product-artifacts.sha256`.
Independent review passed; see
`docs/REVIEW_20261009_FINE_PRODUCT_DECOMPOSITION.md`. The frozen single-map triangle and accepted
Euler sources are unchanged.
