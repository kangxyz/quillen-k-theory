# Independent acceptance: original brutal truncations and term-filtration sequence

Accepted 2026-10-09 06:58 UTC after complete source inspection, fresh isolated
rebuilds of the four new files, fixed recursive origin audits, actual-map
consumers and before/after source hashes. All final checks are warning-free.

The raw three-file layer reuses mathlib's actual restriction/extension
stupid-truncation complex and functor. It supplies the original inclusion,
natural nested-cutoff maps with strict identity/composition, and the actual
adjacent sequence trunc≥(n+1) K → trunc≥n K → single_n(K^n). The sequence is
short exact and has genuine degreewise splittings. Its actual chosen cokernel
is identified with that original single complex with the original quotient
projection unchanged. This raw result holds for all cochain complexes in an
abelian category, with no boundedness, projectivity or acyclicity hypothesis.

The fourth file proves exactness of the original brutal and single-term
functors, then restricts them to actual bounded termwise-P complexes. It needs
P to contain zero and be replete/extension-closed, not kernel-closed. Actual
relative cofibrations are derived from exactness of the quotient functor,
yielding the original adjacent IsCofibrationSequence in the isomorphism model.
Brutal truncation is not incorrectly asserted to preserve quasi-isomorphisms.

The raw independent audit checks all 534 origins across the 24-source GW
boundary. The final exact-wrapper audit checks all 574 origins across 25
sources, including private/generated helpers. Both allow only propext,
Classical.choice and Quot.sound. Consumers retain the original mathlib functor,
all actual inclusion/quotient maps, the genuine chosen-cokernel projection,
and the canonical based KMap additivity equality without kernel closure.

Fresh artifacts are in `/tmp/quillen-brutal-independent-0652`, first in
LEAN_PATH. Evidence: `logs/gw-brutal-independent-*`,
`logs/gw-brutal-exact-independent-*`,
`audits/GilletWaldhausenBrutalIndependentAudit.lean`, and
`audits/GilletWaldhausenBrutalExactIndependentAudit.lean`.
The pinned mathlib StupidTrunc source was unchanged and separately rehashed;
only its previously absent build artifact was produced.

This gives genuine term-filtration layers, not yet the global graded K-theory
decomposition or Gillet–Waldhausen equivalence. Fixed-stratum endpoint and
change-of-weak-equivalence fibration assembly remain separate proof obligations.
