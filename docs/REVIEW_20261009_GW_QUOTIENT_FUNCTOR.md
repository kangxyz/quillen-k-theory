# Independent review: exact acyclic truncation quotient

Accepted 2026-10-09 05:30 UTC. The new `QuotientExact.lean` extends the
seven previously reviewed Gillet–Waldhausen algebra modules to eight.

The actual categorical cokernel maps define the quotient functor and its
natural projection. Cancellation against the genuine quotient epimorphism
proves additivity. The previous boundary isomorphism to next cycles is shown
to respect that quotient projection and to be natural on exact complexes.
Degreewise exactness then uses zero terms below the boundary, exact cycles at
the boundary and the original terms above it.

`boundedAcyclicQuotientExactFunctor` is an actual exact functor under the
structural replete/zero/extension/kernel-closure conditions on P. Its underlying
functor is definitionally the third projection of the original truncation
sequence. No exactness, relative-cofibration or K-equivalence conclusion is
supplied as an input.

The new source was read in full and independently recompiled warning/error-free
against the isolated artifacts used in the preceding independent review. All
eight source hashes matched before and after. The fixed164-origin recursive
audit and arbitrary-universe exact-functor, unchanged-projection and scheme
consumers passed with only standard Lean logical foundations.

Evidence: `audits/GilletWaldhausenQuotientIndependentAudit.lean`,
`logs/gw-quotient-independent-{check,audit,hashes}.log` and
`logs/gw-quotient-independent-sources.sha256`, manifest SHA-256
`e2eedd2a4c81889df0c1efd3eb9913582d0809b75e2250087e41c07b68fefb0d`.

Relative cofibration of the truncation transformation, disk-layer identification,
additivity, fibration and Gillet–Waldhausen remain separate. This source is
outside the frozen 05:00 archive.
