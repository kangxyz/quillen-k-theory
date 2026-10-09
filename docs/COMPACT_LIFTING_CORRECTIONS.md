# Compact-parameter lifting corrections

The five sources under `Topology/HomotopyLifting/Compact` expose the actual
covering-homotopy property only for compact locally compact parameter
spaces. No separation hypothesis is added. Genuine full HLP implies this
property, but the converse and a universal homotopy-fiber lift are not
asserted.

The existing variable-time acceleration proof gives a stationary lift on
a prescribed duration-zero set using only the original parameter X. The
coherent parallel-lift proof uses only I × X and retains its actual
backtrack contraction, both endpoint maps and every zero-set value.
Original comparison correction combines these two constructions.
Fiberwise homotopy extension uses only I × D after genuine ordinary HEP.
The full boundary-track correction uses only (D × I) × I; its duration
vanishes at both path endpoints, correction time zero and the entire
prescribed boundary. The unpadding corollary retains the original boundary
homotopy at every intermediate time.

All five are direct proofs on the displayed compact tests, reusing the
accepted actual time-coordinate formulas. They do not invoke a universal
inverse family, strict-fiber total-space equivalence, HLP on a noncompact
mapping-path space, or the global bar fiber conclusion. In the planned
mapping-cylinder application the original endpoint projections still have
genuine HLP; only the final cylinder correction uses this smaller scope.
Existing full-HLP production sources are unchanged.

Ordered source compilation passed warning-free in
`logs/compact-lifting-corrections-check.log`. Recursive-origin and exact
parameter, path, base, zero-set, boundary, cube and degree-zero consumers
are checked by `audits/CompactLiftingCorrectionsAudit.lean`.
The source boundary is frozen in
`logs/compact-lifting-corrections-sources.sha256`. The fixed16 recursive-origin audit (4+5+1+1+5) and all14 consumers
passed warning-free in `logs/compact-lifting-corrections-audit-final.log`.
No source or initial-audit repair was needed; the second audit pins the
observed origin counts. Independent fresh review passed at13:03:30 with all16 origins and25
exact-map consumers, all dependency hashes unchanged. See
`REVIEW_20261009_COMPACT_LIFTING_CORRECTIONS.md`. All five files are outside the 12:10 archive.
