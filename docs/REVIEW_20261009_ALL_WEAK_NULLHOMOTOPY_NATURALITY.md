# Independent review: the entire original acyclic nullhomotopy

Accepted 2026-10-09 13:17:52 UTC.

The three complete sources in
`logs/all-weak-nullhomotopy-naturality-sources.sha256` were read: the original
weak-transformation cylinder naturality, actual realization homotopy
naturality, and `AllWeak/NullhomotopyNaturality`.

## Semantics

Categorical postcomposition of the nerve cylinder is proved through the
actual one-arrow diagram and uncurrying, using the functor's composition
law. Exact precomposition and postcomposition of the original S-cylinder
are strict equalities of full simplicial maps, retaining their endpoints.

For realization, the supplied strict cylinder square is transported using
the already proved naturality of the actual inverse realization-cylinder
isomorphism. This yields equality at every time and every original source
point; it does not replace either homotopy by one with equal endpoints.

The acyclic square uses the actual original acyclic inclusion, its all-weak
coarse exactness, and the original change-of-weak map. Chosen zero objects
are compared with the explicit nested-structure zero equality. Exact
zero-transformation components then identify the entire original cylinder.
The realized theorem evaluates both original zero-to-identity homotopies
at the same reversed time, establishing the actual canonical nullhomotopy
with its existing reversal convention. Only the genuine coarse
two-out-of-three hypothesis is used. Independent object and hom universes
are retained, including actual bounded-term scheme consumers. There is no
fibration, homotopy-cartesian square or canonical fiber equivalence premise.

## Independent verification

The first-path overlay excludes all three target artifact families, then
freshly rebuilds them in order. The fixed-origin recursive audit expects
exactly **7 = 4 + 1 + 2** source declarations. **13 consumers** include the
nine authored original-cylinder, full path, endpoints, fixed zero and
arbitrary-scheme checks, plus exact generic S-pre/postcomposition, the
literal canonical source coordinate and equality of the entire stored
continuous path.

- Audit: `audits/AllWeakNullhomotopyNaturalityIndependentAudit.lean`
- Preparation: `logs/prepare-all-weak-nullhomotopy-naturality-independent.py`
- Replay: `logs/verify-all-weak-nullhomotopy-naturality-independent.sh`
- Final audit replay: `logs/verify-all-weak-nullhomotopy-naturality-independent-final.sh`
- Evidence directory: `logs/all-weak-nullhomotopy-naturality-independent-20261009`

The fresh source rebuild and fixed7 recursive-origin scan passed. One extra
review consumer initially used continuous-map composition directly on a
TopCat morphism; selecting its `.hom` corrects the audit only. Initial logs
are retained. The final replay passed warning-free, including all13 consumers and
the fixed7 recursive-origin guard. All target, 3,493 prerequisite-source,
16,065 dependency-artifact and project/toolchain-pin hashes match before
and after. No production source changed. These sources are outside the frozen12:10 archive.
