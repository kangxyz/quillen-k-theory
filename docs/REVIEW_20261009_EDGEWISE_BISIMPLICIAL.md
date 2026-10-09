# Independent review: partial bisimplicial edgewise subdivision

Reviewed 2026-10-09 independently of the implementation author. Scope:
`Quillen/Topology/Realization/EdgewiseBisimplicial.lean`, frozen by
`logs/edgewise-bisimplicial-sources.sha256`.

The accepted endpoint is actual homotopy equivalence of diagonal realizations
for subdividing either one of the two bisimplicial directions, with exactly
that direction's second-half endpoint as the forward map. The separate
upper-index comparison needed by Q/S is explicitly identified with the
inner endpoint on the outer-subdivided diagram.

The proof does not assume rowwise realization invariance. Double subdivision
is identified with ordinary edgewise subdivision of the diagonal by a natural
simplicial isomorphism. The two orders of partial endpoint restriction compose
to the already proved canonical global endpoint; the second order uses the
actual naturality square. A third adjacent map gives a second global endpoint
on a subdivided diagram. The proved homotopy-level adjacent-composites theorem
therefore supplies each individual partial comparison, preserving its exact
forward continuous map. This is a genuine two-out-of-six argument, rather than
an unsupported inference from a single composite being an equivalence.

No mathematical blocker was found. No Q/S equivalence, degreewise-to-diagonal
invariance theorem, or naturally chosen inverse is claimed by this module.

Independent current-source rehash build of the module passed, followed by
an independent execution of `audits/EdgewiseBisimplicialAudit.lean`. All 21
source-origin declarations, including private/generated helpers, have only
`propext`, `Classical.choice`, and `Quot.sound` in their recursive axiom
closures. The canonical forward-map statements are among those audited.
The source hash matched before and after both checks. Logs:

- `logs/edgewise-bisimplicial-independent-build.log`
- `logs/edgewise-bisimplicial-independent-all-axioms.log`
- `logs/edgewise-bisimplicial-independent-final-hash-check.log`

The module is outside the frozen 04:11 archive. Public integration is a
separate step. No proof source was modified by this review.
