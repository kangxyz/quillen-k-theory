# The original common-base homotopy-fiber square

For actual continuous maps p:X→B, q:Y→B and j:X→Y with the strict square
q∘j=p, `HomotopyFiber/CommonBaseSquare.lean` identifies the actual fiber
of p at b with the strict pullback of the actual projection hofib(q,b)→Y
along j. Its forward map stores the original x and the original mapOver
fiber point (j(x), γ); its inverse removes the redundant fiber source
coordinate. The whole original γ path is retained in both directions.

The actual homotopy-fiber projection already has a proved covering-homotopy
lifting property. The accepted strict-pullback-to-homotopy-pullback
comparison therefore gives a genuine homotopy equivalence, with forward map
exactly the original comparison for the common-base fiber square. The
parameter coordinate, original mapOver fiber coordinate, unchanged entire
inner q-path, and literal constant outer path are exposed separately.

The theorem is generic for spaces in one displayed universe, matching the
existing actual lifting API. It imposes no connectedness, nonemptiness,
finiteness, or lifting property on p or q. Its finite based homotopy-degree
conclusion includes degree zero and every actual fiber point. An empty
fiber still has the stated actual homotopy equivalence.

This is a universal actual-fiber model. Applying it to original relative
S-realizations still requires the two genuine global relative-tail fiber
comparisons and their original-map compatibility. Those global comparisons
are not assumed or concluded by this source.

The focused source check passed warning-free. The combined source manifest
is `logs/all-weak-fiber-square-sources.sha256`; the single-pass recursive
origin audit, including unchanged inner paths, constant outer paths,
empty-aware general scope, degree zero and the actual original relative
inclusion map, is in `audits/AllWeakFiberSquareAudit.lean`. The final fixed41 audit
([20,21]) and all31 consumers passed warning-free in
`logs/all-weak-fiber-square-audit-final.log`. Independent fresh2/fixed41/37-consumer review is accepted; see
`docs/REVIEW_20261009_ALL_WEAK_FIBER_SQUARE.md`.
