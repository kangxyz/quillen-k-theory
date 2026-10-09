# Independent review: actual fiber transport and compact HELP

## Accepted scope

Accepted after full semantic inspection, fresh isolated rebuilding of both
sources, and the fixed-13 recursive-origin audit with 17 exact consumers.
Every check passed warning-free. The terminal audit completed at 09:57:46 UTC
on 2026-10-09; frozen source and inspected prerequisite hashes match before
and after validation.

Frozen manifest: `logs/basepoint-help-sources.sha256`, fingerprint
`5f88f53f6635a36ec75a0c87cdc83fd0e13c510fd1da55564303569a170f8326`.

- `Quillen/Topology/HomotopyFiber/BasepointTransport.lean`:
  `96d3f84384c5f724d09dfa2d4e4ef16722c402e7c57a90f6707a2da05bff1404`
- `Quillen/Topology/HomotopyFiber/BasepointHELP.lean`:
  `3b666ca81cb5efb734032ab672c8de286b98ecb2b9a8b556cdc1dabb1c2dc9ea`

Neither production source was edited during review.

## Actual mathematical contract

For an arbitrary continuous map `p : E → B` and a displayed path `γ : b ⟶ c`,
`basepointTransportEquiv p γ` is a genuine homotopy equivalence between the
original compact-open-path fibers at `b` and `c`. Its forward map keeps the
source point exactly, and its full path is exactly the original fiber path
followed by `γ`, using the standard concatenation parametrization.

The construction uses the actual fiber-to-pullback homeomorphism, reversing
the fiber path into the pullback of a constant point map. The displayed path
is a homotopy between the two constant maps. The existing actual pullback
homotopy equivalence prefixes the reversed path, then the inverse
homeomorphism reverses it back. The supporting pullback construction was
read: its inverse uses the reversed homotopy, and its genuine inverse
homotopies cancel the two prefixes and remove constant padding continuously.
No desired fiber equivalence is supplied as a hypothesis.

Transport commutes strictly with the original `mapOver` over a common base.
The arbitrary-square variant commutes strictly with the original
`HomotopyFiber.map`, using `γ.map v.continuous` in the target. The proof checks
the complete paths with their actual concatenation parametrization, not
merely their endpoints or their homotopy classes. No fibration assumption is
needed for these homotopy-fiber statements.

Full compact HELP propagates through this square by composition with actual
transport equivalences and the accepted first-map cancellation theorem.
A `Joined` hypothesis supplies an individual path for each proposition; it
does not assert a continuously chosen path family or global inverse family.

For genuine fibrations `p` and `q`, the original strict-fiber map has compact
HELP exactly when the original path-space fiber map does. The proof uses the
actual strict-fiber inclusions, whose forward maps are genuine homotopy
equivalences obtained from HLP. Their naturality square commutes on the
literal original map and constant path. Composition and cancellation prove
both directions. Consequently strict-fiber HELP propagates along individual
joined base points too.

## Limits

One arbitrary common universe is explicit, matching the existing HLP/HELP
APIs. No compactness, separation, connectedness or nonemptiness is assumed
for the original spaces. A displayed base path necessarily supplies its two
base points, but either fiber may be empty. The homotopy equivalence handles
empty fibers honestly. Full HELP retains every value of the prescribed
boundary homotopy, not only endpoints. Strict-fiber conclusions require the
two genuine HLP hypotheses; the homotopy-fiber conclusions do not.

These endpoints give individual-path transport. They do not establish
continuous transport for arbitrary chosen path families or any finite-cover
or global gluing theorem.

## Independent evidence

- Isolated first-`LEAN_PATH` overlay:
  `logs/basepoint-help-independent-20261009/olean`. Both reviewed artifact
  stems are excluded before rebuilding; unchanged dependencies are symlinked.
- Fixed audit: `audits/BasepointHELPIndependentAudit.lean`, all 13 origins
  (eight transport, five HELP), including generated declarations, recursively
  allowing only `propext`, `Classical.choice` and `Quot.sound`.
- Seventeen consumers import the combined `Quillen.Library` and test exact
  source/path maps, both naturality squares, full HELP for arbitrary squares,
  actual all-degree and explicit degree-zero transport maps, empty fibers,
  joined-path propagation, strict-fiber comparison, and literal full
  prescribed-boundary HELP on both kinds of fibers.
- Script: `logs/verify-basepoint-help-independent.sh`, shared slot1 and
  single-threaded Lean. Source and key prerequisite hashes are checked before
  and after the fresh build/audit. Dependency resolution is logged explicitly.
- Evidence directory: `logs/basepoint-help-independent-20261009/`.

Terminal evidence: `check.log`, `audit-fixed13.log`, `deps.log`,
`hashes-after.log` and `prerequisites-after.log` in that directory.
Artifact manifest: `logs/basepoint-help-independent-20261009/artifacts.sha256`.
