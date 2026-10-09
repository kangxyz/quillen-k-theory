# Independent review: original square and bar fiber homotopy equivalences

Accepted 2026-10-09 10:22 UTC, after semantic inspection, fresh isolated
compilation of both frozen sources, a fixed-18 recursive-origin audit and
18 independent consumers. All checks passed warning-free. Only `propext`,
`Classical.choice` and `Quot.sound` occur in the recursive axiom closures.

Frozen sources: `logs/square-bar-fiber-he-sources.sha256`.

## Genuine square-fiber theorem

`HomotopyFiber.mapHomotopyEquivOfEquivalences` assumes a strictly commuting
square whose supplied original total and base maps are genuine homotopy
equivalences. Its forward map is definitionally the unchanged original
homotopy-fiber map: the source is mapped by the given total map and the
whole original path is postcomposed by the given base map.

The actual homotopy-pullback source projection is a genuine equivalence
because its parameter map is one. Cancelling that projection against the
original total equivalence gives a genuine equivalence whose forward map
is the canonical constant-path comparison. Genuine source invariance gives
its original fiber comparison. The independently established explicit
prefix/suffix homotopy identifies this comparison up to homotopy with the
original square fiber map followed by the genuine base-fiber comparison.
Replacement of the forward map and cancellation retain exactly the desired
original fiber map. Actual continuous inverse maps and both inverse
homotopies are constructed; this is not a weak-to-strong upgrade.

The source/base-fiber invariance, source-projection equivalence, original
comparison-fiber homotopy and genuine cancellation implementations were
inspected. No connectedness, fibration or nonemptiness hypotheses are added.
The common universe is the one required by the existing path-space API.

## Actual two-sided-bar augmentations

`dropFiberHomotopyEquiv` and `evaluationFiberHomotopyEquiv` apply the theorem
to the already proved genuine equivalences of the original total and base
bar augmentations. Their forward maps are definitionally the previously
defined `dropFiberMap` and `evaluationFiberMap`, including their literal
complete source/path formulas. The evaluation target is the unchanged
original diagonal fiber.

This improves the earlier weak bar-fiber result to a genuine homotopy
equivalence by the stronger hypotheses already proved for these maps.
It supplies transport between the original bar, replacement and diagonal
fibers. It does not identify a single row fiber with the global replacement
fiber and does not prove the global row-fiber or Waldhausen fibration theorem.

## Validation evidence

Script: `logs/verify-square-bar-he-independent.sh`.
Fresh overlay: `/tmp/quillen-square-bar-he-independent-1019`, first on
`LEAN_PATH`; both target artifact families were excluded before rebuilding.
Source hashes were checked before and after. The dependency listing confirms
that the second new module uses the fresh first module.

Audit: `audits/SquareBarFiberHomotopyIndependentAudit.lean`. The independent
consumers include a public-library import, the original comparison and fiber
maps, literal complete source/path coordinates, both genuine inverse laws,
all finite homotopy degrees including zero, empty fibers and full compact
HELP of the original square and bar maps. No desired conclusion is supplied
as a hypothesis.

Logs: `logs/square-bar-he-independent-{build,audit,prehash,posthash}.log`.
Evidence: `logs/square-bar-he-independent-artifacts.sha256`.
Both sources and these results are outside the frozen 09:45 archive.
