# Compact HELP on actual mapping-cylinder fibers

## Checked endpoint

`Quillen.CategoryTheory.TheoremB.CompactMappingCylinderFibers` proves
`CompactMappingCylinder.sourceFiber_compactHELP` for the literal source end
of a displayed topological mapping-cylinder pushout, on each original strict
fiber. Its only lifting input is full compact HELP for the original attaching
map on that strict fiber. There are no HLP, separation, nonemptiness, or
whole-space compactness assumptions.

The collapse and target maps form an actual homotopy equivalence on each
strict fiber. Its homotopy is the existing target-cylinder deformation,
restricted using its exact base-coordinate identity. The composite of collapse
with the source end is exactly `HomotopyFiber.strictMapOver` of the original
attaching map. Accepted full-boundary HELP cancellation proves the result,
retaining every time of an arbitrary prescribed boundary homotopy.

This construction does not identify a fiber with a quotient pushout. It does
not prove HLP of the mapping-cylinder projection or variable-base relative
lifting. Those remain separate obligations for chart gluing.

## Frozen evidence

Source SHA256:
`5285f0f1af4fe0dcd8c907b4960e46a853c9171ece355c349c5853c9332cabf3`.

- Manifest: `logs/compact-mapping-cylinder-fibers-sources.sha256`.
- Warning-free source check: `logs/compact-mapping-cylinder-fibers-check2.log`.
- Own audit: `audits/CompactMappingCylinderFibersAudit.lean`.
- Fixed23 defining-origin recursive audit and9 exact consumers:
  `logs/compact-mapping-cylinder-fibers-fixed23.log`, terminal12:34:55Z.
- All recursive axioms are among `propext`, `Classical.choice`, `Quot.sound`.
- Independent fresh build, fixed23 origins and15 strengthened consumers accepted:
  `docs/REVIEW_20261009_COMPACT_MAPPING_CYLINDER_FIBERS.md`.
- Sources were rehashed after checks; no frozen dependencies were modified.
