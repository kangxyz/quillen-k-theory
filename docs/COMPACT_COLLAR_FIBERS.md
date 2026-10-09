# Compact HELP transported by the actual collar comparison

## Checked scope

`HomotopyFiber.strictFiberInclusion_compactHELP_of_equiv` starts with an
actual total-space homotopy equivalence `e : E ≃h F`, a genuine HLP map
`q : F → B`, and full compact HELP of the original strict-fiber map induced
by `e`. It proves full compact HELP of the original canonical inclusion
`strictFiberInclusion (q.comp e.toFun) b`.

The proof uses the actual source-change equivalence on homotopy fibers,
the strict-fiber inclusion equivalence supplied by genuine HLP of `q`, the
literal commuting triangle, and accepted full-boundary cancellation.

`leftCollar_strictFiberInclusion_compactHELP` and its right analogue use the
unchanged actual collar comparison homotopy equivalence and genuine endpoint
pullback fibration. Their explicit remaining input is compact HELP of the
actual `leftCollarComparisonFiber` or `rightCollarComparisonFiber`.
Deriving that input from original attaching data is a separate file owned by
the chart author. No HLP of the collar, whole-chart deformation, or global
weak-cartesian gluing is asserted here.

## Evidence

- Frozen manifest: `logs/compact-collar-fibers-sources.sha256`.
- Warning-free source check: `logs/compact-collar-fibers-check2.log`.
- Own fixed7 recursive defining-origin audit:
  `logs/compact-collar-fibers-fixed7.log`, terminal12:38:30Z.
- `audits/CompactCollarFibersAudit.lean` checks two actual generic consumers,
  including the entire original prescribed boundary homotopy, and prints all
  four literal collar APIs. Independent review adds actual collar consumers.
- Only `propext`, `Classical.choice`, `Quot.sound` occur recursively.
- Frozen sources rehashed unchanged after the audit.
