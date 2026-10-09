# Actual collar fibers and compact HELP

The four frozen modules in `logs/compact-collar-fiber-geometry-sources.sha256` identify the actual strict fibers of a displayed double mapping cylinder at its two ends and open interior, then identify the fibers of its literal left/right collar restrictions.

The endpoint and interior homeomorphisms preserve the original attaching maps. The height case split proves full compact HELP for the actual collar comparison fibers from full compact HELP for the original attaching strict-fiber maps. A separate companion transports the original attaching homotopy-fiber HELP through the genuine Hurewicz strict-fiber equivalences and compact-HELP cancellation.

The final endpoints are `DoubleCylinder.leftCollar_strictFiberInclusion_compactHELP_of_homotopyFibers` and its right analogue. Inputs are the actual displayed pushouts, the original commuting map of spans, genuine Hurewicz lifting for the relevant original projections, and full compact HELP of the original attaching homotopy-fiber map at every point. Output is full compact HELP of the unchanged collar strict-fiber inclusion, retaining the literal constant path.

This boundary does not assert Hurewicz lifting for the collar or a global double-cylinder fiber theorem. Finite-parametric collar gluing remains a separate obligation.

## Validation

All four sources compiled warning-free in order. The fixed-count recursive declaration-origin audit passed all 92 origins (25, 40, 16, 11), with only `propext`, `Classical.choice`, and `Quot.sound`. Fourteen actual-map consumers passed, including the complete attaching path formula, strict-fiber comparison square, full HELP endpoints and finite homotopy-set bijectivity. Final terminal status: 2026-10-09 12:49:22 UTC.

Audit: `audits/CompactCollarFiberGeometryAudit.lean`.
Log: `logs/compact-collar-fiber-geometry-audit-fixed92.log`.
Independent review is recorded separately.
