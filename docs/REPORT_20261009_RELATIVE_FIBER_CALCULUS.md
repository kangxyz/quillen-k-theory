# Actual relative-fiber calculus

## Checked endpoint

The ten-source boundary in
`logs/relative-fiber-calculus-sources.sha256` is checked warning-free and frozen.
It proves concrete prerequisites for the relative-realization fiber theorem.
It does not assert that global theorem.

- `SplitRealizationFiber.inclusion_bijective` derives every finite based
  homotopy-set bijection, including dimension zero, for the original split
  inclusion equipped with its constant path. Inputs are the actual row map
  `χ : E → A ⊗ B`, a genuine realization homotopy equivalence with precisely
  that forward map, and the strict splitting triangle. The whole resulting
  source/path pair is identified with the original product fiber inclusion.
- `ProductRealization.comparison_compact_lifts_universe` proves exact lifts in
  every compact-source universe using actual finite right support.
  `comparison_compactHELP` preserves an entire supplied boundary homotopy,
  rather than only its two endpoint equations.
- Compact HELP is proved closed under composition. The intermediate constant
  boundary prefix is removed using the genuine relative interval-square
  extension theorem. Exact injective compact lifting also passes to original
  source-change maps of actual homotopy fibers, retaining their path coordinate.
- The original first projections of actual product and product-type row
  fibers satisfy compact HELP. Their actual zeroth homotopy maps detect genuine
  path connectedness when the first factor is path connected.
- `HomotopyFiber.piMap_bijective_of_fiberMap` proves the long-exact-sequence
  detection step for a map over a fixed base. Degree `n+1` fiber bijectivity
  and degree `n` fiber injectivity imply bijectivity of its original degree
  `n+1` middle map. At `n=0`, the argument uses the actual pointed-set
  connecting map to the zeroth homotopy set; it assigns no group law to π₀.
- Actual path connectedness supplies the zero-degree conclusion. The accepted
  free-path-space transport then gives the same canonical bijectivity at
  every source point.
- A genuine Hurewicz fibration over a path-connected base has path-connected
  total space when one actual strict fiber is path connected. This is proved
  by lifting each point's base path, without a continuous choice of paths.
  The result applies to actual compact-open homotopy pullbacks.

## Evidence and dependencies

Own origin and exact-consumer audit: `audits/RelativeFiberCalculusAudit.lean`.
The corrected initial scan passed all39 defining-module declarations and all
exact consumers. Its successful prefix is preserved in
`logs/relative-fiber-calculus-initial-success.log`; the count-frozen rerun is
`logs/relative-fiber-calculus-fixed39.log`.
Exact source checks are in `logs/relative-split-fiber-compact-help-check2.log`,
`logs/relative-help-detection-bar-check2.log`,
`logs/relative-detection-bar-check4.log`, and
`logs/relative-connected-bar-check2.log`. Some serial logs subsequently stop
in a separate unfinished bar draft; preceding commands used shell `&&`, so
those later draft diagnostics do not invalidate the successful source checks.

Dependencies are the accepted finite-realization/product topology, actual
product-fiber topology, original HELP and homotopy-fiber LES, genuine
Hurewicz lifting, and the separately frozen `HomotopyGroups/PathTransport`.
Only the standard axioms are permitted by the recursive audit.

## Remaining global obligation

The checked boundary does not turn weak equivalences into continuous inverse
families. The actual canonical homotopy-pullback comparison still needs its
fiber-map identification, and the realization argument still requires a
new weak/compact-parametric cartesian pushout gluing theorem followed by
skeletal and compact sequential assembly. The two-sided bar presentation
and these global steps are outside this frozen boundary.
