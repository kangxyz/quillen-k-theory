# Independent review: incident-chart finite cubical lifting

**Accepted, 2026-10-09 14:46:00 UTC.** All four excluded-target fresh
builds, fixed-origin audit, twenty-one consumers, and before/after hashes
passed warning-free. No production source or live artifact was changed.

## Frozen scope

- `Quillen/Topology/CubicalSubdivision/FaceContainment.lean`
- `Quillen/Topology/CubicalSubdivision/IncidentCharts.lean`
- `Quillen/Topology/CubicalSubdivision/ControlledLifting.lean`
- `Quillen/Topology/CubicalSubdivision/ControlledChartLifting.lean`

Manifest: `logs/cubical-controlled-charts-sources.sha256`, fingerprint
`78d799e0fddef107df93dc696fd7fb1b1044cce4a4bde462454c63685983e3a5`.
All four files were read completely, together with the relevant original
face-intersection, outer-boundary and skeleton-pasting proofs.

## Semantic assessment

For an actual affine grid face, an interior intersection with another face
forces whole-face containment. The moving-coordinate lemma proves equality
of the original interval labels: different grid intervals meet only at
endpoints, which contradict the specified interior parameter. A fixed
coordinate in the containing face cannot meet a moving interior coordinate.
The remaining coordinates explicitly construct parameters in that containing
face for every point of the first face. No maximal-face or dimension
hypothesis is silently required. In dimension zero the unique empty-coordinate
face and its empty boundary behave literally.

`incidentCharts chart F` records the chart of every actual coface containing
`F`, not merely its arbitrarily assigned chart. It is a finite nonempty set
because the face itself is a coface. Containment reverses the chart-set
inclusion, so the combined source constraint is monotone with face
containment. Interior intersections bring the other face's chart into this
same finite constraint set.

`exists_controlled_grid_lift` performs genuine induction through the finite
closed face skeleton. Its invariant keeps the original target equation, the
whole original outer boundary, and every constraint of every face meeting
an already defined point. Faces lying in an outer wall use the original
boundary map. Other faces use only their full-boundary local filling input.
Their intersection with the outer boundary lies on their own parameter
boundary, where the prior stage is preserved exactly.

The original quotient skeleton-pasting theorem supplies continuity and exact
restriction to each attached face and to the lower skeleton. To maintain the
constraint invariant at a new point, a boundary intersection returns to the
old skeleton; an interior intersection invokes the proved whole-face
containment and monotonicity. Thus filling one cell cannot silently lose a
constraint needed by a later incident cell. The terminal skeleton is the
unchanged full cube. The local face-filling hypothesis contains no global
filler or global lifting conclusion.

`controlledChartMap` is the literal original map on the subspace satisfying
all chosen source-chart constraints and all chosen target-chart conditions.
Its image coordinate is exactly `p e`. The finite-intersection wrapper first
chooses an actual finite affine grid subordinate to the supplied open cover
of the cube parameter space. A whole face lies in every chart assigned to
any coface containing it. Consequently its boundary map lands in the actual
intersection-restricted source, using both the existing source invariant and
the original target equation. BoundaryLifting of that nonempty finite
intersection gives the filler through the actual finite face-coordinate
homeomorphism. Its original source coordinate retains every incident
constraint. The controlled induction then gives the final exact original
boundary and target equation.

Neither the source sets nor the target chart sets are assumed open. The
parameter sets are genuinely open and cover the whole test cube. Their
control of every originally supplied boundary source value is an explicit
hypothesis, separate from target coverage. Lifting is required on all
nonempty finite intersections, not just the individual charts. These
conditions must still be constructed in a later geometric application.

## Independent verification

The first-path overlay excludes all four target artifact families, compiles
the sources in order into fresh regular files, and verifies their actual
import paths through `lean --deps`. The single origin traversal audits
fixed **22 = 3 + 12 + 2 + 5** declarations and generated helpers recursively,
allowing only `propext`, `Classical.choice`, and `Quot.sound`.

The **21 consumers** retain all thirteen authored tests and add:

- equality of the original moving-interval labels at an interior intersection;
- unconditional actual face containment in dimension zero;
- every containing face's assigned chart, and extraction of the face's own
  source constraint;
- literal source and image conditions of an intersection-restricted point;
- the full controlled-grid theorem, including its simultaneous constraint
  conclusion on every original face;
- assembly of original BoundaryLifting from actual controlled covers of each
  supplied test, rather than assuming that global conclusion;
- existence of an actual source point over the zero-cube target.

Empty chart-index coverage is explicitly impossible, using the actual
nonempty cube. The zero-dimensional local filler still comes from the
nonempty incident intersection; no nonempty source assumption is inserted.
The source, target and chart-index universes remain independent `u`, `v`, `w`.

The dependency traversal seeds targets, the independent audit, and implicit
`Init`. All **3,501 prerequisite sources**, **16,097 dependency artifacts**,
the frozen target source hashes, audit bytes, and toolchain/project pins were
checked before and after verification. Every check passed on the first run;
no audit repair was needed.

## Evidence and remaining scope

- Audit: `audits/CubicalControlledChartsIndependentAudit.lean`.
- Preparation: `logs/prepare-cubical-controlled-charts-independent.py`.
- Replay: `logs/verify-cubical-controlled-charts-independent.sh`.
- Evidence directory: `logs/cubical-controlled-charts-independent-20261009/`.
- Terminal log: `logs/cubical-controlled-charts-independent-20261009/terminal.log`.
- Evidence manifest: `logs/cubical-controlled-charts-independent-20261009/artifacts.sha256`.

This is actual finite subdivision and controlled lifting infrastructure.
The geometric whole-track parameter cover, its finite-intersection lifting
inputs, the mixed open/closed attachment comparison, and the global
Waldhausen fibration theorem remain separate obligations. This review does
not infer arbitrary compact HELP or a homotopy inverse from finite lifting.
This boundary is post-freeze work outside the immutable 12:10 checkpoint.
