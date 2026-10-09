# Actual local collar and finite weak-chart support

Frozen checked sources:

1. `NormalizedFibrationFirstCollar.lean`: the original two mapping cylinders
   supply the generic first-pushout collar data. The actual end is a genuine
   SDR of this open collar; its entire deformation preserves the original
   base. Outside the overlap, whole fibers lie in the collar. A genuine end
   fibration supplies weak covering-homotopy lifting of the collar projection.
2. `FiberwiseMappingPath/TargetRestriction.lean`: the subspace on which every
   stored path value lies in an arbitrary target subset is homeomorphic to the
   vertical mapping-path space of the genuinely restricted map. Every original
   path coordinate, constant section and scaling homotopy is retained. This
   is not the generally false endpoint-only restriction identification.
3. `CubicalSubdivision/ControlledWeakCharts.lean`: actual weak maps on all
   nonempty finite chart intersections supply strict HELP on each original
   finite cube test controlled by an open parameter cover. The source chart
   conditions and complete auxiliary comparison paths are retained through
   ordinary mapping paths and the proved incident-face lifting theorem.

The last conclusion is ordinary strict HELP: the original boundary is fixed,
while the comparison homotopy is not asserted vertical. Neither a local SDR
nor ordinary weakness is promoted to vertical endpoint RLP or full compact
HELP. Arbitrary base changes require their own genuine coordinate arguments.

## Checked evidence

- Sources: `logs/controlled-weak-chart-support-sources.sha256`.
- Audit: `audits/ControlledWeakChartSupportAudit.lean`.
- Exactly 54 defining origins, split `[16,35,3]`; all recursive axioms are
  `propext`, `Classical.choice`, or `Quot.sound`.
- All 16 original-map consumers pass, including independent universes,
  entire stored paths/scaling, empty target subset, exact SDR base equation,
  full original cube boundary and dimension zero.
- Initial scan and consumers: `logs/controlled-weak-chart-support-initial-audit.log`.
- Fixed-count final replay: `logs/weak-locality-check2.log`, terminal exit 0 at
  14:58:20 UTC on 2026-10-09. Its preceding command separately compiled the
  ordinary weak-locality wrapper; that source is outside the 54-origin count.

Independent acceptance is recorded separately.
