# Exact base change of vertical endpoint lifting

Frozen source pair: `logs/fiberwise-mapping-path-base-change-sources.sha256`.
The modules are `FiberwiseMappingPath/BaseChange` and `BaseChangeLifting`.

The actual pulled-back source consists of pairs `(t,x)` satisfying
`q(f(x)) = g(t)`; the target consists of `(t,y)` satisfying `q(y) = g(t)`.
The map is literally `(t,x) ↦ (t,f(x))`.

`baseChangeHomeomorph` identifies its vertical mapping paths with pairs of
the new base point and an original vertical mapping path lying over it.
It retains every original path value, the original source, and the new
base coordinate. Its inverse restores the constant new base coordinate at
every path time. All four object universes are independent.

`endpoint_boundaryLifting_baseChange` proves strict finite cube-boundary RLP
for the new vertical endpoint from that of the original vertical endpoint.
The lift uses the target's actual parameter coordinate; its boundary equals
the original boundary map, including the whole stored path.
`baseChangedMap_isWeakHomotopyEquivalence` consequently proves complete
weakness of the literal base-changed map, including degree zero and component
surjectivity. `endpoint_boundaryLifting_restriction` proves the corresponding
exact endpoint result for every base subset, including intersections and
empty subsets. No openness or fibration hypothesis is inserted here.

This is a stability result for an already proved finite lifting property.
It does not assert preservation of arbitrary topological quotient pushouts
by base change, or establish a global relative-realization fiber theorem.

## Author validation

Both exact sources recompiled warning-free in dependency order. The single
origin scan passed all34 defining declarations recursively with only the
standard three axioms. All13 consumers passed, including literal full path
coordinates, both inverse round trips, the original map, explicit degree zero,
components, smaller charts, intersections and the empty chart.

- Audit: `audits/VerticalMappingPathBaseChangeAudit.lean` (fixed34 guard)
- Clean ordered recheck and initial audit: `logs/fiberwise-mapping-path-base-change-audit-initial.log`
- Standalone terminal source check: `logs/fiberwise-mapping-path-base-lifting-check3.log`

Independent acceptance is recorded separately by the reviewer.
