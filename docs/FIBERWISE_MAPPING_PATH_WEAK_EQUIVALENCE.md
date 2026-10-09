# Complete weakness of the original vertical endpoint

Source: `Quillen/Topology/FiberwiseMappingPath/WeakEquivalence.lean`.
Namespace: `Quillen.FiberwiseMappingPath`.

The source is compiled warning-free and frozen. Its fixed-three-origin,
fifteen-consumer author audit passed warning-free at 2026-10-09 14:55:29 UTC,
with only `propext`, `Classical.choice`, and `Quot.sound`. Source hashes match.
Independent review is pending.

For the original `q : C(F, B)` and `f : C(E, F)`, the theorem
`endpoint_isWeakHomotopyEquivalence_iff q f` proves complete weakness of the
original vertical mapping-path endpoint exactly when the original `f` is
weak. The source, target and base retain independent universes `u`, `v`, `w`.
No common-universe restriction is introduced.

The proof uses only the existing genuine homotopy equivalence of the original
constant-path inclusion, the exact identity `endpoint_inclusion`, and the
accepted empty-aware two-out-of-three theorem. It preserves actual component
surjectivity and all finite based homotopy-set maps, including degree zero.
No continuous inverse to a merely weak map is chosen.

Supporting APIs:

- `inclusion_isWeakHomotopyEquivalence q f`: weakness of the unchanged
  constant-path inclusion, derived from its existing genuine homotopy equivalence.
- `endpoint_isWeakHomotopyEquivalence_of_homotopyEquiv q f e he`: an actual
  homotopy equivalence `e` with `he : e.toFun = f` supplies weakness of the
  original endpoint, retaining that exact original forward map.

The existing `Basic` API provides the original inclusion, path contraction,
and strict endpoint-composite identity. `Locality` provides a stronger local
boundary-lifting criterion. This module does not duplicate or alter those
constructions. It asserts no endpoint HLP, vertical HELP, strict lifting,
fiber conclusion, or global gluing theorem.

The audit retains the original composite, complete stored inclusion path,
actual endpoint and vertical base coordinate, both directions of the weak
criterion, the HE-forward-map specialization, all finite degrees and explicit
pi-zero, actual components, an empty-source/nonempty-target obstruction, both
spaces empty, and the identity map over an arbitrary target projection.

Audit: `audits/FiberwiseMappingPathWeakEquivalenceAudit.lean`.
Frozen manifest: `logs/fiberwise-mapping-path-weak-equivalence-sources.sha256`.
Source log: `logs/fiberwise-mapping-path-weak-equivalence-check.log`.
Audit log: `logs/fiberwise-mapping-path-weak-equivalence-audit.log`.
