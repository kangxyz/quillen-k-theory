# Independent review: original canonical square-comparison detection

**Accepted for the stated local scope.** The unchanged source
`Quillen/Topology/HomotopyFiber/CartesianDetection.lean` has SHA256
`c7d97cb58dd4d44d37837f125f526b44eb705eaccc0abbe1960e1eaa0d327ef7`.

The whole source and its critical connectedness, actual fiber detection,
Hurewicz lifting, and based-homotopy prerequisites were read. The original
transition is exactly the existing fiber map: source coordinate `a(x)` and
path `b ∘ γ`. The comparison fiber map is the original canonical square
comparison on the source coordinate and retains the entire outer path `γ`.

The homotopy moves the intermediate parameter to `γ(t)`, assigns the inner
path `s ↦ b(γ(t*s))`, and keeps outer suffix
`s ↦ γ(1-(1-t)*(1-s))`. Both endpoint equalities are proved. Its value on each
supplied constant-path basepoint is fixed for every time, so the subsequent
based homotopy-set identification has the actual fixed-point hypothesis.
No unbased homotopy is silently used as a based one. The actual
`baseFiberComparison` is the forward map of the proved fiber equivalence.

All finite homotopy-set bijections, including zero, transfer from the
original transition to the comparison fiber map. The final theorem assumes
genuine path-connected source and base, a path-connected actual target
fiber, and an explicit source point above the stated base point. The actual
homotopy-pullback target is consequently path connected. The accepted LES
and path-transport results give bijections for the original canonical
comparison at every source point. These hypotheses exclude the vacuous
empty-source loophole; no stronger disconnected or unpointed claim is made.

Independent validation passed warning-free:
- Fresh source build in an isolated first-`LEAN_PATH` overlay, with the
  reviewed artifact excluded from prerequisite symlinks.
- Fixed **25** defining-origin recursive axiom audit, including private and
  generated declarations; only `propext`, `Classical.choice`, `Quot.sound`.
- **15** exact consumers: original source and path maps, prefix/suffix and
  intermediate-point formulas, both homotopy endpoints, the fixed chosen
  basepoint, explicit degree zero, all-point/all-degree detection, and
  genuine connectedness of the actual target.
- Frozen source hashes rechecked unchanged. The accepted ten-source
  relative-fiber calculus manifest was also rechecked.

Audit: `audits/CartesianDetectionIndependentAudit.lean`.
Evidence: `logs/cartesian-detection-independent-20261009/`, including
`check.log`, `deps.log`, `audit-final.log`, and the before/after hashes.
Script: `logs/verify-cartesian-detection-independent.sh`.
No production source was modified; all checks used slot1 and `-j1`.

This accepts the local original-map square theorem. Global bar realization,
finite weak-cartesian cube, and compact-parametric gluing remain separate.
