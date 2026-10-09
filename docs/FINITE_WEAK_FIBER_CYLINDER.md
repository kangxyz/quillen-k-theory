# Finite bridge-end HELP with weak original fiber maps

Status: all three sources compile warning-free (terminal 2026-10-09
14:19:14 UTC) and are frozen in
`logs/compact-cylinder-weak-input-sources.sha256`, fingerprint
`fa606b4a9b4bc32ac3fa8bbfd2b4513fcd1fdd7ce6069469528435909aa6a495`.
The ordered replay and recursive origin audit passed warning-free at
2026-10-09 14:22:13 UTC: exactly 10 defining-module origins, only the three
standard axioms, and all 9 initial exact-map consumers. The fixed-10 replay
and all 11 consumers passed warning-free at 2026-10-09 14:24:53 UTC.
Implementation and both prerequisite source manifests match. Independent
acceptance of this three-source boundary is not yet claimed.
The earlier nine-source boundary is unchanged.

## Checked source endpoint

For a genuine displayed mapping cylinder of `f : A → C`, let `j : A → M`
be its original source end, `r : M → C` its original collapse, and `π=r≫base`.
`source_endpoint_boundaryLifting_of_weak_fibers` takes:

- genuine HLP of the original `f≫base` and `base`;
- the actual compact locally compact lifting property of `π`;
- the complete, empty-aware weak-equivalence property of every original
  strict-fiber map of `f`.

It concludes the literal finite cube-boundary RLP of
`FiberwiseMappingPath.endpoint π j`. The realization-model wrapper derives
its compact cylinder lifting input from a genuine homeomorphism of the base
to an actual simplicial realization. It does not require full compact HELP
on the original attaching-map fibers.

`source_cube_fullHELP_of_weak_fibers` spells out the finite relative result:
for the original boundary map and prescribed vertical boundary homotopy on
an actual cube, the filler extends that boundary exactly, has the displayed
base exactly, and its vertical comparison equals the original boundary
homotopy at every time. All dimensions, including the empty boundary of the
zero-cube, are included.

## Proof route

1. Over an explicitly contracted base of genuine fibrations, actual
   strict-fiber inclusion homotopy equivalences and genuine two-of-three
   transfer the complete weak property to the original total map.
2. Pullback fiber homeomorphisms identify the literal pullback transition
   with the original strict-fiber transition, retaining its coordinates.
3. Pull the original fibrations back over the supplied finite cube. Its
   contraction and the previous steps make the actual total transition weak.
   `WeakFinite.cube_strictHELP` supplies a relative lift on this finite test.
4. Genuine stationary base correction, fiberwise HEP, and boundary unpadding
   restore the exact base while preserving the entire original boundary
   track. This proves `weak_fullHELP_on_cube_over_base` for the original map.
5. The canonical cylinder collapse still has genuine full compact HELP
   because it is an actual homotopy equivalence. The separately proved
   compact vertical cancellation is used only with that collapse, not with
   a merely weak map. It retains the complete side-and-caps boundary.
6. Packing the resulting original vertical path gives the exact original
   endpoint RLP in every finite dimension.

## Scope and sources

The weak-to-HELP step is explicitly limited to finite cube-boundary pairs.
No weak-to-arbitrary-compact HELP assertion is used. The two original
projections still have unrestricted HLP; no unrestricted HLP of the mapping
cylinder is inferred. No open-attachment locality, bar fiber theorem, or
Waldhausen fibration conclusion is contained in this boundary.

- `Quillen/Topology/HomotopyFiber/ContractibleBaseWeak.lean`
- `Quillen/Topology/HELP/WeakFiberCube.lean`
- `Quillen/CategoryTheory/TheoremB/CompactMappingCylinderWeakBoundary.lean`

The own audit is
`audits/CompactMappingCylinderWeakBoundaryAudit.lean`. Its consumers include
original total maps, complete relative homotopies, dimension zero, the
literal vertical endpoint, and original-map weak/component conclusions.
The separate WeakFinite four-source prerequisite passed independent fresh
checking of all 87 origins and 32 consumers at 2026-10-09 14:20:31 UTC.
The nine-source finite-cylinder prerequisite was independently accepted by
fresh rebuilding, fixed 47 origins, and 29 consumers at 2026-10-09
14:24:14 UTC. This specialization has completed its own final audit and
remains subject to independent review.

## Author verification

- Source manifest: `logs/compact-cylinder-weak-input-sources.sha256`.
- Successful ordered replay and initial audit: `logs/compact-cylinder-weak-input-initial-audit.log`.
- Fixed-10 audit: `audits/CompactMappingCylinderWeakBoundaryAudit.lean`.
- Final guard/11-consumer replay: `logs/compact-cylinder-weak-input-fixed10.log` (terminal success).

The final consumers also require actual emptiness of the mapping cylinder
when the original source is empty, and explicitly instantiate the original
vertical endpoint lifting problem in dimension zero. They do not add a
nonemptiness assumption to any implementation theorem.

- Final authored evidence: `logs/compact-cylinder-weak-input-evidence.sha256`.
