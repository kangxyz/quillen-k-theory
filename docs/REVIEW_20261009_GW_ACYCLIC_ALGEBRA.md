# Independent review: bounded acyclic cycles and truncations

Accepted 2026-10-09 05:07 UTC. This is algebraic support for
Gillet–Waldhausen, not the K-equivalence theorem.

## Exact mathematical scope

The ambient category is arbitrary abelian, with independent object and morphism
universes. The object predicate is replete, contains zero and is closed under
extensions and kernels of ambient epimorphisms between its objects.

`AcyclicCycles` uses the actual homological-complex cycle objects, cycle
inclusions and differential-to-cycle maps. Acyclicity makes the latter maps
epimorphisms. Downward integer induction from a strict upper term bound proves
all cycle objects belong to the predicate. No lower bound, global projectivity,
or cycle-membership hypothesis is inserted into that theorem.

`BoundedAcyclic` constructs the inherited exact category of actual termwise
bounded acyclic complexes with terms in the predicate. Extension closure is
proved from degreewise short exact sequences and the acyclicity theorem.

`TruncationMaps` identifies the actual mathlib truncation arrows at and below
their boundary. `AcyclicTruncation` proves that the actual truncation and its
actual cokernel remain bounded, acyclic and termwise in the predicate. At the
boundary, uniqueness of cokernels identifies the quotient with the next cycle
object; no unsupported quotient-closure assumption is used. The resulting
short exact sequence is lifted without changing its ambient arrows to an
inherited conflation.

## Independent verification

All four source files were read in full and independently recompiled into an
isolated artifact overlay, in dependency order, without using their live oleans.
The four checks were warning/error-free. Source hashes matched before and after.

`audits/GilletWaldhausenIndependentAudit.lean` recursively audited all 70
declaration origins, including generated/private declarations, with a fixed
expected count. Only `propext`, `Classical.choice` and `Quot.sound` occurred.
Arbitrary-universe consumers checked both membership theorems, the actual
inherited conflation, its unchanged first and second arrows, and the actual
quotient-to-next-cycle isomorphism.

Evidence: `logs/gw-algebra-independent-check.log`,
`logs/gw-algebra-independent-audit.log`,
`logs/gw-algebra-independent-hashes.log`, and
`logs/gw-algebra-independent-sources.sha256` (manifest SHA-256
`7aec0376e2c07356ac54162fcde01dc82dfff4f2039832b7a2c8e8eb11f0e4bb`).

## Boundaries

This review does not assert exactness of the truncation functor, the additivity
theorem, change-of-weak-equivalences fibration, Gillet–Waldhausen, or comparison
of strict with locally perfect complexes. These four files are outside the
already frozen 05:00 checkpoint and will be integrated with later reviewed work.
