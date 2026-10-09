# Independent review: literal loops and the original double-S base

Accepted 2026-10-09 12:36:03 UTC.

Both complete sources were read: `Topology/HomotopyFiber/ContractibleSource`
and `Waldhausen/Fibration/AllWeak/OrdinaryRows`, under `Quillen`.
Exact frozen manifest: `logs/contractible-loop-ordinary-rows-sources.sha256`.

## Semantics

A contractible source is contracted to the displayed original point by a
chosen contraction followed by the reverse track at that point. No constant
track for this modified contraction is asserted. The actual inclusion of
that point is therefore an unbased homotopy equivalence. The point-source
homotopy fiber is explicitly homeomorphic to the existing actual path
space `Path y y`, with its full path coordinate unchanged. Applying the
accepted source-equivalence theorem proves the literal original loop
inclusion is a homotopy equivalence. Its displayed source point, entire
path and constant-loop basepoint are exact. The induced original based
maps are bijective in every finite degree, including zero. Independent
source/target universes are retained. The actual all-weak relative-tail
consumer uses the separately proved contractibility and assumes no
fibration conclusion.

The double-S base result is an actual natural isomorphism of the original
ordinarySRows diagrams. The forward map applies the genuine exact
all-acyclic inclusion to each original row, and the inverse inserts only
the trivial acyclicity witnesses. Actual ordinal restrictions commute
strictly; both composites are strict identities before realization.
Original objects and morphisms, all-zero simplices and the full original
diagonal are retained. This layer has the explicit common-universe
SmallCategory scope of the existing S-map API.

These are exact prerequisites for the later fiber-exchange diagram. They
do not prove the global relative-realization fiber theorem or identify
its canonical reversed zero-to-inclusion nullhomotopy by assumption.

## Verification

A separate overlay excluded both target artifact families and rebuilt the
exact sources, with fresh regular target imports verified by `lean --deps`.
The exhaustive recursive audit checks exactly **42 origins = 25 + 17**
against the three standard Lean axioms. All **29 consumers** pass: the
25 authored consumers plus unchanged point coordinate, the literal loop
inclusion's inverse homotopy, strict full-diagonal inverse equality and
its original nested-grid object formula. Existing consumers include
original paths/basepoints, degree zero, all finite degrees, actual relative
tail, both ordinal naturalities, original row morphisms and all-zero rows.

All target hashes, **3,520 prerequisite-source**, **16,101 artifact**, and
project/toolchain-pin hashes match before/after. The first independent
source and audit run passed warning-free; no repair was needed.

- Audit: `audits/ContractibleLoopOrdinaryRowsIndependentAudit.lean`
- Preparation: `logs/prepare-contractible-loop-ordinary-rows-independent.py`
- Replay: `logs/verify-contractible-loop-ordinary-rows-independent.sh`
- Driver: `logs/contractible-loop-ordinary-rows-independent-driver.log`
- Evidence: `logs/contractible-loop-ordinary-rows-independent-20261009/artifacts.sha256`

Both endpoints are outside the frozen12:10 archive.
