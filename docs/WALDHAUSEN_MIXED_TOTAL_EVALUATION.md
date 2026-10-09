# Prescribed total evaluation into the original coarse S-construction

`MixedNerves/TotalEvaluation.lean` uses the shared `coarseWeakRowNerve` target.
Its `coarseRowEvaluation` has the original coarse-chain evaluation in each
actual inner row degree. Strict naturality follows from the proved original
CompatibleFunctor square applied to genuine row restriction.

The accepted arbitrary-bisimplicial rowwise-diagonal theorem produces
`coarseRowEvaluationHomotopyEquiv`, with precisely the original diagonal
map as forward map. The actual coarse-row presentation `coarseSSetIso` then
gives `totalCoarseEvaluation` and `totalCoarseEvaluationHomotopyEquiv`, whose
target is the existing original coarse Waldhausen simplicial set. The exact
forward-map identity is proved. This coarse evaluation endpoint retains
independent object and hom universes: each actual row category already has
object universe max(u,v). No extension, saturation or cylinder hypothesis is
required for this coarse evaluation.

`cofRowEvaluation` is the original row-diagonal inclusion followed by the
same evaluation, and `totalCofEvaluation_eq` proves the literal factorization
of its prescribed map. `totalCofEvaluationHomotopyEquiv` follows by composing
the separately established genuine total mixed-inclusion equivalence with
the coarse evaluation equivalence. This endpoint explicitly retains that
comparison's common object/hom universe, structural JointData, proved second-
endpoint section, and coarse two-out-of-three condition. No equivalence or
fibration conclusion is encoded as a hypothesis. The actual complex-cylinder
consumer supplies these inputs from the genuine cone/shift-closed model.

The original relative S-construction presentation and global fibration
assembly remain separate. All equivalences here are genuine unbased
realization homotopy equivalences with prescribed forward maps; no based
inverse or additional K-theory identification is asserted in this file.

The source compiles warning-free. Its frozen manifest is
`logs/mixed-total-evaluation-sources.sha256`. The all18-origin recursive audit and16 consumers passed warning-free with
only the standard three axioms. The fixed18 guard was independently confirmed in `audits/MixedTotalEvaluationAudit.lean`, covering actual
maps, inner ordinal naturality, the original coarse S-set, original diagonal
components and degree0, exact cylinder inputs and an arbitrary-scheme coarse
evaluation specialization. Independent review accepted the evaluation boundary.

Independent acceptance on2026-10-09 used four fresh evaluation sources,
fixed111 defining origins and79 original-map/structural-input consumers,
warning-free with unchanged production and dependency hashes. The actual
coarse target and explicit universe scopes were retained.
