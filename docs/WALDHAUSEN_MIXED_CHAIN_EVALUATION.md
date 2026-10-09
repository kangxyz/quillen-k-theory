# Prescribed evaluation of the original mixed chains

`MixedNerves/ChainEvaluation.lean` transports actual diagonal evaluation
through the accepted literal coarse/fine transposition. The resulting
`coarseChainEvaluation` sends an original mixed chain to its diagonal
vertices. Each diagonal arrow is its original coarse-chain arrow followed
by its original fine-transformation component. The realization homotopy
equivalence has exactly this evaluation as forward map; its inverse is the
original constant section transported through the inverse transpose. Their
section composite is proved to be the identity simplicial map.

`cofChainEvaluation` is the actual original inclusion followed by this
augmentation. This file does not use that definition alone to assert a
cofibration-chain comparison equivalence.

The original base functor on coarse weak categories is
`coarseWeakPostcompose`. Diagonal, coarse-chain and cofibration-chain
evaluation are strictly natural for the already defined CompatibleFunctor,
which carries only actual fine/cofibration/coarse predicate preservation.
The naturality proof uses the original base functor's composition law on
the actual two-factor diagonal arrow, without inverse choices. This is the
naturality needed for genuine inner-row reindexing and the separate total
augmentation, whose target is the shared `coarseWeakRowNerve`.

Object universe Type(max u v), hom universe v is displayed. No cylinder,
saturation, extension or fibration conclusion is an input to the evaluation
homotopy equivalence. The source check and all20-origin recursive audit passed warning-free, with
only the standard three axioms. All17 consumers (16 examples plus actual
arbitrary-scheme HE) passed. The final fixed20 guard rerun also passed warning-free;
the driver is `audits/MixedChainEvaluationAudit.lean`. The frozen source
manifest is `logs/mixed-chain-evaluation-sources.sha256`; independent review accepted the evaluation boundary.

Independent acceptance on2026-10-09 used four fresh evaluation sources,
fixed111 defining origins and79 original-map/structural-input consumers,
warning-free with unchanged production and dependency hashes. The actual
coarse target and explicit universe scopes were retained.
