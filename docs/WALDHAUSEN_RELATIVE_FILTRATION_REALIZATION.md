# Original relative-filtration realization

The original relative S-construction is compared to genuine mixed
cofibration chains by the original grid/weak-row presentation, the actual
relative-inner-S interchange, and the original initial-filtration functor.
The resulting map preserves both original row restrictions strictly.
Taking the last diagonal uses the literal identity on all three indices.
The accepted bisimplicial realization theorem is applied twice, with the
original forward map retained in each application.

Only the coarse extension axiom is needed here. Categorical diagrams retain
independent object/hom universes; raw S-map realization retains its explicit
common-universe scope. No cylinder, saturation, fiber equivalence, or
naturality of chosen inverses is an input. This endpoint alone does not
prove the global homotopy-fiber or Gillet–Waldhausen theorem.

Author audit: `audits/RelativeFiltrationRealizationAudit.lean`, fixed
44 origins (16 + 28), 18 consumers, only the three standard Lean axioms.
The independent review strengthens this to 25 consumers:
[review](REVIEW_20261009_RELATIVE_FILTRATION_REALIZATION.md).
Source fingerprint: `logs/relative-filtration-realization-sources.sha256`.
