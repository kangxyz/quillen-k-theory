# Independent review: generic bisimplicial realization invariance

Reviewed independently of the implementation authors on 2026-10-09. Frozen
scope: seven modules in `logs/bisimplicial-realization-sources.sha256`.

## Accepted contract

For arbitrary bisimplicial sets and an actual bisimplicial map, actual
homotopy equivalences on every row imply an actual homotopy equivalence
of diagonal realizations. The forward map is exactly the realization of
the specified diagonal map. No compatible selection of rowwise inverses,
groupoid condition, dimensional bound, or claimed weak-to-strong upgrade
is an input.

## Semantic review

- Outer latching subcomplexes are the actual finite unions of degeneracy
  images. Every degeneracy is monic because its face gives a retraction.
- The preimage of the preceding union under the next degeneracy is proved
  exactly equal to the corresponding lower-dimensional union, using actual
  face/degeneracy identities, including repeated vertices and zero cases.
  This supplies genuine finite pushouts; arbitrary union gluing is not assumed.
- Latching-map realization equivalence follows by nested finite induction
  from lower rows and these mono pushouts, with the specified maps retained.
- The outer skeleton uses full coefficient rows and actual evaluation maps
  into the diagonal. Pointwise comparison with each ordinary outer skeleton
  proves exhaustion and a genuine sequential colimit.
- The enriched attachment is precisely the union of the latching cylinder
  and the boundary cylinder. Its exact preimage characterization distinguishes
  degenerate coefficient simplices from nonsurjective simplex operators.
  Eilenberg–Zilber uniqueness proves injectivity away from the attachment;
  it is not replaced by an unjustified injectivity claim on whole rows.
- The successor square and the internal union square are actual simplicial
  pushouts. All maps and naturality squares are supplied and preserve the
  canonical diagonal map.
- Realization products are used only with locally compact factors, here
  finite standard simplices and their boundaries. The proof does not assume
  unrestricted preservation of topological products by realization.
- Actual monomorphism realization HEP supplies every cofibration needed by
  finite homotopy gluing and the proved coherent sequential invariance
  theorem. The final inverse is a genuine topological homotopy inverse.

No semantic correctness blocker was found. This theorem supplies a general
topological input to Q/S and perfect-model comparisons; it does not by
itself prove their rowwise algebraic equivalence hypotheses.

## Independent verification

The current-source command
`lake --rehash build Quillen.Topology.Realization.BisimplicialEquivalence`
passed with 2,049 jobs on the pinned toolchain. The independent audit
`audits/BisimplicialRealizationIndependentAudit.lean` then passed all **164**
origin declarations, including private/generated helpers, recursively
allowing only `propext`, `Classical.choice`, and `Quot.sound`.

Additional arbitrary-universe consumers check the exact forward-map identity
by `rfl` and the proposition-level diagonal conclusion from row hypotheses.
Both build and audit exited with code 0. All seven source hashes matched
before and after the checks. No proof source was modified by the review.

Evidence: `logs/bisimplicial-independent-build.log`,
`logs/bisimplicial-independent-all-axioms.log`, and
`logs/bisimplicial-independent-final-hash-check.log`.
This is focused acceptance; the delivered 04:11 archive excludes this later
scope. Public integration and later immutable verification remain separate.
