# The original acyclic-to-relative diagram

`AllWeak/RelativeInclusion.lean` constructs the literal functor from actual
relative rows for `AllWeak.nested (acyclicStructure N)` to the original
relative rows for N. It applies the original acyclic inclusion to every
unchanged one-longer quotient component and natural-transformation map.

The target tail's acyclicity comes directly from each source component's
actual acyclic-object witness. Fine exactness is proved through accepted
genuine row postcomposition and the actual fully faithful relative
inclusions. No saturation or extension axiom is needed for this categorical
construction, its original tail square, chosen-zero row, ordinal naturality,
or split-fiber square. The latter is proved using the original finite
zero/object/zero oneChain and oneEmbedding; no alternative split section is
substituted.

In the explicitly common-universe S-model, the source proves:

- `relativeInclusionSRows_tail`: the original tail square through the actual
  `ordinaryRowsInclusion (acyclicStructure N)`;
- `totalFiberInclusion_relativeInclusion`: the original total split-fiber
  square through the original fine acyclic inclusion;
- `relativeInclusionTotal_zeroSimplex` and `relativeInclusionTotal_basepoint`:
  literal preservation of the original all-zero simplices and total point;
- `relativeInclusionTotal_coarseEvaluation`: the strict original
  coarse-evaluation square, with the original all-weak-source acyclic
  inclusion as its bottom map. Only this last square invokes the original
  coarse extension axiom and coarse two-out-of-three, needed by its existing
  exact-map endpoints.

The categorical portion retains independent object and hom universes.
The original total S-maps retain the explicit common-universe restriction.
No global relative fiber theorem, loop equivalence from the acyclic
realization, fiber exchange, or whole-nullhomotopy compatibility follows
merely from these strict diagram squares. Those remain separate proofs.

The warning-free focused source check is
`logs/all-weak-relative-inclusion-check.log`. Recursive origins and original
maps, fine exactness, both strict squares, zeros, basepoint, ordinals and
arbitrary-scheme categorical consumers are checked in
`audits/AllWeakRelativeInclusionAudit.lean`. The final fixed23-origin audit and all16 consumers pass warning-free in
`logs/all-weak-relative-inclusion-audit-final.log`, using only the standard
three axioms recursively. Production hashes match
`logs/all-weak-relative-inclusion-sources.sha256`. Independent fresh-source review is accepted: all23 origins and22
strengthened consumers passed warning-free with all prerequisite hashes
unchanged; see `docs/REVIEW_20261009_ALL_WEAK_RELATIVE_INCLUSION.md`.
