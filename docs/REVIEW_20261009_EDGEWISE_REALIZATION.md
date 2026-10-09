# Independent review: edgewise realization

Reviewed independently of the endpoint author on 2026-10-09. Scope: the five
modules in `logs/edgewise-realization-sources.sha256`, 697 source lines.

## Accepted contract

For every simplicial set X, the actual ordinal edgewise subdivision
`[n] ↦ [n]ᵒᵖ ⋆ [n]` has a realized homotopy equivalence to |X| whose forward
map is exactly the realized second-half endpoint. Its naturality and the
image of the degenerate interval representing any chosen vertex are proved.
No dimension, connectedness or finiteness assumptions are imposed on X.
The theorem does not assert that this endpoint map is a homeomorphism or
that its selected inverse is canonical, simplicial, or naturally selected.

## Semantic review

- The join and reversal formulas define the genuine edgewise ordinal functor.
  The second-half inclusion is natural, so its contravariant action is an
  actual simplicial comparison rather than a levelwise family without coherence.
- The representable contraction is an explicit all-degree simplicial cylinder.
  Its first half decreases to zero using the reversed interval coordinate;
  its second half increases to the last vertex. Monotonicity across the join
  and naturality for all simplicial operators are proved. Both cylinder
  endpoints identify the actual identity and constant simplicial maps.
- The realized contraction proves contractibility of each subdivided simplex.
  The comparison equivalence on each representable is derived from actual
  source and target contractions; it is not an assumed comparison field.
- The mono-realization HEP lemma applies the proved relative cell lifting
  theorem to actual compact-open path evaluation. It does not assume every
  topological quotient map is a cofibration.
- The cellular criterion uses actual simplicial skeletal attaching pushouts.
  Boundaries are supplied by lower-dimensional induction, with their genuine
  dimension bound. Cocontinuity and preservation of monomorphisms supply
  the required pushout and HEP hypotheses on both sides.
- Infinite-dimensional X is handled by the actual exhaustive sequential
  colimit with HEP transitions and the already proved coherent sequential
  homotopy-invariance theorem. The resulting inverse is an actual homotopy
  inverse, not an upgrade from weak equivalence without a theorem.
- Forward-map identities survive every gluing step. The naturality square
  is the realization of endpoint naturality; the chosen-basepoint formula
  uses the genuine simplicial degeneracy/face identity.

No mathematical correctness blocker was found in the stated scope.
This result does not itself prove Quillen Q / Waldhausen S comparison.

## Independent current-source verification

`lake --rehash build Quillen.Topology.Realization.EdgewiseRealization`
passed on the pinned Lean/mathlib environment with 2,048 jobs. All five new
source modules were rebuilt. The log is `logs/edgewise-independent-build.log`.

`audits/EdgewiseIndependentAudit.lean` then passed every one of the **108**
declarations originating in these exact five modules, including private and
generated declarations. It recursively rejects every axiom beyond
`propext`, `Classical.choice`, and `Quot.sound`. Its additional arbitrary-
universe examples verify the definitionally unchanged forward map, exact
chosen-vertex image, and naturality. The complete run exited with code 0;
log: `logs/edgewise-independent-all-axioms.log`.

All five frozen source hashes matched after the independent audit. Public
integration and immutable archive verification are separate checks. No proof
source was modified by the review.
