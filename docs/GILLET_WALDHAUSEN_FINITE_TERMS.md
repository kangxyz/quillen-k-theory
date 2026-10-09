# Genuine finite termwise K-decomposition

## Contract

Four new modules retain the original complexes, functors, and maps:

- `FiniteTermFiltration`: the original brutal truncation and single-term
  quotient are exact endofunctors of each actual term-bound stratum. Their
  original adjacent maps give genuine structural cofibration sequences;
  their actual endpoints are naturally identity and zero.
- `FiniteTermEvaluation`: original term evaluation and original single-complex
  insertion are exact. Their actual composites are naturally identity in the
  same degree and zero in other degrees. Evaluation followed by insertion
  is the original single-term layer.
- `FiniteTermKFormula`: the independently proved canonical literal additivity
  theorem is finitely iterated inside the original stratum. The actual
  identity K-map becomes the finite product of the original layer K-maps,
  in the existing group multiplication, including K₀.
- `FiniteTermKEquivalence`: evaluation and insertion are assembled into the
  genuine mutually inverse group maps described below.

For an abelian category A and an object predicate P containing zero, replete,
and extension-closed, the endpoint is

`finiteTermKEquiv P a m k`.

Its source is the actual isomorphism-weak Waldhausen K-group in degree k of
bounded termwise-P complexes with actual zero terms outside `[a,a+m-1]`.
Its target is the finite product, indexed by `Fin m`, of the original
isomorphism-weak K-group of the inherited exact category P.

The forward component at i is definitionally the original public normalized
`KMap` of evaluation at `a+i`. The inverse is literally the finite product of
the original public `KMap`s of single-complex insertion at those degrees.
The source reassembly identity is proved by genuine finite structural
additivity. The target identity is proved using the original same-degree
identity and different-degree zero natural isomorphisms. Empty intervals
(`m=0`) and degree zero (`k=0`) are included.

No equivalence, additive-map identity, categorywide uniform bound, kernel
closure, projectivity, or geometric resolution hypothesis is an input.
These are the inherited ordinary-cofibration isomorphism weak models.
Brutal truncation is not claimed to preserve quasi-isomorphisms. No global
graded decomposition, acyclic-cycle decomposition, fibration, or
Gillet–Waldhausen comparison is asserted by this four-source boundary.

## Universes and schemes

The pure algebra and finite endofunctor K-map formulas allow independent
object and morphism universes. For the mixed evaluation/insertion K-map
interface, the final equivalence explicitly uses
`A : Type (max u v)` with `Category.{v} A`. It does not assume an unproved
universe-change comparison.

For an arbitrary scheme `X : Scheme.{u}`, the actual application is
`finiteTermKEquiv.{u,u+1} (SchemeSheaf.finiteLocallyFree X) a m k`.
The explicit universe annotation is needed by Lean to resolve the maximum;
there is no noetherian, regularity, resolution-property, or global-projectivity
hypothesis. The generic bounded-term predicate is the already accepted actual
strict-perfect predicate on X.

## Verification evidence

The frozen source manifest is
`logs/gillet-waldhausen-finite-term-k-checked-sources.sha256`.
All four focused builds are warning-free, in
`logs/gillet-waldhausen-finite-term-{filtration,evaluation,kformula,kequivalence}-build.log`.
The two new local finite-product instances have explicit module-specific
names, preventing collision with previously frozen independently imported
modules.

The independent review freshly rebuilt all four sources and passed exactly
111 new declaration origins, split 39+34+6+32, with only `propext`,
`Classical.choice`, and `Quot.sound`. It checked original forward maps,
literal inverse products, both inverse identities, empty intervals in every
degree, explicit K₀, and arbitrary schemes. All four and the preceding
thirty source hashes match.

The authored aggregate driver is `audits/GilletWaldhausenFiniteTermKAudit.lean`.
Its final fixed772 all-thirty-four-source recursive audit and all consumers
passed, including the explicit arbitrary-scheme application, with no errors,
warnings, or `sorryAx`. Only the three standard logical axioms occur. The
terminal raw log is `logs/gillet-waldhausen-finite-term-k-axioms.log`.
All preceding thirty source hashes and the frozen four hashes match.

Independent acceptance is recorded in
`docs/REVIEW_20261009_GW_FINITE_TERM_K_EQUIVALENCE.md` and
`logs/finite-term-k-independent-20261009/`. The authored artifacts are hashed
by `logs/gillet-waldhausen-finite-term-k-artifacts.sha256`.
