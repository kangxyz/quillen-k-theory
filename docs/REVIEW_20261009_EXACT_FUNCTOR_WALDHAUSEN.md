# Independent review: exact-functor Waldhausen adapter and Q/S naturality

2026-10-09. Lean 4.34.0; mathlib revision
`5ed2965256430c3649e86755f9576b54eca72435`.

## Verdict and scope

**Accepted:** actual preservation of arbitrary pushouts along inflations,
the complete structural Waldhausen exactness adapter, and unconditional
canonical Q/S naturality for the two original K-map APIs, within the
universe scope below. No semantic or kernel-assumption blocker was found.

The frozen four-module scope is recorded in
`logs/exact-functor-waldhausen-sources.sha256`:

1. `Quillen/CategoryTheory/ExactCategory/MatrixInflation.lean`
2. `Quillen/CategoryTheory/ExactCategory/FunctorPushout.lean`
3. `Quillen/Waldhausen/ExactFunctor.lean`
4. `Quillen/Waldhausen/QuillenComparison/ExactNaturality.lean`

All four complete sources and the relevant exact-category, matrix-deflation,
biproduct, structural Waldhausen, and based-naturality dependencies were
inspected. The reviewed production sources are unchanged.

## Exact endpoints and limits

`ExactFunctor.map_isPushout` proves that an arbitrary genuine additive,
conflation-preserving exact functor preserves **any actual pushout along an
admissible monomorphism**, with all four original mapped arrows and all four
original mapped objects retained. It does not require an ambient abelian
category, balancedness, weak idempotent completeness, a functor equivalence,
existence of arbitrary pushouts, or an extra preservation hypothesis.

`ExactFunctor.waldhausenExact` derives every field of the existing structural
`Waldhausen.IsExact` predicate for the existing `ofExactCategory` structures:
zero preservation, inflation preservation, isomorphism preservation, and
pushout preservation. The last field uses the newly proved theorem. The
predicate is not weakened or replaced.

The final `comparisonKEquiv_exactFunctor_naturality F n` proves

```lean
(comparisonKEquiv ED n).toMonoidHom.comp (Waldhausen.KMap F.waldhausenExact n) =
  (F.KMap n).comp (comparisonKEquiv EC n).toMonoidHom
```

for every `n : ℕ` and genuine exact functor `F`. There is **no additional
`IsExact`, chosen-zero equality, naturality-square, or comparison-equivalence
hypothesis**. Both homomorphisms are the already-defined original K-map APIs,
with their actual canonical zero normalization. The comparison equivalence
is the previously proved canonical Q/S equivalence.

The structural results allow source and target categories to have distinct
object and hom universes `(u,v)` and `(u',v')`. The final K-map square uses a
common object universe and a common hom universe, with these two independent,
matching the existing K-map APIs. No raw cross-universe K-theory comparison
is claimed. This is an exact-category Q/S naturality result, not a proof of
Gillet–Waldhausen or a strict-/locally-perfect comparison.

## Matrix admissibility is proved

`isPushout_biprod_map_left` constructs the actual universal property of
adding an unchanged summand. `inflation_graph` proves that the graph
`(1,f) : A ⟶ A ⊞ T` is admissible by exhibiting it as the actual kernel of
`(-f,1)`. The latter map is admissible by the existing matrix-deflation
lemma and the admissibility of the identity. This uses exact-category
axioms and explicit universal properties, rather than a blanket assumption
that every split monomorphism is admissible.

For `i : A ⟶ B` admissible and arbitrary `f : A ⟶ T`, cobase-change
stability makes `i ⊞ 1` admissible. Composing it with the graph proves
`inflation_biprod_lift`: the actual map `(i,f)` is admissible. In particular,
`(i,-f)` is admissible, as needed for the pushout difference sequence.

## Actual pushout/cokernel conversion

For a commutative square `i ≫ g = f ≫ j`, `pushoutShortComplex` has
literal objects `A`, `B ⊞ T`, `P` and literal maps `(i,-f)`, `(g,j)`.
Independent consumers check both map formulas by `rfl`.

`isCokernelOfBiprodPushout` proves the actual cokernel universal property:
a map annihilating `(i,-f)` gives compatible maps from `B` and `T`, and the
supplied pushout's universal property yields the unique map from `P`.
Conversely, `isPushoutOfBiprodCokernel` constructs a pushout's universal
factorization from this cokernel property, including its uniqueness.
Neither direction assumes the other as an unproved bridge.

The difference map's proved admissibility and cokernel uniqueness place
this **actual** short complex in the source exact structure. The imported
`conflation_of_inflation_of_isCokernel`, although located in a K-theory file,
was inspected: it only transports the defining inflation conflation through
the unique cokernel isomorphism and `iso_closed`. It assumes no K-theory
comparison or homotopy conclusion.

The genuine exact functor maps this conflation to a target conflation.
Its canonical `mapBiprod` isomorphism identifies the image middle object
with the biproduct of the image objects. The two component equations use
actual preservation of the biproduct lift/desc maps and of negation.
Transporting through this explicit short-complex isomorphism gives the
cokernel property for the **original mapped square**. The converse
pushout/cokernel lemma then proves the desired pushout universal property.

## Based canonicality

The final module applies the independently reviewed
`comparisonKEquiv_naturality_KMap` to the newly constructed
`F.waldhausenExact`. Thus the structural witness previously left separate
is now actually discharged from exact-functor data. The underlying
normalized S-map remains actual S-diagram postcomposition, and agreement
with the original Waldhausen K-map is checked by an additional consumer
using this generated witness. No definition transports the Q-map through
the desired equivalence to manufacture the S-map or the commuting square.

## Independent verification

Each source is freshly compiled in dependency order into a separate olean
overlay. All four original oleans are excluded; unchanged dependency
artifacts are linked in. The overlay is first in `LEAN_PATH` for every
source check and audit, and import resolution is logged. Compiler calls
use `lean -j1` under `/tmp/quillen-lean-slot-1.lock`, with acquisition times.
The four fresh source checks completed without warnings or errors.

The independent audit is fixed at **17 defining-origin declarations**,
including private/generated constants, with recursive axiom collection
allowing only `propext`, `Classical.choice`, and `Quot.sound`. Additional
consumers check matrix admissibility, actual difference-map formulas, the
cokernel universal property, separate-universe pushout/structural exactness,
and common-universe equality/naturality for the original K-map APIs.

The final independent audit and every consumer passed without warnings
or errors. The 17 audited declarations comprise 3 matrix-inflation,
12 pushout, 1 structural-adapter, and 1 final-naturality declarations.
All four reviewed sources and all eight inspected dependency hashes still
match. Import-resolution logs confirm use of every fresh reviewed olean. Evidence directory:
`logs/exact-functor-waldhausen-independent-20261009/`.
Audit source: `audits/ExactFunctorWaldhausenIndependentAudit.lean`.


SHA256:

```text
b10b2521dfb786f9a577033ad515157ab8cf891d0d1bdcb9cb2eb591b23f7315  Quillen/CategoryTheory/ExactCategory/MatrixInflation.lean
20b9c6efd2555f69c357754cad829d39559eddef799ce179070fc455b9305e3f  Quillen/CategoryTheory/ExactCategory/FunctorPushout.lean
92ec01f7e9f58ef6d19ddc8d3500bdc8bcf9a220f25c1cc2d5c0130a832d590c  Quillen/Waldhausen/ExactFunctor.lean
54b30e7e07b061ee96ca00265ddd81e7dac0f04339d1d17a86cef3bdbff7e0d8  Quillen/Waldhausen/QuillenComparison/ExactNaturality.lean
8b0278c6327ebd2e49644bf683a1cf713af2112bb571c40767279b6aae57f1a7  audits/ExactFunctorWaldhausenIndependentAudit.lean
6f7cd416c6a8a5929db9013a68de5622b1168b799bf190dad804aea07e995bcb  logs/exact-functor-waldhausen-independent-20261009/sources.sha256
9b2cbad27c1729c457572093fc3d6af7ccfdf9d4b084d8190a4dbb06a880f3db  logs/exact-functor-waldhausen-independent-20261009/origin-axioms-and-consumers.log
302973310e86ea388a27a240655afabaca42c9aa59a38c813fa0583c4c539259  logs/exact-functor-waldhausen-independent-20261009/import-resolution.log
0d267bb1140595b99a121bc92a61ccc9e409fa885809aef92437d1fc1bd57dd5  logs/exact-functor-waldhausen-independent-20261009/inspected-dependencies.sha256
```

Final source and dependency rechecks are `post-audit-hashes.log` and
`post-dependency-hashes.log`. The independent review changed no production
source.
