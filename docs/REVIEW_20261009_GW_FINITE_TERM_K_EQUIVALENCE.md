# Independent review: genuine finite-term K-equivalence

Date: 2026-10-09. Result: **accepted for the corrected frozen four-source finite-term endpoint**.
No implementation source was changed by the reviewer.

## Exact endpoint and universe contract

The four-source boundary constructs `finiteTermKEquiv P a m k` for the actual
finite term stratum `[a, a + m - 1]` of cochain complexes whose terms satisfy `P`.
The stratum is the original full subcategory of actual bounded termwise complexes,
with actual zero terms outside that interval. It retains their original
differentials and all chain maps. Its exact structure is inherited from actual
ambient short exact sequences, and its weak equivalences are **isomorphisms**.

Inputs are an abelian category, `P.ContainsZero`, repleteness, and closure of `P`
under the ambient exact extensions. Finite-product closure is derived. There is
no kernel closure, projectivity, acyclicity, globally uniform bound, or supplied
K-equivalence/additivity conclusion.

The first three modules retain independent `A : Type u`, `Category.{v} A`.
The final mixed evaluation/insertion K-map module explicitly requires
`A : Type (max u v)`, `Category.{v} A`, so the term category and complex stratum
fit the existing common-object-universe KMap API. This is the actual theorem's
scope; no raw cross-universe transport is claimed. An independent universe probe
confirms parameter order `[v,u]`. For `X : Scheme.{u}`, the explicit specialization
is `finiteTermKEquiv.{u,u+1} (SchemeSheaf.finiteLocallyFree X) ...`.

The forward map is definitionally the tuple of the original degreewise evaluation
KMaps at `a+i`, `i : Fin m`. The inverse is definitionally the literal finite
product of the original single-complex insertion KMaps at those same degrees.
Neither map is substituted by an abstract inverse or conjugated through a
pre-assumed equivalence.

## Mathematical audit

I read all four complete sources and the actual brutal-truncation layer,
fixed-bound, exact-functor-sequence, and literal K-group multiplication dependencies.

- Original brutal truncations stay in the same specified term-bound stratum
  because their original term maps are monic into the old terms. Original
  single-term layers retain those bounds via their actual termwise epimorphisms.
- The original adjacent inclusion and projection form the actual ambient
  short exact sequence. Exact truncation/layer functors and this actual sequence
  derive all structural cofibration-sequence inputs to additivity, including
  the relative condition. No additivity statement is a hypothesis.
- At the lower endpoint, the natural isomorphism uses the original brutal
  inclusion. Above the upper bound, the actual truncation is naturally zero.
  These give the original identity and trivial canonical KMaps.
- Iterated genuine structural additivity expresses every finite-stratum class
  as the product of its original single-term layers. `KCommGroup` extends exactly
  the existing homotopy-group `Group`; it adds the proved commutativity law and
  does not replace multiplication, identity, or inverse, including at K₀.
- Evaluation and insertion are genuinely exact. Same-degree insertion followed
  by evaluation is naturally the identity using the original single-term
  identification; at any different degree it is naturally zero. Evaluation
  followed by insertion is the original layer functor.
- These actual composites give the delta K-map identities. The first inverse
  identity follows from finite layer additivity, and the second from evaluation
  of the literal product and those delta identities. Thus the resulting
  `MulEquiv` is proved, with the exact displayed forward and inverse maps.

`m=0` is included without an `a≤b` hypothesis: the interval is empty, the inverse
is the empty product, and the same lower/upper endpoint argument proves every
class trivial. All results include `k=0`, using the existing fundamental-group
K₀ definition rather than a formal Grothendieck-group placeholder.

## Integration repair and verification scope

Before freezing, the author's aggregate audit and the reviewer both detected a
real declaration collision: anonymous local finite-product instances in the new
files could receive a name already used by the separately imported TruncationLayer.
The author gave the two new instances explicit unique names. Previously frozen
sources were untouched. The corrected boundary is the only one accepted here.

All four corrected sources were freshly rebuilt in manifest order into an
isolated overlay. Other unchanged dependencies were linked; no production olean
was replaced. Checks use Lean 4.34.0 and `-j1` under the specifically assigned
slot2 lock, with acquisition logging. All thirty prior frozen GW source hashes
were reconstructed without conflicts and checked before building.

## Final independent verification

`audits/FiniteTermKIndependentAudit.lean` passed its fixed **111-origin** guard:
39 Filtration, 34 Evaluation, 6 KFormula, and 32 KEquivalence declarations. It
checks every exact defining-module origin, including private/generated constants,
recursively permitting only `propext`, `Classical.choice`, and `Quot.sound`.
The earlier independently frozen GW modules are explicitly imported together,
so the repaired integration collision is tested as well.

All **19 example consumers and the arbitrary-scheme definition** passed without
warnings. These cover closure-minimal raw term-bound retention and actual single
short exactness, original truncation/evaluation/insertion maps, the original
lower-endpoint inclusion, the actual structural layer sequence, literal finite
multiplication, the precise mixed-universe equivalence, original forward maps,
the inverse expanded completely into the literal product of original insertion
KMaps, both inverse identities, every-degree empty-stratum triviality, the
explicit empty K₀ case, and the original isomorphism weak predicate.

The arbitrary-scheme definition uses the explicit verified universe arguments
`{u,u+1}` and has only the standard three axioms. A separate rfl consumer identifies
`boundedTerms (finiteLocallyFree X)` with the existing actual `strictPerfect X`
object property. Neither consumer supplies regularity, noetherianity, a resolution
property, kernel closure, or any K-equivalence. All four frozen hashes and all
thirty prior GW source hashes match after the audit.

## Limits

This is a genuine finite-stratum, isomorphism-weak K-equivalence. It is not a
category-level splitting of arbitrary complexes, preservation of quasi-isomorphisms
by brutal truncation, a global graded decomposition of the whole bounded category,
a change-of-weak-equivalence fibration, or a Gillet–Waldhausen theorem.

The arbitrary-scheme consumer concerns actual finite strict-perfect isomorphism-
weak strata and the actual finite locally free term category. It uses no
noetherian, regular, resolution-property, or global-projectivity input. It does
not identify these factors with the public small-model `Scheme.K` or establish
a quasi-isomorphism/perfect comparison.

## Frozen source boundary

- `Quillen/Waldhausen/GilletWaldhausen/FiniteTermFiltration.lean`:
  `1ef4a5f5d3e87cdd1e48c72cacadb016f4e9b570ea3de59aaea22046e3e5aab9`
- `Quillen/Waldhausen/GilletWaldhausen/FiniteTermEvaluation.lean`:
  `e8ff1b150aacf8fb768b4d882b88d9710738940f1e39417181cd3950b865d00f`
- `Quillen/Waldhausen/GilletWaldhausen/FiniteTermKFormula.lean`:
  `638651b5e2b73df4e7264aa80530db3c6a0e218d387f60a17f9a958306c15853`
- `Quillen/Waldhausen/GilletWaldhausen/FiniteTermKEquivalence.lean`:
  `510767118f40e43113c5377215d722835039ddf4980003da8d365fb00ca67c55`

Manifest: `logs/finite-term-k-independent-20261009/sources.sha256`.
Manifest SHA-256:
`7beebfb10691060e5b54fadcaba45e89c69b164408ae853c74d24d53d445c925`.


Evidence directory: `logs/finite-term-k-independent-20261009/`.
- `check.log`: four warning-free isolated fresh source checks
- `audit.log`: fixed111 recursive origin audit and all strengthened consumers
- `deps.log`: fresh selected import resolutions
- `universe-probe.log`: the exact exported mixed-universe type and parameter order
- `hashes-before.log`, `hashes-after-build.log`, `hashes-after-audit.log`: frozen4 rechecks
- `prior-sources.sha256`, `prior-hashes-before.log`, `prior-hashes-after-audit.log`: unchanged prior30
- `artifacts.sha256`: exact report/audit/probe/script/log/fresh-artifact hashes

The ordered build and slot2 acquisition are recorded in
`logs/finite-term-k-independent-session.log`; the audit records its own acquisition.
No live Lake rebuild or production artifact replacement was used.
