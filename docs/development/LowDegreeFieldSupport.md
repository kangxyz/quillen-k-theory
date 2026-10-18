# Low-degree field and finite-support foundations

This is the implementation and proof plan for the arithmetic-curve request
prepared on 2026-10-18. It records the native constructions and the remaining
proof routes.
The stated native Q1--Q3 constructions and Q6 finite-field K2/G2 vanishing are
proved. Q7 supplies the original kernel-intersection and finite-residue generic
G2-injectivity consequences; finite-family boundary lifting retains its separate
generic-G1-injectivity hypothesis. Q4 comparison injectivity and positive marking,
and Q5 origin-DVR unit generation, remain substantial mathematical obligations.

## Source basis and execution boundary

The investigated Quillen baseline is
`16cc1d011ef6d9c28b045879be10617411a0c2b4`, with Lean `v4.34.1`, mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, and Aglib
`25c37780264f0da94f5bb6bd31cc089d26f2da80`. The independent Quillen worktree was
clean before this task. At the user's subsequent request, the root and maintained
downstream manifests now select Aglib
`16aa08a90198d76be0bec47dd640b5c992acd9d7`, with the same Lean and mathlib pins.
The former dependency directory, including its nine unrelated guidance and
tooling edits, is preserved intact in the task's external scratch backup.
The new dependency is pristine. Its supplied Milnor interfaces are used directly;
only the additional finite-field and tame-kernel proofs remain Aglib candidates.
The relevant existing Quillen comparison artifacts are present locally;
their presence is a cache candidate, not a substitute for checking source and
trace compatibility during a focused build.

Implementation now takes place in the dedicated Git worktree
`tmp/output/quillen-low-degree-foundations` of the surrounding workspace, on
`codex/low-degree-field-support`. The previous Quillen worktree is clean on
`main`. Task-owned source was transferred with matching SHA256 values;
dependencies and build outputs were cloned independently. The later Aglib
upgrade preserves matching local artifacts and lets current Lake input checks
select the affected compilation closure.

The original investigation used R5 source baseline
`1b7c3945394bcc27a94d1ebf86df702b0291ee18`; the later separately checked
adapter proposals use the live R5 baseline
`d34faaf9c80b457a4afe0ee9589acf378b1c8dac`. Its dependency checkout is a
different Quillen revision, `c73a12d54e59297d8acf3a7f0046fcf87e5f0ebb`.
The subsequent rule-source update to
`959fb044206b188c9b7cd66404b2b37b84fad8b0` changes guidance and CLI files only;
the adapter source files, toolchains and dependency pins retain their identities.
R5 source, manifests, and its Quillen package checkout remain read-only.
At resumption, the governing R5 guidance is reconciled with
`a9236feda5b7c1acdf52d7eda3941b35672c41b4`. Its shared coordination entry is
`infra/ORCHESTRATION.md`; the relevant formalization, execution and host-routing
sections are unchanged from the accepted rule source above. This guidance
identity is separate from the mathematical source and dependency snapshots.
Downstream retargeting is returned as a separate patch. Source references below
are exact module/declaration locators, not permission to change their owners.

Follow [Contributing](../../CONTRIBUTING.md),
[Architecture](Architecture.md), and the
[Aglib candidate convention](../../Quillen/Aglib/README.md).
General family/category results belong in the designated candidate subtree;
Q/S maps and K-comparisons remain in Quillen. Keep one implementation of each
general family object. Migrate the existing general R5 construction, with an
explicit namespace comparison when necessary, instead of creating a competing
finite-family model. Quillen must never import R5.

## Current construction boundary

| Target | Supported current result | Remaining acceptance or mathematics |
| --- | --- | --- |
| Q1a | Actual all-field stable determinant, elementary kernel, quotient equivalence and ring naturality; independent mathematical review accepted | Original matrix-cube marking belongs to Q1b |
| Q1b | All-field original upper finite-module determinant, literal scalar-extension square and `moduleDetEquiv_matrix_cube`, including rank zero; normally compiled and independently accepted | The validated original R5 consumer patch remains unapplied; full R5 integration is separate |
| Q2 | `Quillen.FiniteSupport.decompositionKEquiv` in every positive degree, original evaluation/inclusion laws and finite-sum inverse; independent mathematical review accepted | Retain scoped final checks at the delivered source identity; no K0 decomposition is claimed |
| Q3, Dedekind modules | Native SmallModel primary transport, all-degree point dévissage, positive `residueFieldAssemblyKEquiv` and original support/ambient pushforwards; independently accepted | R5's actual sheaf-stalk boundary transport remains separate |
| Q3, finite closed support | Locally Noetherian finite-S splitting and finite-family equivalence; on Noetherian schemes, actual upper coherent support and public field-scheme assembly in every positive degree, with original pushforwards; accepted and normally compiled | Application-specific R5 integration remains unapplied |
| Q4 | Direct Aglib Milnor interfaces; universal central lifting; all-rank generation of the original Steinberg kernel by ordered defects; field-natural surjective canonical Milnor maps to original right-projective and upper finite-module K2, with explicit module transport and proved actual fiber perfectness; independently accepted | Milnor-map injectivity, injectivity of the original Steinberg/fiber comparison, comparison isomorphism and positive product marking |
| Q4, topology | General actual homotopy-fiber perfectness from path-connected perfect-pi1 source, simply connected target and surjective integral H2; original stable-zero fiber perfect over every ring via constructed covering/homology data; independently accepted | Universality/injectivity of the central-extension comparison is a separate Q4 obligation |
| Q5, identity operations | Original scalar operations and signed boundaries; positive principal K0 calibration and ordered principal/local-DVR unit-uniformizer formulas, retaining a supplied fraction field; cross-universe action/cube transport, bilinear field products and unit-unit boundary zero; independently accepted | Reversed ordered input, Steinberg relation and Milnor/product marking |
| Q5, DVRs | Actual-DVR Milnor tame kernel equals the unit-symbol span on supplied Aglib objects, including the canonical uniform residue; split-residue DVR generic G-map injectivity; actual-origin section and trait G/K injectivity proposal independently accepted | Quillen unit-pair generation still needs marked comparison and boundary compatibility |
| Q6 | For every finite field, original right-projective K2, upper/lower finite-module K2/G2 and literal public G2(Spec F) are trivial; independent review, normal builds and F2/F3/F5 clients passed | No higher finite-field groups or Matsumoto injectivity are claimed |
| Q7, native modules and schemes | Original boundary-coordinate kernel intersections and finite-family lifting under explicit generic-G1 injectivity; finite residue fields give original native/public generic G2 injectivity, retaining supplied fraction fields; principal scheme/local-DVR comparison in all degrees | Arithmetic generic-G1 injectivity remains separate; distinct R5 stalk/application retargets remain unapplied |

The Q2 validation includes strict changed-leaf compilation, 15 scoped environment
linters and native text lint on its nine defining modules (including stable
algebra), a scoped standard-foundation audit, semantic regression properties,
and an independently configured upper-universe client using the same pins.
The checked source does not add custom axioms or proof placeholders. The
earlier standalone client check used a scratch manifest with the exact root
pins. The subsequent authorized dependency upgrade also aligns the maintained
downstream manifest with the new root Aglib pin.

The earlier quotient-to-Q comparison package has its nine-module scoped lint
pass. The primary categorical module has a focused build, scoped lint and
independent mathematical verdict. The completed marking and residue extension
passed scoped environment and native text lint for 33 modules and 1575
declarations, using all 15 selected linters. Its standard-foundation audit
checked 1628 declarations from 34 defining origins, including private and
generated declarations, allowing only `propext`, `Classical.choice`, and
`Quot.sound`. The additional affine-localization origin and two downstream
clients passed the same audit for 35 declarations in three origins. Together
with the earlier audits, these cover every new defining module in this
milestone. The two clients also passed scoped environment and native text lint.

At the `8203f54d` milestone with Aglib `25c3778`, normal aggregate
`lake build +Quillen:olean` completed successfully, and the
generated `QuillenTest` aggregate passed strict compilation. Import generation,
library layout, and source-token checks passed with 4667 production modules
and 1048 trust-test modules. Regression properties include the literal
rank-zero positive cube and a rank-one F5 cube with determinant 2, distinct
from its inverse. The independently configured client retains the literal
positive cube, original tensor extension and determinant square. Dependency
pins and maintained downstream manifests were unchanged at that milestone.
The Aglib upgrade has a separate validation basis: exact Milnor compatibility
and DVR residue leaves, the scalar candidate and its K-action consumer passed
normal focused compilation. Only one modified pre-existing Aglib implementation
lies in the current Quillen import closure, `Modules.Tensor.Sections`; matching
unaffected artifacts are retained. This does not assert a full Aglib-root build.

On the updated basis, the fifteen subsequent scalar, homotopy, Steinberg and
boundary defining origins passed the full standard-foundation audit for 759
declarations. The seven newly uncovered or refreshed lint scopes passed all
15 selected environment linters and native text lint (302 declarations), with
compatible earlier lint evidence retained for the other eight scopes.
The two direct-Aglib Milnor candidates passed normal compilation, independent
ordinary mathematical review, 15 scoped linters and native text checks, and
the complete 33-declaration origin audit. Their old seven-module Quillen
implementation and README were deleted. The maintained independent client
`Consumer.MilnorInterfaces` checks both smallest fields, the actual uniform/
tensor field-map square, the ordered DVR residue and the uniform kernel;
it and the existing field/support clients passed normal compilation under
the aligned maintained manifest.

Subsequent independent batches add 141 audited declarations from the Serre,
base-ring-isomorphism and torus leaves, 40 from actual Steinberg-kernel
centrality, 36 from object-class calibration, and 30 from SmallModel boundary
transport. Each batch has matching strict/normal compilation, scoped native
lint evidence and independent ordinary mathematical acceptance. Together
the current stage covers 23 disjoint defining origins and 1039 declarations;
the additional independent Milnor client has five checked declarations.
This is combined scoped coverage, not a newly run whole-library audit.
The next seven defining origins add 325 audited declarations: universal
Steinberg lifting (82), actual fiber centrality (19), Steinberg symbols (81),
the original fiber/K2 comparison (60), source-contraction boundary geometry
(10), natural-transformation loop cancellation (18), and principal rank-one
module comparisons (55). Each has normal focused compilation, scoped
environment/text lint and independent ordinary mathematical acceptance at
its delivered source identity. The combined current coverage is therefore
30 disjoint origins and 1364 declarations, with the independent five-declaration
Milnor client checked separately. These seven providers were also compiled
together under the updated pins. No perfectness or isomorphism claim for
the actual fiber group follows from these checks.
The next accepted batch comprises eleven new defining modules and two existing
homotopy-fiber modules with generalized universe binders. Principal-object
calibration contributes 172 audited declarations, central-lift surjectivity six,
field/DVR unit products 87, rank-two Steinberg reduction 85, pullback-cover
homology 86, and scalar-universe naturality 56. The five-module field-naturality
scope has a fresh full audit of 75 declarations in normal Lake artifacts;
its earlier overlay inventory had 74. Both inventories passed the same
standard-foundation policy, and the current normal inventory is retained in
full. All scopes have matching focused builds, scoped lint and independent
ordinary mathematical acceptance. The changed universe-binder suppliers and
all five direct Waldhausen/prespectrum consumers passed focused normal builds;
affected new principal/scalar/fiber providers were also refreshed. This is
scoped evidence, not a whole-library replay.
Maintained regression and independent-package consumers retain the literal
integer-2 positive boundary, the unit-1 zero boundary, the canonical lower
field-product cube and a power-series scalar-universe instance. Their exact
normal builds, scoped lint and full six-declaration audit passed. Anonymous
examples were named without changing statements or proofs so the defining-origin
lint runner could select them. Generated imports and source/layout checks pass
for 4925 production and 1114 trust-test modules at this checkpoint.
A subsequent accepted source family supplies the all-rank Steinberg step:
267 defining-origin declarations across parabolic factorization, source-word
Bruhat coverage and kernel descent passed strict compilation, all 15 scoped
linters, native text checks and the full standard-foundation audit. Independent
complex review accepted the same frozen sources. Each provider then passed
its normal Lake build in dependency order, with unchanged source identities.

The next comparison and topology scopes have separate matching evidence:
43 audited declarations for the canonical Milnor/Quillen maps, four for their
generated-kernel wrappers, 36 for the ordered principal unit boundary, 51 for
the actual local-DVR transport, 29 for mixed-universe chains, three for actual
component-cover existence and 25 for the all-ring stable-zero homology setup.
All passed focused normal builds and independent mathematical review.
The shared literal pullback and minimal homology retarget have a fresh normal
lint and full-origin audit of 123 declarations: 24 geometry, 15 fiber and 84
homology. The earlier overlay inventory was 125; the current normal selection
is retained in full, including private and generated declarations.
The canonical comparison's subsequent documentation repair changes only its
module description and one theorem docstring; exact reverse projection matches
the accepted implementation byte-for-byte. Its normal build and the four
wrappers' build passed again, followed by native scoped lint for all 47 declarations.
These scoped checks do not assert fiber perfectness, Milnor injectivity,
positive product marking or unconditional finite-field Quillen vanishing.
The next seventeen-source chain criterion has independent complex review,
normal provider-first builds, and a fresh normal-artifact lint/full-origin
audit for all 336 declarations. Its actual origin names match the frozen
inventory. The three subsequent group, mapping-cylinder and all-ring application
leaves also have independent complex acceptance and normal provider-first builds.
Their fresh normal scoped lint selects 11 declarations; the full-origin audit
selects ten, with the generated congruence-origin coalescence recorded explicitly.
Both inventories are retained without filtering.
`Field.FiniteFieldKTwo` adds eight unconditional finite-field endpoints, with
four named regression declarations and five independent-package consumers.
All seventeen passed the full standard-foundation audit and native scoped lint;
normal provider, regression and separate-client builds passed. The tests include
F2/F3/F5 and the actual canonical lower/public affine coordinates.
`Dedekind.FiniteResidueLocalization` adds fourteen audited declarations and
two regression plus four separate-client declarations. Normal builds and the
fresh twenty-declaration normal lint/audit cover the original localization and
public supplied-field pullbacks, including actual integer and Spec Q to Spec Z
consumers. These results do not assume generic G1 injectivity.
A whole-root incremental attempt was stopped when the changed upstream
tensor leaf expanded into unrelated projective-line developments; its
partial cache progress is retained and no new whole-root pass is claimed.

Integration with main revision `a9f226c6` preserves all changed non-facade
Lean sources byte-for-byte from their owning branch; the proof bodies have
no overlapping changes. Its nineteen new general Aglib-candidate providers
passed normal focused compilation under Aglib `16aa08a9`. A joint strict
import check of those nineteen and the seven new providers also passed.
Regenerated import roots, library layout and source-token checks passed for
4914 production and 1113 trust-test modules. Existing scoped proof evidence
is retained at the unchanged implementation identities; this integration
check is not a new whole-root compilation or audit.
An independent source-only inventory also finds that none of the incoming
224 production or 65 test implementation roots reaches any of the four
changed pre-existing Aglib implementation leaves. It finds no duplicate
upstream path among the nineteen new candidates and no incoming package,
pin or toolchain changes.

The subsequent native Dedekind construction retains the exact
`smallTorsion R⁰` localization term. Its categorical transport, point dévissage,
quotient assembly, canonical residue-field comparison and residue-field
assembly have separate independent ordinary mathematical acceptance. The
original module-level
K-map endpoints use the same native universe. The subsequent same-original-
category comparison `smallKUniverseEquiv` supplies explicit universe transport;
`Affine.UniverseComparison` uses it for public scheme G-theory. The native
Milnor migration was independently compared with the actual R5 definitions by
transparent tensor/symbol/map identities. The current direct Aglib reuse preserves
that tensor quotient as `MilnorK.K2.Group`; `MilnorK.twoEquiv` gives its marked
comparison with the public uniform group `MilnorK.K F 2`. Finite-field vanishing
concerns these Milnor groups, rather than an unconstructed Quillen comparison.

## Fixed mathematical conventions

Write `E.K n = pi_(n+1)(BQ(E), zero)`. Positive K-groups are commutative;
use `Additive (E.K n)` when forming direct sums. The completion comparison
`zeroCompletionPositiveKEquiv R 0` concerns K1, whereas index `1` concerns
K2. Right modules use `Rᵐᵒᵖ`. Neither an opposite-ring identification nor a
SmallModel transport is suppressed in a final theorem.

The standard completion-to-Q comparison already contains one inner-loop
reversal. Preserve it and its specified basepoint paths. A new isomorphism
cannot be called normalized until its equation on the actual matrix cube or
ordered symbol has been proved. The R5 conventions to be reconciled are
`T = -D_Q after F_1` and `N = -mu_+^{-1} after F_2`.

All-field Q1 is needed, including positive characteristic. Q2 is needed in
degrees 1 and 2 for small abelian families in a common universe; in particular
allow index universe `u` and category/hom universe `u+1`. Broader degree
statements are appropriate only when the same proof supplies them.

## Proof suppliers and constructed comparisons

| Obligation | Foundational supplier | Native construction using it |
| --- | --- | --- |
| Stable quotient and determinant | `StableElementaryQuotient` and finite matrix elimination | `StableFieldDeterminant`: actual elementary kernel and quotient determinant |
| Quotient through completion to original Q | `StableGeneralLinearCompletionKernel`, `ProjectiveCompletionPositiveK` and its naturality | `Field.{ElementaryProjectiveKOne,ProjectiveDeterminant,ModuleDeterminant,MatrixCubeComparison}`: original determinant, scalar square and literal cube equation |
| Stable ring naturality | `StableCompletionBasedRingNaturality.stablePiOneMap_ringMap` | Quotient and determinant naturality through the original tracks |
| Finite products | `Waldhausen.Product.KEquivalence` and exact Q/S naturality | `FiniteSupport.FiniteProduct`: equivalence on original Q projections |
| Filtered nerves and based groups | `FilteredRealization.{NerveColimit,BasedGroups}` | `FiniteSupport` stage diagram, arrow lifting, common vertices and rebasing to original K-maps |
| Singleton closed support | `GeneralDevissage.closedSupportGEquiv` and its pushforward equation | `FiniteClosed`, `FiniteClosedFamilies` and `ClosedImmersion.FinitePointAssembly`: geometric assembly retaining original field pushforwards |
| Exact equivalences | `KTheory.Equivalence` | Actual finite-stage, finite-module and upper coherent-model comparisons |

The initial source inspection found elementary matrix commutator relations.
The finite-rank stable Steinberg presentation, its universal central lifting
property and a canonical map from its kernel to actual K2 are now constructed.
The comparison isomorphism and the required low-degree homotopy/homology
argument remain missing. The Coxeter
Matsumoto name in mathlib is unrelated. Hurewicz *fibration* APIs do not supply
a degree-two Hurewicz isomorphism.

## Q1: determinant on the original field K1

### Q1a. Stable algebra

The implemented proof in `StableFieldDeterminant` follows this route.

1. Over a commutative ring define `det : StableGeneralLinear.Group R ->* Rˣ`
   with `StableGeneralLinear.lift`, using finite `GeneralLinearGroup.det`.
   Prove determinant invariance under `step` and `transition` from block
   determinant and simultaneous reindexing. Export `det_of` and ring-map
   naturality as equalities of homomorphisms. Rank zero is included.
2. Identify the existing `Elementary.matrix` with `Matrix.transvection` and
   prove that every elementary generator has determinant one. Extend by
   subgroup closure to `elementary R <= det.ker`.
3. For a field, use mathlib's
   `Matrix.exists_list_transvec_mul_diagonal_mul_list_transvec` or
   `diagonal_transvection_induction_of_det_ne_zero` to reduce an invertible
   finite matrix to diagonal units. Do not assume infinite residue field or
   a finite-rank commutator theorem.
4. Collapse diagonal coordinates in the stable elementary quotient. A
   determinant-one pair `diag(a,a^{-1})` is elementary by the existing
   Whitehead block identity; reindexing places the pair in any two slots.
   Alternatively conjugate one-slot diagonal units in the already
   commutative stable quotient. Show a diagonal class is the rank-one class
   of the product of its entries. This gives the reverse kernel inclusion.
5. Rank-one diagonal units give a section of `det`. Descend through the
   actual quotient to obtain `quotientDetEquiv : ElementaryQuotient F ≃* Fˣ`.
   Prove its value on `quotientMap (of F n g)` and its square with
   `quotientRingMap f`. Handle `n=0`, `F2`, and `F3` through the same proof.

Owner: `Quillen/Algebra/Group/StableFieldDeterminant.lean`. The algebraic
endpoint feeds the original Q-group transport and representative comparison
below.

### Q1b. Canonical transport and representative marking

Form the projective-Q comparison

```text
ElementaryQuotient F
  --elementaryPiOneEquiv--> pi1(ZeroComponent F)
  --zeroCompletionPositiveKEquiv F 0--> K1(projective F^op).
```

Its composite retains the original stable matrix map. Prove its ring-change
square using quotient surjectivity, `stablePiOneMap_ringMap`, and
`zeroCompletionPositiveKEquiv_baseChange`; there is no need to choose a new
inverse naturality datum. Invert only this canonical composite to define the
projective determinant.

Construct the exact equivalence from finite projectives to finite modules over
a field, and the commutative-field opposite-ring comparison, with their actual
scalar-extension natural isomorphisms. Then transport through
`presentationKEquiv`/`smallKMap` to the same upper-universe finite-module Q
group used by the client. State the final `D_Q` on that group and prove literal
scalar-extension naturality.

The marking uses a geometric proof. The R5 module
`QuillenSourceFieldConstructors` defines `positiveModuleMatrixCubeClass` as the
literal coordinate transpose of its capped Q automorphism cube. Its existing
`positiveModuleMatrixCubeClass_eq_neg` proves a relation to its zero-first
class, not to the native completion class. The native
Q-cylinder/cube construction compares the mapped
stable automorphism loop, the actual completion-to-Q track, the cap, and the
loop-degree shift. The equality of represented classes gives

```text
D_Q (positiveMatrixCube g) = GeneralLinearGroup.det g.
```

Inspect the two cube coordinates and the existing inner-loop reversal
explicitly; the sign cannot be fixed by naming an inverse equivalence.
`Quillen.Field.moduleDetEquiv_matrix_cube` in `Field.MatrixCubeComparison`
proves this equation for every field and every finite rank, including zero,
on the literal `Automorphism.Cube.automorphismFirstCube` of the original
upper-small finite-module matrix automorphism. Its source SHA-256 is
`6302dccd9faffdac0a0806e856d8ee119cdf6d70cd030554e58b1c7ceee61554`.
The theorem has normal build evidence and independent complex acceptance.
The R5 adapter remains an unapplied integration product.

The implemented `Field.MatrixTransport` uses the actual reversed-coordinate
free-module basis and maps its isomorphism through the upper SmallModel. Its
target action is the ordinary `g.val.mulVec` for the same matrix `g`.
`Automorphism.Isomorphism` transports the represented cube through that
specified isomorphism. `ProjectiveCompletionAutomorphismCones` identifies the
unlocalized subdivision contraction arms as actual natural transformations.
`Automorphism.PositiveNormalization` proves that right translation, its actual
cancellation cap and one inner-loop reversal represent the positive cube class.
Its homotopy criterion retains the candidate's original correction path,
using the proved commutativity of every loop-component fundamental group.
`Plus.ProjectiveCompletionAutomorphismHomotopy` supplies the actual localized
finite-stage numerator/denominator homotopy. `Field.StableMatrixMarking`,
`Automorphism.NormalizationOrder` and `SpaceAction` compare the inverse-first
and right-cap normalizations through actual loop actions. This proves the
literal matrix-cube equation without a global completion-to-positive H-map.
Commutativity alone is not used to interchange the loop-valued cap factors.

## Q2: finite-support decomposition on evaluation maps

### Q2a. One canonical family and its finite stages

Migrate the R5 general candidates `Pi/Abelian.lean` and
`Pi/FiniteSupport.lean` to `Quillen/Aglib/CategoryTheory/Pi/`, using native
`CategoryTheory` namespaces and the same mathematical objects. First check
mathlib and pinned Aglib for each structure to avoid duplicate instances.
Supply pointwise abelian structure, exactness, and evaluation exact functors.

Let `FinFam(C)` be the full subcategory of families `M` for which
`{i | not IsZero (M i)}` is finite. For a finite subset `s`, let `Stage(s)` be
the full subcategory of the SAME ambient product on objects zero outside `s`.
Prove these object properties are Serre classes. Subset inclusions are literal
full-subcategory inclusions; their composition does not require choosing
new zero extensions. Every finite-support object lies in some stage.

Restriction identifies `Stage(s)` with `product_(i in s) C_i`; its inverse is
zero extension. The unit is the identity on `s` and the unique zero-object
isomorphism outside it. This must work for arbitrary zero objects outside
support. Prove exactness, evaluation equations, singleton-inclusion equations,
and compatibility under `s <= t`. The empty stage is equivalent to the
one-object zero category, with trivial K-groups.

### Q2b. Finite products using the original Q projections

Construct the binary exact product structure and its projection/insertion
exact functors under the general candidate owner if missing. Transfer
`Waldhausen.Product.KEquiv` through `comparisonKEquiv`, identifying
`ofExactCategory (product E F)` with the Waldhausen product structure.
Use `comparisonKEquiv_exactFunctor_naturality` to prove the forward map is
exactly the pair of the original Q `KMap`s. An abstract product isomorphism
without those equations is insufficient.

Induct over a finite index set to obtain the dependent finite-product
equivalence. At each step use restriction/splitting exact equivalences and
prove evaluation coordinates, rather than carrying a choice of enumeration
into the public map. Its inverse is determined by the original coordinate
inclusions. The empty product needs a proved trivial-group endpoint.

### Q2c. The actual filtered Q-nerve colimit

Index by `Finset I` with subset arrows, a small filtered category in the
same enlarged universe as the category family. Build a strict diagram
`s |-> Q(Stage(s))` and the cocone to `Q(FinFam(C))` from actual inclusions.

Discharge the inputs of `FilteredNerveColimit.nerveCoconeIsColimit`:

1. **Objects:** choose a finite support containing the displayed family.
2. **Arrows:** represent an actual Q-arrow by an admissible span. Its apex is
   a finite-support family; enlarge the stage to contain all displayed
   endpoints and this apex. Lift both legs with their admissibility proofs.
   A sharper same-stage lift may use that an inflation into a stage object
   forces its apex to have the same support bound.
3. **Equality:** `mapQ_faithful_of_fullyFaithful` supplies faithful legs.
   Equality of Q spans is an apex isomorphism, which lifts in the full
   subcategory. Equality of underlying stage objects is literal after a
   common transition, by subtype extensionality and proof irrelevance.

Use a single ambient zero family as a vertex at every stage and in the
cocone. These vertices are strictly compatible. The zero objects selected by
the abelian/finite-biproduct instances need not be definitionally this family.
Construct their unique zero isomorphisms, realize the corresponding Q edges,
and prove the rebasing equation to the public zero-normalized `KMap`.
Do not assume normalized Q functors form the same strict diagram without
proving that assertion.

Apply `piMap_jointlySurjective` and `piMap_eq_eventually` only after the
actual simplicial colimit and vertex conditions have been proved. Recall
that K-degree `n` uses homotopy degree `n+1`.

### Q2d. Assemble and characterize the direct sum

For `a : K_n(FinFam(C))`, stage representability implies that its evaluation
coordinates vanish outside one finite set. Define

```text
e_n(a)_i = K_n(ev_i)(a),
j_n(x) = sum_(i in support x) K_n(incl_i)(x_i).
```

Use the finite-product theorem at a representing stage to prove
`j_n(e_n(a)) = a`. Evaluation composed with an insertion is the identity at
the selected coordinate and the zero exact functor elsewhere; prove its K-map
is trivial. This proves `e_n(j_n(x)) = x`, and both are homomorphisms. The
same finite-stage argument makes the construction independent of any chosen
representative. Export coordinate, singleton, and finite-sum inverse equations.
If the proof works uniformly in positive degrees, expose that generality and
derive degrees 1 and 2; do not start a separate continuity programme.

## Q3: Dedekind and finite closed-point assembly

For a Noetherian Dedekind domain, let `T_R` be the actual Serre subcategory of
finite torsion modules. Prove functorial primary decomposition into the
finite family of maximal-ideal-primary pieces. Use annihilators of finite
generating sets to obtain finite support; prove homomorphisms preserve pieces
and cross-primary homomorphisms vanish. The resulting exact equivalence is
with a finite-support family of primary categories, NOT with residue vector
spaces.

The pinned mathlib already supplies the module-level primary components in
`Mathlib.Algebra.Module.Torsion.PrimaryComponent`: `Ideal.primaryComponent`,
its `map`, `map_ker_eq`, and `map_surjective`, together with
`iSup_primaryComponent_eq_top` and `iSupIndep_primaryComponent` over Dedekind
domains. `Submodule.isInternal_prime_power_torsion` in
`Mathlib.Algebra.Module.DedekindDomain` supplies the finite annihilator-factor
decomposition. Reuse these results for the categorical exact equivalence.
For its localization consumer, compare the actual large-category torsion
predicate with `ModuleCat.FiniteLocalization.torsion R⁰` and then the
`smallTorsion R⁰` supported model in
`Quillen.GTheory.FiniteModules.LocalizationSequence`; do not replace the
original supported K-term by an untracked small model.

For each nonzero prime, supply the finite filtration of its primary modules
by powers of the ideal. The factors are modules over the residue field.
Apply existing dévissage, retaining restriction-of-scalars/pushforward as its
forward K-map. Compose its direct sum with Q2 and the primary exact
equivalence to obtain `J_n` in degrees 1 and 2. Prove the equation on each
direct-sum inclusion; it identifies the final map with residue pushforward.

For the surface, separately split coherent sheaves with finite closed support
into their singleton-supported components in the Aglib candidate owner. Its
projection/inclusion isomorphisms must be natural and exact. Apply singleton
`closedSupportGEquiv`, then Q2, in every positive degree, including K1 and K2. The supported
stalk quotient and its fullness/essential-surjectivity proofs are separate.
R5's label `J2` here denotes a second-support stratum in K1, not degree two.

The finite-S step is now supplied by
`Quillen.Aglib.AlgebraicGeometry.Modules.Coherent.Support.FiniteClosed`.
`finiteSupportEquivalence` has the original summation functor forward and
exact directions; its singleton square and self/other evaluation isomorphisms
cover arbitrary off-coordinate zero objects. Each component is actual
restriction to the complement of the other points followed by extension by
zero. The sum of original counits is stalkwise invertible, and its inverse
gives explicit retracts proving coherence. This uses local noetherianity and
closedness of each point of S, without a global separation or T1 hypothesis.
`FiniteClosedFamilies.reconstructionEquivalence` supplies the canonical
finite-family equivalence on locally Noetherian schemes for an injective
family of closed points. On a Noetherian scheme ordinary support containment
in their range already forces finite support.

`ClosedImmersion.FinitePointAssembly.fieldAssemblyKEquiv` then identifies
the direct sum of public `G (Spec (fields i)) (n+1)` with the actual supported
subcategory of `SmallModel.{u+1} (FiniteTypeSheaves X)`. It requires
`X : Scheme.{u}`, `[IsNoetherian X]`, `I : Type u`, an injective closed-point
family, and closed immersions from the specified field spectra whose images
are those points. Its singleton, finite-sum and ambient equations retain
the original pushforwards. Both K1 and K2 specializations are public; this
geometric native assembly is accepted and normally compiled.

The Dedekind module-level construction is implemented in
`Quillen.GTheory.Dedekind.PrimarySupport`, `ResidueDevissage`, `ResidueAssembly`,
`ResidueField` and `ResidueFieldAssembly`. Its public endpoint is

```text
Quillen.DedekindResidue.residueFieldAssemblyKEquiv R n :
  (directSum_p Additive (G (p.asIdeal.ResidueField) (n+1)))
    ≃+ Additive (SupportedG R⁰ (n+1)).
```

It assumes only a commutative Dedekind domain. The all-degree point theorem
`residuePrimaryKEquiv` applies actual general-ideal power filtrations, including
nonprincipal primes. The canonical quotient-to-residue-field algebra map is
an equivalence by maximality, and its finite-module comparison uses original
restriction of scalars. `residueFieldAssemblyKEquiv_of`, its finite-sum formula
and `supportedKMap_comp_residueFieldAssembly` retain the original support and
ambient pushforwards. The source is finite-module G-theory of
`Ideal.ResidueField`. `Affine.UniverseComparison.publicSpecGRingEquiv`
compares public scheme G with native ring G for every Noetherian ring in all
degrees, through the same original coherent category. Its residue-field
comparison preserves the original scheme residue pushforward.
`Affine.LocalizationNaturality.publicSpecGRingEquiv_localization_pullback`
identifies literal `Scheme.pullbackG` for localization at any submonoid with
the original finite-module localization map in all degrees. These accepted
comparisons alone do not identify `Scheme.boundaryG`. The subsequent
`Affine.PrincipalBoundaryComparison` supplies that additional boundary square.

## Q4: the characteristic-zero Matsumoto phase

Use Aglib's public `MilnorK.K F 2` and its canonical `MilnorK.twoEquiv F` to
the retained tensor quotient `MilnorK.K2.Group F`. The supplied comparison
preserves the ordered symbol and field maps. R5's legacy tensor interface can
use a transparent alias to `Group`; no Quillen copy or old module alias is
retained. Keep this marked comparison explicit whenever the two presentations
meet.

`Algebra.Group.StableSteinberg` now constructs a presentation with finite-rank
root generators, root-additivity, disjoint-commutator, ordered-chain-commutator
and stabilization relations. Its map is onto the original stable elementary
subgroup, and a fresh index after stabilization proves perfectness, including
over fields of orders two and three. `StableSteinbergNaturality` maps each
literal generator by its coefficient field map and proves the squares with
the original stable GL and elementary maps. Both leaves have independent
ordinary mathematical acceptance. No identification with a separate infinite-
index presentation is assumed.

`StableSteinbergCentrality` now proves centrality of this actual kernel.
Every presented word lies in a finite-rank root subgroup. Commuting fresh-column
and fresh-row root products give literal matrix conjugation formulas for that
subgroup. Injectivity of the original finite-stage stable-GL map forces a
kernel element's matrix to be identity. The fresh-index commutator expression
then centralizes every original root. A common maximum rank proves the result
for arbitrary words. This proof uses no injectivity assertion about Steinberg
stages, and includes rank zero and fields of orders two and three. Independent
ordinary review accepted the centrality proof.

`StableSteinbergTorus` supplies the literal words
`w(a)=x01(a)x10(-a^-1)x01(a)` and `h(a)=w(a)w(-1)`. Their actual rank-two
images are the Weyl matrix and `diag(a,a^-1)`. The exact ordered defect
`h(a)h(b)h(ab)^-1` is a field-natural element of the original elementary-map
kernel. Matrix multiplicativity does not assert multiplicativity of `h` in
the presented group. This construction is independently accepted.

`StableSteinbergUniversal` proves the universal lifting property for every
surjective central extension onto the actual elementary group, with an
independent universe for the extension group. Fresh-index commutator lifts
satisfy all defining relations and stabilization; Steinberg perfectness gives
uniqueness. The theorem does not assert surjectivity onto an arbitrary central
extension.

`StableSteinbergSymbols` proves that the literal ordered defect is bilinear
and satisfies the Steinberg relation. Its rank-three torus commutator
calculation preserves the positive ordered symbol. The canonical
`milnorToKernel` uses Aglib's supplied tensor symbol lift and the forward
`MilnorK.twoEquiv`; the actual field-map square and smallest-field clients
are checked. All-rank kernel generation is now supplied by the subsequent
three-module family; injectivity of this map remains open.

`HomotopyFiber.LoopCentrality` constructs the actual right loop concatenation
and proves centrality of the original connecting-map image and projection
kernel, without connectivity hypotheses. `Field.SteinbergFiberComparison`
applies this to the actual fiber of `stableZeroMap F`. Its fundamental group
is a central extension onto the original elementary group. Universal lifting
gives a Steinberg-to-fiber homomorphism. BGL asphericity identifies the fiber
projection kernel with the original target pi2; the original basepoint path
then gives a map from the Steinberg kernel to original finite-projective
right-module K2, explicitly `(FiniteProjectiveModule.exactStructure Fᵐᵒᵖ).K 2`.
The subsequent finite-module transport must remain an explicit composition.
`SteinbergFiberNaturality` now proves the exact square with original
`rightBaseChangeExact f` and the restricted original Steinberg field map,
for fields in the same universe. Its nonstationary homotopy-fiber transport
retains both original correction paths. The two existing map/LES suppliers
are generalized only in their universe binders; their proof bodies and old
single-universe specializations are unchanged.
`SteinbergFiberSurjectivity` proves the four original lift/kernel/pi2/projective-K2
maps surjective under explicit `Group.IsPerfect (StableFiberPiOne F)`.
`Aglib.Algebra.Group.Hom.CentralLifts` supplies the general central-kernel range
argument. `Plus.StableFiberPerfectness` now proves the required perfectness
for the literal original stable-zero fiber over every ring. Its field result
targets exactly the existing `StableFiberPiOne` alias and is theorem-valued;
the existing surjectivity consumers install that proved instance locally.

`StableSteinbergRankTwo` proves, for every field, that the original ordered
defects generate exactly `stage F 2 ∩ ker(toElementary F)`. Its two-cell
Bruhat proof takes place inside the original stable presentation and uses
no injectivity of an unstable Steinberg-stage map.
`StableSteinbergParabolic`, `StableSteinbergBruhat` and
`StableSteinbergKernelGeneration` now close the all-rank step. The original
old-stage/column parabolic admits actual kernel descent. Source-word coverage
in the quotient by the same defect subgroup is proved as a genuine `B V B`
subgroup, with both zero and nonzero pivots. Literal finite-matrix detection
then gives one-step descent at every rank at least two, hence
`defectSubgroup_eq_kernel`, `kernel_le_stage_two` and surjectivity of the
unchanged `milnorToKernel`. The proof includes F2 and F3. Milnor-map
injectivity, comparison bijectivity and positive product marking remain open.

`Field.MilnorKTwoComparison` composes the supplied uniform Milnor map with
the original right-projective K2 map, and then explicitly with
`rightProjectiveUpperModuleKEquiv F 2`. Both resulting maps preserve the
literal ordered torus-defect formula and the original field-extension
squares. Its conditional surjectivity statements expose the stage-two and
actual-fiber-perfectness hypotheses separately. `Field.MilnorKTwoSurjectivity`
uses the all-rank theorem above to discharge stage containment in four
explicit wrappers. `Plus.StableFiberPerfectness` supplies their remaining
actual-fiber-perfectness input, so the canonical maps are surjective over
every field. Finite-field lower/public G2 consequences use separate explicit
model and affine transports.

Retain these explicit projective/opposite/finite-module compositions when
proving comparison bijectivity and equality with the positive scalar product
on actual symbols. The field-extension square is already supplied, but it
does not identify the product marking. These remaining comparison and marking
proofs are the acceptance boundary for Q4.

Q6 uses the smaller surjectivity route. The actual homotopy-fiber LES,
asphericity of BGL and the original stable pi1 kernel give a central extension
from the original target pi2 into the fiber group `H`, with quotient the actual
elementary group. The proved perfectness of `H` makes the genuine Steinberg
lift surjective, hence its kernel surjects onto original pi2. Universality
of `H` is not needed for this conclusion.

Q4 bijectivity has a further independent obligation: prove injectivity of
that original Steinberg/fiber comparison. Proving Milnor-to-Steinberg-kernel
injectivity alone does not settle it. A degree-two homological/universal-central-
extension comparison is a possible route, but the actual marked homology maps
and its injectivity must be constructed rather than assumed.
`LocalCoefficients.PullbackCoveringHomology` now closes the same-universe
chain supplier with the free module on the actual covering fibers and their
genuine monodromy. Its original-chain arrow square has the literal second
projection from the pullback subtype as lower map. No connectedness,
source-cover simple connectedness or base-pi1 bijectivity is assumed.
`Covering.Pullback` supplies the shared literal matching-pair subtype in
independent space universes. For a simply connected total cover, its original
first-projection pi1 map identifies pi1 of the pullback with the raw pi1
kernel. Path connectedness is derived under explicit source path connectedness
and raw pi1 surjectivity. `PullbackFiber` retains the original projection and
connecting equations and proves that its actual mapAt map is bijective on pi1.
The homology provider now uses this same model through transparent aliases.

`PullbackCoveringHomologyUniverseLift` closes the mixed-universe chain step
for source `Type u` and target/cover `Type (max u v)`. Only the source is
lifted; an actual coefficient-down isomorphism and target comparison give an
isomorphism of the original chain arrows. The successor specialization
retains the original `UniverseLift.chainMap.{u,u+1,u+1}`, literal second
projection and integral coefficient object.

`ClassifyingSpace.ComponentCover` constructs a surjective simply connected
cover of the actual categorical vertex component, including mixed category
universes. `Plus.ProjectiveCompletionCover` specializes it to the literal
original `ZeroComponent R`. `Plus.StableZeroFiberHomology` uses that cover
and the original plus certificate, for every ring, to construct all the
pullback data: path connectedness, perfect pi1 of the pullback, the original
integral second-projection quasi-isomorphism, and an actual pi1 equivalence
to the original constant-path stable fiber. The original correction paths
and connecting/projection equations remain visible.
This closes the covering and homological setup, not perfectness of the
homotopy fiber.

`LocalCoefficients.H2CapDescent` now proves the next precise criterion. For
an injective actual map `j : C(X,Y)` between spaces in one universe, with
path-connected source, simply connected target and surjective original
integral H2 map, the range of the original `connectingHom` lies in the
commutator subgroup of the original constant-path fiber pi1. Its coupled
family constructs the ambient capped-tetrahedron cocycle, the marked absolute
spherical-minus-constant cycle and prescribed finite vertex straightening.
Repeated simplices and fixed-family intersections are reconciled by actual
map equality and injectivity, with genuine boundary HEP. Original categorical
H2 surjectivity yields a finite boundary equation; actual endpoint evaluation
and the source-edge coboundary prove the result. No global normalization law
or Hurewicz comparison is assumed.
`HomotopyFiber.InjectiveH2Perfectness` applies the original LES and perfect
source pi1 to this commutator criterion. `HomotopyFiber.H2Perfectness` removes
injectivity using the genuine mapping-cylinder inclusion and its actual target
homotopy equivalence, retaining the strict composite, original H2 maps and
endpoint-aware fiber comparison. Thus path-connected source, perfect source
pi1, simply connected target and surjective original integral H2 suffice for
perfect pi1 of the actual homotopy fiber. No CW or simply connected source
hypothesis is introduced. The quasi-isomorphism corollaries retain the original
local-coefficient and mathlib singular-chain arrows. The all-ring
`Plus.StableFiberPerfectness` application uses the constructed cover data and
original fiber-map bijection at the canonical constant-path point.

## Q5: low-degree actions, signs, and the origin DVR

Construct only the `(1,1)` field/module action and `(0,1)` supported-object
action needed by the inverse-symbol boundary. Reuse existing self-track
operations where applicable, but prove additivity in the automorphism/unit
variable and compatibility with the actual localization nullhomotopy.
Preserve the same `mu_+` and prove its marking on ordered field symbols.

The native identity-automorphism construction is now implemented in
`KTheory.LowDegreeScalarAction.IdentityAutomorphism`, using generic
`Topology.HomotopyGroups.LoopNormalizationProduct` and `SelfTrackOperation`.
For the original exact structure `E` and `u : Aut (Id C)`, its public maps are

```text
kZeroActionHom E u : E.K 0 ->* E.K 1
kOneAction E u     : E.K 1 ->* E.K 2.
```

`kZeroNatAut` and `kOneNatAut` prove the multiplication and identity laws in
the natural-automorphism variable. Those laws use `C : Type (max u v)` with
`Category.{v} C`; checked consumers include finite projectives, `FGModuleCat`
and its actual upper SmallModel. Generic descent retains the original cube
quotient. Source degree one uses an explicit trivial pi1-action on pi2,
discharged for the native Q-space by `SpaceAction`; higher source additivity
uses a distinct spatial coordinate. The whole composition prism is fixed at
Q-zero. The representative formulas preserve track time first and the inverse
relative to spatial-first `loopKOneNormalization` in degree zero.

All three leaves passed normal compilation, independent complex mathematical
review, 15 scoped environment linters, native text checks and the full
182-declaration standard-foundation audit. The two generic leaves have no
K-specific inputs or direct KTheory imports. Their inherited transitive import
debt is unchanged.

`LowDegreeScalarAction.ExactNaturality` proves the whole normalized-Q
self-homotopy square from ordinary componentwise compatibility of identity
natural automorphisms under an exact functor. It retains the actual zero rebase.
The general candidate `CategoryTheory.Linear.ScalarAutomorphism` supplies the
canonical scalar natural automorphism and lifts it to the actual chosen model
through full faithfulness. `LowDegreeScalarAction.ScalarUnit` then supplies
the unit-group homomorphisms into both original K-operations and their actual
KMap naturality, including independently sized source categories with one
fixed model universe. Finite-projective consumers need a commutative ring;
finite-module consumers additionally need Noetherianity. These constructions
have independent ordinary mathematical acceptance and focused normal builds.

`SelfTrackLoopShift.operation_loopShift` proves the signed loop-shift formula,
and `HomotopyFiber.SelfHomotopy.connectingHom_operation` proves its consequence
for the original path-space boundary. In degrees two to one the output is
inverted: the new track coordinate, curried coordinate and spatial normalizer
must all be tracked. Both leaves have independent mathematical acceptance.
`LowDegreeScalarAction.SerreBoundary` now identifies the supported operation
through the whole original Serre fiber comparison and its fixed epsilon
nullhomotopy. Thin Q-hom sets at its actual quotient-zero objects prove literal
double simplicial cylinder equalities; realization gives invariance for every
homotopy time, epsilon time and source point. The whole stored fiber path is
therefore preserved. Bijectivity of the original fiber comparison gives
`delta_1(action_1(a)) = action_0(delta_0(a))^-1` for the formal quotient.
The actual-target version constructs its formal automorphism through the
fully faithful canonical target lift. Scalar specialization requires only
ordinary source, target and localization-functor linearity, with no linear
structure on the formal quotient. Independent ordinary review accepted these
statements in their common small categorical universe. The following leaf
supplies their actual standard SmallModel transport.

`LowDegreeScalarAction.SmallModelBoundary` now proves that standard-model
transport through the literal exact identity functors, including the separate
finite-module `smallAbelianKEquiv`. Its `finiteConnectingHom_scalar` uses the
original finite-module connecting maps for every commutative noetherian ring
and submonoid. Localization linearity is proved from the original scalar
extension, and the kernel operation restricts the original lifted scalar
automorphism. Neither model nor formal quotient is given a new linear instance.

`LowDegreeScalarAction.ObjectClass` fixes the object-class sign. The original
K0 object loop under the identity operation gives `automorphismClass`, hence
the inverse of the literal `automorphismFirstCube` class. For the actual upper
free rank-n field-module object, the determinant is `(r^n)^-1`, with rank zero
and the chosen-zero object included. The rank-one value is `r^-1`.
Both subsequent leaves have independent ordinary mathematical acceptance.
`FiniteModules.PrincipalObjectBoundary` now computes the original degree-zero
Serre boundary on the literal positive cube of an inverted self-conflation
endomorphism, including zero cokernels. It gives the original supported
cokernel object class with positive sign. The actual-target proof retains
the original localization lift and correction paths. For a commutative
Noetherian ring and regular `r`, its original `closedConnectingHom r 0`
sends the actual localized rank-one scalar cube to the original quotient-ring
rank-one object class. The unit case is included.

`LowDegreeScalarAction.UniverseNaturality` proves operation and object-class
naturality for the original `universalKMap` in independent small categorical
universes. The canonical `smallKUniverseEquiv` therefore preserves scalar
actions, object classes and literal positive scalar cubes, with both
essential-smallness hypotheses and no linear instance on either model.
`FieldSymbols` defines a positive rank-one K1 class using the original
determinant inverse and proves equality with the literal matrix cube.
The actual scalar K1 operation gives its bilinear field unit product and
original tensor-extension naturality. `DvrSymbols` proves unit-unit boundary
zero for actual localization, principal, fraction and local-DVR boundaries.
Its upper product is explicitly lowered by the canonical universe comparison.
`PrincipalUnitBoundary` now computes the ordered unit/principal boundary
over every Noetherian commutative ring at a regular element. The original
`closedConnectingHom r 1` sends the canonically lowered product to the
literal lower positive rank-one quotient scalar cube at the image of the
first unit. The signed boundary inverse and object-class inverse cancel
explicitly. Unit principal elements and the zero quotient are included.
No field or proper-ideal hypothesis is used.
`DvrUnitBoundary` now transports this formula through the original principal/
local-DVR boundary square. For a Dedekind domain, a height-one prime and an
irreducible element of its actual local DVR, the original local boundary of
the canonically lowered ordered field product is the literal lower positive
native residue scalar cube. Canonical promotion and the original determinant
then give the positive reduced unit. The supplied-fraction-field version
retains the original field and exactly the restriction map used by the
existing native boundary comparison. Genuine inverse-ring-isomorphism scalar,
object, cube and product transport supply these joins; no ring structure on
the quotient is replaced. The reversed input, Steinberg relation and equality
with the ordered Milnor/Steinberg construction remain open.

Derive the raw boundary and then its corrected version through the fixed
`D_Q`, `mu_+`, `T`, and `N`. Check both ordered inputs `{u,pi}` and `{pi,u}`
and the scalar calibration using actual representatives. A free sign choice
or unrelated automorphism is not an acceptable calibration.

For the actual smooth-curve origin DVR, construct unit-pair classes in its
original K2 and prove generation. The algebraic part of a useful route is proved:
`MilnorK.K2.DVR.ker_tame_eq_unitSymbolSpan` identifies the Milnor
tame kernel with the integer span of field symbols of two actual DVR units.
The directly supplied Aglib `MilnorK.K2.Residue` and `DVR.Basic` give the ordered tame map,
with `∂{u,π}=ū` and `∂{π,u}=ū⁻¹`, for every DVR and its fraction field.
Quillen unit generation still needs the marked comparison, an injection of
the original DVR group, and actual Quillen boundary compatibility. This route
must discharge that injection rather than assume it from residue vanishing:
the residue field has characteristic zero and its K2 need not vanish.
`GTheory.DVR.SplitResidue.localizationKMap_injective_of_residueSection`
proves injectivity of the original generic finite-module G map in every
degree when the actual residue map has a ring section. Equivalently one may
supply field maps `σ : F →+* R`, `ρ : R →+* F` with `ρ.comp σ = id` and
`ker ρ` the maximal ideal. The actual `PowerSeries ℚ` test realizes this
hypothesis. The separate, unapplied `NativeOriginDvrSection` proposal constructs
the section for the existing arithmetic diagram and supplied genuine model
from their geometric triangles. It strictly checks the original trait
`Scheme.pullbackG` and `Scheme.pullbackK` injectivity in every degree, including
the existing additive G2/K2 maps. Its 45-declaration standard-foundation audit
and patch applicability check passed against 52 matching fresh R5 sources;
independent ordinary mathematical review accepted it. The abstract arithmetic
diagram supplies its coefficient section directly; the genuine-model scheme
corollaries retain the normality premise of that model's diagram constructor.
This does not supply a Quillen
product or unit-generation theorem. An alternative Dennis--Stein/unit-generation
argument must prove the needed
generation theorem and compare its classes to `mu_+`. Keep either unresolved
generation/injectivity input visible while pursuing the concrete origin case.
Finally prove generic and closed pullback equations on generators, and extend
by generation. Do not claim a full local-ring presentation from this result.

## Q6: finite fields

Migrate/reuse the all-finite-field zero proof for the actual Milnor tensor
quotient. Separately construct a symbol-preserving surjection to original
module-Q K2 and transport to `G2(Spec k)`, or prove that latter group zero
directly. Characteristic-zero Q4 does not supply this surjection in positive
characteristic. Include the smallest fields without extra cardinality
hypotheses. This endpoint does not require computation of all higher groups.

The basis, maps and symbols now come directly from Aglib's precise
`MilnorK.K2` leaves; Quillen retains only the additional Aglib candidate
`Quillen.Aglib.KTheory.MilnorK.K2.FiniteField`. Its tensor
`k2_eq_zero_of_finite` and `finiteField_k2_subsingleton` need exactly
`[Field k] [Finite k]`. The corresponding uniform degree-two endpoints use
the injectivity of the supplied `MilnorK.twoEquiv`. The old Quillen-targeting
Milnor retarget proposal is superseded by direct Aglib retargeting; its patch
remains unapplied and does not certify whole-R5 integration.
The canonical actual Quillen maps and their field naturality are now supplied
by `Field.MilnorKTwoComparison`. All-rank kernel generation discharges the
stage-two condition in its surjectivity argument, and
`Plus.StableFiberPerfectness` now supplies actual stable-fiber perfectness.
`Field.FiniteFieldKTwo` now gives unconditional subsingleton and `eq_one`
theorems for the original right-projective K2 and upper finite-module K2.
The same-category canonical `smallKUniverseEquiv.{u,u+1}` gives the original
lower `FiniteModuleLocalization.G F 2`; the actual `publicSpecGRingEquiv`
then gives literal public coherent G2 of `Spec F`. The result uses exactly
`[Field F] [Finite F]`, including F2/F3, with no external perfectness or
stage-containment premise. Milnor-map injectivity and positive product marking
are not needed for this vanishing theorem.

## Q7: three distinct localization consequences

Use the original exact tail
`T2 -> G2(R) -> G2(K) -> T1 -> G1(R) -> G1(K)`.

1. Q3 in degree one and the square with each local DVR boundary identify the
   generic image with the intersection of their kernels. Coordinate
   injectivity of the support assembly is the decisive implication. Neither
   Matsumoto nor finite residue fields are needed.
2. If residue fields are finite, Q3 in degree two and Q6 give `T2 = 0`.
   Exactness then gives generic G2 injectivity; actual affine regular K/G
   transport gives the corresponding K2 assertion. Degree-one assembly is
   insufficient for this step.
3. Under the explicit premise that `G1(R) -> G1(K)` is injective, exactness
   makes the support-to-ambient G1 map zero and the generic boundary onto
   `T1`. Combine with degree-one assembly for arbitrary finite residue-G1
   families. Number-ring K1 injectivity is a separate arithmetic supplier.

Return narrow number-ring and origin statements. Stronger R5 background
records quantify over degrees, fields, or DVRs beyond the proved scope and
must remain explicitly uninstantiated until their full hypotheses are met.

`Quillen.GTheory.Dedekind.Localization` implements the native part using the
original `localizationKMap`, `connectingHom` and `supportedKMap`.
`residueFieldBoundary` consists of primary evaluation and the inverse of the
proved pointwise comparisons. Its kernel-intersection theorem has source
degree `n+1`, not degree zero. `residueFieldG1_finite_family_lift` retains both
the original raw boundary equation to the actual assembly and every prescribed
coordinate under the explicit generic-G1-injectivity premise.
`FiniteModules.LocalizationNaturality` and
`Dedekind.{LocalDvrSupport,LocalDvrComparison,LocalDvrBoundaryNaturality}`
now supply the native scalar-localization comparison. In particular,
`localDvrBoundary_comp_extension` identifies the original local boundary
after actual fraction-field tensor extension with the original global
residue coordinate for `G(n+2) → G(n+1)`.
`localization_range_eq_iInf_localDvrBoundaryFromGlobal_ker` and
`localDvrG1_finite_family_lift` give consequences 1 and 3 with those literal
native boundaries. The finite-family lift retains the original generic-G1
injectivity hypothesis.

`Dedekind.FiniteResidueLocalization` supplies consequence 2. At each height-one
point, Q6's original lower residue-field G2 theorem is transported through
`residueFieldKEquiv` and `residuePrimaryKEquiv` to the actual primary group.
Original supported exactness gives injectivity of
`localizationKMap (nonZeroDivisors R) 2`. The original affine localization
square gives injectivity of the literal public scheme pullback. A genuine
canonical spectrum isomorphism retains the original algebra map to any supplied
fraction field in the stated universe. Actual residue-field finiteness is the
only additional arithmetic premise. Integer and Spec Q to Spec Z clients derive
it from finite quotients; no generic-G1 hypothesis is used in this consequence.

`Affine.PrincipalBoundaryComparison.publicSpecGRingEquiv_principalClosed_boundaryG`
now proves the additional square for the original principal scheme boundary
over every Noetherian ring and every element, in all degrees. Its proof uses
the genuine supported global-sections/pushforward natural isomorphism and
model-universe boundary transport. `Affine.RingIsoNaturality` keeps the
original Spec ring-isomorphism pullback and the inverse scalar-restriction map.
`Dedekind.PrincipalDvrBoundaryComparison` combines these with the actual DVR
quotient and fraction-field identifications, retaining any supplied fraction
field and including G1 to G0. These native statements and the literal R5
`Localization.AtPrime p` boundary proposal have independent ordinary acceptance.
R5's distinct sheaf-stalk boundary uses its particular canonical
stalk, residue and generic triangles. A separate, unapplied R5 proposal now
supplies those actual triangles through the canonical stalk and residue-field
isomorphisms. It identifies the literal `boundaryAtG` with the native local-DVR
boundary, proves the original generic G2 image is the intersection of all
literal boundary kernels, and lifts every finite residue-G1 family under the
explicit original generic-G1-injectivity premise. The extended proposal passed
strict compilation, a full 237-declaration origin audit, patch applicability
and independent ordinary review on the updated native/Aglib basis. It does not
prove arithmetic G1 injectivity or finite-field Quillen G2 vanishing.

## Construction dependencies

| Construction | Native owner | Supplied interface | Dependencies |
| --- | --- | --- | --- |
| Stable algebra | `Algebra/Group/StableFieldDeterminant.lean` | Stable determinant, field kernel, quotient equivalence and naturality | Stable algebra and finite matrix elimination |
| Canonical families | `Aglib/CategoryTheory/Pi/{Abelian,FiniteSupport,FiniteStages}.lean` | Exact evaluations and stage restriction/extension equivalence | Pointwise abelian categories |
| Finite products | `KTheory/FiniteSupport/FiniteProduct.lean` | Original Q-projection equivalence, including the empty product | Waldhausen product and exact Q/S naturality |
| Marked determinant | `KTheory/Field/` comparison leaves | Canonical quotient-Q transport and literal matrix-cube equation | Stable determinant, completion comparison and actual localized homotopy |
| Direct sum | `KTheory/FiniteSupport/Decomposition.lean` | Original evaluation map and finite-sum inverse | Canonical families, finite products and actual filtered Q diagram |

These dependencies supply Q1 and Q2 and support the native Q3 assembly. Q4
remains a separate substantial phase; its new topology must be bounded by
the actual degree-two comparison needed.

## Validation, review, and handback

During authoring compile exact changed leaves with the pinned runtime and
preserved caches. Diagnose a trace/cache mismatch before rebuilding a broad
closure. Keep finite local heartbeat increases scoped and justified; leave
package defaults unchanged. No placeholders, custom axioms, or unproved laws
hidden as fields may close an obligation.

At a coherent delivered milestone, run the applicable scoped environment/text
lint, changed `QuillenTest` properties, and the affected separate client.
Exercise real content: determinant-one elimination, zero-rank and small-field
specializations; arbitrary off-support zero objects; empty support; insertion
and evaluation formulas; and the actual cube/scalar square when supplied.
Regenerate facades with `scripts/generate_imports.py` and check affected
enrollment/import direction. Scope axiom auditing to the new declaration
origins and their transitive inputs under the existing three-axiom policy.
Reuse compatible checks; a helper return or commit creates no new full build.

Obtain independent statement/source-correspondence review at the stable
algebra/Q1/Q2 interfaces before adopting their new load-bearing claims for
substantial further work. The review must distinguish completed native-map
theorems from remaining representative/comparison obligations. Compilation and
axiom auditing alone do not establish that correspondence.

For each accepted milestone report its exact public statements and hypotheses,
owned paths and local source identity, pins, review boundary, commands and
reusable evidence, original-map downstream adapter, and remaining gap. Commit
completed owned source and fixed evidence at a deliberate local boundary;
exclude caches and exploratory output. The user's subsequent instruction
authorizes merging and pushing the completed native results; the R5 proposals
remain separate and unapplied.

The R5 retarget proposals remain unapplied. A strict foreign-style replay
failed on older long lines; a separate fresh kernel-compatibility replay of
79 sources using the actual R5 configuration passed. The new
`NativeClosedSupport` bridge passed strict compilation, a six-declaration
standard-foundation audit, ordinary source-correspondence review and
`git apply --check` against R5 revision
`d34faaf9c80b457a4afe0ee9589acf378b1c8dac`. It proves the original general
closed-support assembly and second-support K1 corollaries. The separate
`NativeFieldDeterminant` bridge passed strict compilation, a nine-declaration
standard-foundation audit and patch applicability checks. Its literal cube,
same-matrix automorphism and original tensor-functor identities preserve the
pre-existing determinant constructor, its `T = -D_Q` sign and original scheme
pullback naturality. Its additional 13 original R5 imports have successful
fresh kernel compilations. The adapters use the fresh native-compatible source
projection; they do not certify the different currently installed R5 dependency
checkouts or full R5 CI. No conclusion here asserts completion of Q1–Q7 or
established status for the full programme.

## Classical reference locators

[Weibel, The K-book, chapter III](https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.III.pdf):
1.1.1--1.2.2 for determinant and field elimination, 5.4--5.5 for universal
central extensions, 5.10.1--5.10.2 for the literal torus words and Steinberg
word calculation, 5.10.5 for kernel symbol generation, 6.1 for the full symbol
presentation, and 6.1.1 for finite fields. The algebraic K2 in these chapter-III
locators still needs comparison with this library's original topological groups.

[Chapter IV](https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.IV.pdf):
1.7.1 for the classical degree-two comparison, 6.4 for product/filtered-union
behavior, and Exercise 7.9 for the automorphism representative. These locate
the mathematics; they do not discharge the native constructions above.

[Chapter V](https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.V.pdf), 6.6--6.7.3,
locates the Dedekind localization tail and specialization. Source conventions
must be compared with the library's actual maps before transporting signs.
