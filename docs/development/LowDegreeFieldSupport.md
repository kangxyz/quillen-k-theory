# Low-degree field and finite-support foundations

This is the implementation and proof plan for the arithmetic-curve request
prepared on 2026-10-18. It describes obligations, rather than asserting their
completion. The first application milestone is the conjunction of Q1 and Q2.
The algebraic determinant, a product comparison, or a conditional adapter alone
does not close that milestone. Q4 is a separate substantial phase.

## Source basis and execution boundary

The investigated Quillen baseline is
`16cc1d011ef6d9c28b045879be10617411a0c2b4`, with Lean `v4.34.1`, mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, and Aglib
`25c37780264f0da94f5bb6bd31cc089d26f2da80`. These are the actual dependency
checkouts as well as the committed pins. The independent Quillen worktree was
clean before this task. The pinned Aglib checkout has unrelated guidance and
tooling edits; it is read-only for this work. No dependency update is planned.
The relevant existing Quillen comparison artifacts are present locally;
their presence is a cache candidate, not a substitute for checking source and
trace compatibility during a focused build.

Implementation now takes place in the dedicated Git worktree
`tmp/output/quillen-low-degree-foundations` of the surrounding workspace, on
`codex/low-degree-field-support`. The previous Quillen worktree is clean on
`main`. Task-owned source was transferred with matching SHA256 values;
dependencies and build outputs were cloned independently without changing pins.

The originating R5 source baseline is
`1b7c3945394bcc27a94d1ebf86df702b0291ee18`. Its dependency checkout is a
different Quillen revision, `c73a12d54e59297d8acf3a7f0046fcf87e5f0ebb`.
R5 source, manifests, and its Quillen package checkout remain read-only.
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
| Q1b | Canonical quotient-to-projective-Q and upper finite-module comparisons, determinant and literal scalar-extension squares; independent unmarked-package review accepted | The native completion representative must still be identified with the literal positive cube |
| Q2 | `Quillen.FiniteSupport.decompositionKEquiv` in every positive degree, original evaluation/inclusion laws and finite-sum inverse; independent mathematical review accepted | Retain scoped final checks at the delivered source identity; no K0 decomposition is claimed |
| Q3 | Exact equivalence of actual finite torsion modules with finite-support primary families, canonical summation and inclusion coordinates; independent categorical review accepted | SmallModel transport, residue dévissage and the actual support K-group assembly |
| Q4--Q7 | Detailed dependency and original-map proof routes below | These endpoints are not supplied by the Q1/Q2 constructions |

The Q2 validation includes strict changed-leaf compilation, 15 scoped environment
linters and native text lint on its nine defining modules (including stable
algebra), a scoped standard-foundation audit, semantic regression properties,
and an independently configured upper-universe client using the same pins.
The checked source does not add custom axioms or proof placeholders. The
separate maintained downstream manifest predates the root Aglib pin; its
standalone client check uses a scratch manifest with the exact root pins,
without modifying maintained manifests or updating dependencies.

The unmarked Q1 comparison package has matching changed-leaf builds and a
separate nine-module scoped lint pass. The primary categorical module has its
own focused build, scoped lint and independent mathematical verdict. Scoped
audits cover all these defining origins and the semantic tests/client, retaining
only `propext`, `Classical.choice`, and `Quot.sound`. A coordinated aggregate
import and generated-source enrollment check complete this source milestone;
they do not close the marking or residue-assembly frontiers.

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

## Audited suppliers and missing content

| Obligation | Existing supplier | Content still to construct |
| --- | --- | --- |
| Stable quotient | `Quillen.Algebra.Group.StableElementaryQuotient`: `elementary_eq_commutator`, `quotientLift`, `quotientRingMap` | Field determinant and its actual kernel |
| Quotient to completion pi1 | `StableGeneralLinearCompletionKernel`: `elementaryPiOneEquiv`, `elementaryPiOneEquiv_quotientMap` | Its composite with field determinant |
| Completion to original Q | `ProjectiveCompletionPositiveK`: `zeroCompletionPositiveKEquiv`; `ProjectiveCompletionPositiveKNaturality`: `zeroCompletionPositiveKEquiv_baseChange` | Module/SmallModel transport and positive-cube equation |
| Stable ring naturality | `StableCompletionBasedRingNaturality`: `stablePiOneMap_ringMap` | Quotient and determinant naturality through the same tracks |
| Binary S-product | `Quillen.Waldhausen.Product.KEquivalence`: `KEquiv` | Exact-category Q-product and finite dependent products |
| Canonical Q/S comparison | `Quillen.Waldhausen.QuillenComparison.Equivalence`: `comparisonKEquiv`; `ExactNaturality`: `comparisonKEquiv_exactFunctor_naturality` | Identification of the original Q projections |
| Filtered nerves | `Quillen.Topology.FilteredRealization.NerveColimit`: `nerveCoconeIsColimit` | Actual finite-support Q diagram, arrow lifting and eventual object equality |
| Filtered based groups | `Quillen.Topology.FilteredRealization.BasedGroups`: `piMap_jointlySurjective`, `piMap_eq_eventually` | Compatible vertices and comparison to the original zero-normalized K-maps |
| Singleton closed support | `GeneralDevissage`: `closedSupportGEquiv`, `closedSupportGEquiv_pushforward` | Finite-point splitting and infinite finite-support assembly |
| Exact equivalences | `Quillen.KTheory.Equivalence`: `mapQ_faithful_of_fullyFaithful`, `KEquivOfMapQIsEquivalence` | The specific stage equivalences and finite-module equivalence |

The source inspection found elementary matrix commutator relations, but no
stable Steinberg presentation, universal-central-extension comparison with
actual K2, or applicable degree-two homotopy/homology theorem. The Coxeter
Matsumoto name in mathlib is unrelated. Hurewicz *fibration* APIs do not supply
a degree-two Hurewicz isomorphism.

## Q1: determinant on the original field K1

### Q1a. Stable algebra

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

Proposed owner: `Quillen/Algebra/Group/StableFieldDeterminant.lean`; isolate a
new general finite-matrix lemma under the existing Aglib matrix candidate
owner only if it is needed. This algebraic endpoint is useful but is not Q1.

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

The remaining marking requires a geometric proof. The R5 module
`QuillenSourceFieldConstructors` defines `positiveModuleMatrixCubeClass` as the
literal coordinate transpose of its capped Q automorphism cube. Its existing
`positiveModuleMatrixCubeClass_eq_neg` proves a relation to its zero-first
class, not to the native completion class. Migrate only the needed general
Q-cylinder/cube construction to a native owner, then compare the mapped
stable automorphism loop, the actual completion-to-Q track, the cap, and the
loop-degree shift. Prove the equality of represented classes before inferring

```text
D_Q (positiveMatrixCube g) = GeneralLinearGroup.det g.
```

Inspect the two cube coordinates and the existing inner-loop reversal
explicitly; the sign cannot be fixed by naming an inverse equivalence.
Return an R5 adapter identifying its literal cube with the native term. Until
this is proved, report the quotient-Q determinant as unmarked and Q1 as open.

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
`closedSupportGEquiv`, then Q2, only in the needed K1 degree. The supported
stalk quotient and its fullness/essential-surjectivity proofs are separate.
R5's label `J2` here denotes a second-support stratum in K1, not degree two.

## Q4: the characteristic-zero Matsumoto phase

Use the same unit tensor quotient as R5's `MilnorK2.Basic` and preserve its
`symbol` and `map`; migration requires a transparent identification or an
explicit symbol-preserving comparison. Do not replace it silently by another
presentation.

The algebraic track constructs the stable Steinberg group from elementary
generators and all defining relations, its surjection to the actual stable
elementary subgroup, centrality of its kernel, and its universal property.
For the field case prove that this kernel has precisely the bilinear
Steinberg-symbol presentation. Kernel generation and relations are both
required for an equivalence; generation alone supplies only a surjection.

The topological track must identify that kernel with
`pi2(ZeroComponent F)`, naturally under field maps. One route constructs the
universal central extension of `E(F)` from the homotopy fiber of the actual
plus map and proves its kernel is pi2; another constructs a degree-two
Hurewicz/group-homology comparison on the relevant simply connected cover.
Either route needs new mathematics beyond the existing perfectness and
commutator lemmas. Determine a bounded construction before expanding the
topology library. A record assuming this comparison would leave Q4 open.

Compose the two tracks with the existing positive K2 Q comparison, opposite
and finite-module transports. Prove naturality and the positive marking of
the resulting `mu_+` on actual symbols. This is the acceptance boundary for
Q4, not merely the definition of a Steinberg group.

## Q5: low-degree actions, signs, and the origin DVR

Construct only the `(1,1)` field/module action and `(0,1)` supported-object
action needed by the inverse-symbol boundary. Reuse existing self-track
operations where applicable, but prove additivity in the automorphism/unit
variable and compatibility with the actual localization nullhomotopy.
Preserve the same `mu_+` and prove its marking on ordered field symbols.

Derive the raw boundary and then its corrected version through the fixed
`D_Q`, `mu_+`, `T`, and `N`. Check both ordered inputs `{u,pi}` and `{pi,u}`
and the scalar calibration using actual representatives. A free sign choice
or unrelated automorphism is not an acceptable calibration.

For the actual smooth-curve origin DVR, construct unit-pair classes in its
original K2 and prove generation. A useful route is unit-symbol generation
of the tame kernel in its fraction field, together with an independently
proved injection of the DVR K2 and actual boundary compatibility. This route
must discharge that injection rather than assume it from residue vanishing:
the residue field has characteristic zero and its K2 need not vanish.
An alternative Dennis--Stein/unit-generation argument must prove the needed
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

## Parallel implementation after this plan

| Branch | Owned scope | First acceptance boundary | Dependencies |
| --- | --- | --- | --- |
| A | `Algebra/Group/StableFieldDeterminant.lean`, any specifically assigned matrix helper | Stable determinant, field kernel, quotient equivalence, naturality | Existing stable algebra and mathlib elimination |
| B | `Aglib/CategoryTheory/Pi/{Abelian,FiniteSupport,FiniteStages}.lean` and its family guide | Same finite-support object, exact evaluations, stage restriction/extension equivalence | Existing general R5 candidates, read-only |
| C | Exact-product general candidate and `KTheory/FiniteSupport/FiniteProduct.lean` | Original Q-projection finite-product equivalence, including empty product | Existing Waldhausen product and Q/S exact naturality |
| D | `KTheory/Field/` positive projective/module comparison leaves | Canonical quotient-Q transport and exact remaining cube-marking obligation | Existing completion comparison; A for determinant endpoint |
| Principal | This plan, shared facades, consumer integration, and Q2c/Q2d allocation | Actual filtered Q diagram, direct-sum theorem, integrated Q1/Q2 review | B and C; D for marked Q1 |

Workers may investigate/prove only their assigned branch, with scratch outside
production for incomplete work. They must not update manifests, shared facades,
the Git index, or another branch's files. Package/cache writers remain serial;
coordinate focused compile slots before a missing dependency can trigger a
shared build. Parallel source authoring does not require parallel Lake writers.
Q3 starts when its genuine prerequisites are available. Q4 can receive a
bounded independent derivation after the first branches are underway; it must
not consume Q1/Q2 execution by rebuilding general higher K-theory.

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
exclude caches and exploratory output. Do not push.

## Classical reference locators

[Weibel, The K-book, chapter III](https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.III.pdf):
1.1.1--1.2.2 for determinant and field elimination, 5.4--5.5 for universal
central extensions, 6.1 for the symbol presentation, and 6.1.1 for finite fields.

[Chapter IV](https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.IV.pdf):
1.7.1 for the classical degree-two comparison, 6.4 for product/filtered-union
behavior, and Exercise 7.9 for the automorphism representative. These locate
the mathematics; they do not discharge the native constructions above.

[Chapter V](https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.V.pdf), 6.6--6.7.3,
locates the Dedekind localization tail and specialization. Source conventions
must be compared with the library's actual maps before transporting signs.
