# Remaining field K2 and DVR proofs

This is the revised investigation and execution plan requested on 2026-10-18.
It refines the remaining Q4/Q5 phase of
[Low-degree field support](LowDegreeFieldSupport.md). The target is the
original, positively marked Milnor-to-Quillen map. Proposed constructions and
theorem names below are proof obligations, not declarations already supplied
by the library.

## Objective, basis, and current boundary

The published native checkpoint at this investigation's start was
`35ec263c28a784c766dc142257b1f3806029aff6`, merged into `main` and verified on
the remote. Lean is `v4.34.1`, mathlib is
`d13f23b723b8a846827a245b89c10fc7d3f11612`, and Aglib is
`16aa08a90198d76be0bec47dd640b5c992acd9d7`. Continue in the separate
`codex/low-degree-field-support` worktree. R5 remains read-only; its adapter
proposals are separate products. The governing R5 rule source is
`a9236feda5b7c1acdf52d7eda3941b35672c41b4`.

Use Aglib's actual `MilnorK.K F 2`, its `MilnorK.twoEquiv F`, and its supplied
symbol, scalar-extension, and tame-residue interfaces. There is no new Milnor
foundation to implement. Characteristic-zero fields are the required Matsumoto
scope. An all-field proof is welcome only when the same argument supplies it;
finite-field vanishing is already independently complete.

| Branch | Current mathematical evidence | Remaining work |
| --- | --- | --- |
| Q1--Q3 | Native results, original-map markings, scoped checks, independent acceptance, and publication | Application adapters remain separate |
| Q6 | Actual finite-field projective/module/public scheme K2/G2 vanishing, including F2 and F3 | None for the requested degree-two endpoint |
| Q7 | Native kernel intersections, finite-residue generic G2 injectivity, and conditional finite-family lifting | Generic G1 injectivity remains the explicit arithmetic premise allowed by the assignment |
| Positive field symbol marking | Native seven-module package independently accepted and normally built; public pair theorem needs only `Field F` | None for the ordered positive pair theorem |
| Original Steinberg/fiber comparison | Native all-field injectivity and bijectivity independently accepted; normal leaf builds and affected checks pass | None for the original comparison |
| Milnor-to-Steinberg injectivity | Kernel generation and surjectivity are native; several finite matrix suppliers compile in scratch | The principal open mathematical problem of this plan |
| DVR tame compatibility | Native canonical and supplied-fraction-field statements independently accepted and normally built, without a residue section | None for the marked boundary theorem |
| DVR unit-pair generation | Native lower G2 and original Spec(A) K2 generation independently accepted and normally built with an actual residue ring section; generic/closed pair values also proved | Negative inverse normalization awaits Matsumoto; broader R5 records remain separate |

The accepted non-Matsumoto sources in this tree were added after commit
`35ec263c`. M1--M5 below remain scratch constructions until their missing
composition is proved. Strict compilation alone does not give an independent
original-map verdict.

Four separately accepted native providers have passed normal leaf builds:
`HomotopyFiber.PeriodicConnecting`,
`LowDegreeScalarAction.MixedProjectiveNaturality`,
`LocalCoefficients.SecondHurewicz`, and
`LocalCoefficients.SecondHurewiczInjective`.
No full Hurewicz isomorphism is needed for the selected route.

### Current acceptance checklist

This checklist distinguishes completed suppliers from their unfinished
composition. It is the operative progress report for this plan.

| ID | Current acceptance | Exact remaining obligation |
| --- | --- | --- |
| M1 | Twelve-source coroot torus/automorphism package, 221 declarations, independently accepted | Original Steinberg-word interpretation belongs to M4 |
| M2b | Actual marked type-A permutation presentation and kernel consumer, 110 declarations, independently accepted; used by the accepted normalizer core | No open presentation obligation; the actual matrix projection remains in M2 |
| M2 | Fifteen-source permutation-group core, 186 declarations, independently accepted; signed-section, covariance and diagonal-onto suppliers separately accepted; actual matrix join strictly compiles | Complete the join's full checks and independent review of the actual monomial projection and central kernel |
| M3a | All three canonical equal/opposite/distinct matrix branches and their actual finite-Bruhat suppliers independently accepted; 124 new declarations pass scoped checks | Supply the arbitrary-input reduction and lifted join in M3b/M4 |
| M3b | Actual all-rank matrix Bruhat suppliers are available | Reduce arbitrary upper factors/state inputs to the canonical branches and define the complete lifted actions |
| M4 | Conditional characteristic-zero, rank-at-least-five root-lifting reduction independently accepted, 52 declarations; no actual finite detector family is released | Construct the actual central extension, additive root sections and diagonal covariance; prove the original ordered-defect value with faithful coefficient readout |
| M5 | Conditional stable transfer independently accepted, 63 declarations | Supply M4's actual family with one common rank threshold |
| T | Native original all-field Steinberg/fiber and kernel/K2 endpoints independently accepted and normally built | None for the original comparison; Milnor inverse normalization still needs M4/M5 |
| D | Native lower-G2 and original Spec(A) K2 generation, tame compatibility, and generic/closed pair values independently accepted and normally built | Negative inverse normalization and R5 adapters retain their separate boundary |

Thus the main missing composition is M2, then M3b/M4, then application of
the proved M5 reduction. Counts of completed lemmas are not a percentage
estimate of the remaining mathematical difficulty.

## Research findings and applicability

The primary classical source is Hideya Matsumoto, *Sur les sous-groupes
arithmetiques des groupes semi-simples deployes*, Ann. Sci. ENS (4) **2**
(1969), 1--62, [DOI and original article](https://numdam.org/articles/10.24033/asens.1174/).
The following exact locators were inspected in the
[original PDF](https://www.numdam.org/article/ASENS_1969_4_2_1_1_0.pdf):

| Locator, printed pages | Relevance and boundary |
| --- | --- |
| Chapter II, Theorem 5.10 and Corollary 5.11, 30--31 | Infinite-field central-extension/symbol classification; type A is the relevant non-symplectic case |
| Lemmas 6.1--6.3, 33--36 | Extended Weyl relations and their signs; a split permutation action does not replace them |
| Lemmas 6.5--6.6, 38--40 | Torus automorphisms and the normalizer construction |
| Lemmas 6.7--6.11, 40--43 | Actual transformations of the lifted Bruhat set and rank-two reduction |
| Lemmas 7.1--7.2 and the following calculation, 44--47 | Left/right transformation comparison, including the non-generic pivot branches |

Printed pages 38--40 were also checked visually from the original page images.
The downloaded PDF has SHA256
`4ac51e1290e2ab3c633d5a55378eb078f88d824bb3d28aac3585fce0595db5ca`.
In Lemma 6.5 the displayed generator formula is for the inverse automorphism;
the square is an inner conjugation, not an involution. The central section of
a nonsimple coroot must be reconciled with the original Steinberg word.

These guide proof obligations; none is imported as a Lean axiom. The original
infinite-field scope suffices in characteristic zero. No general Chevalley,
symplectic, topological-central-extension, or congruence-subgroup programme is
part of this implementation.

Charles Weibel, *The K-book*, III, Theorem 6.1 and Definition 6.2, give the
field symbol statement; its proof is referred to Milnor, section 12, rather
than supplied there. The distinction matters when selecting an implementation
route. See the author's
[Chapter III](https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.III.pdf),
printed chapter pages 48--49. Its tame-symbol conventions must be compared
with the existing native ordered unit/uniformizer formula, not copied by sign.

The pinned local code supplies more than the initial assignment baseline:

| Exact source | Available input |
| --- | --- |
| `Quillen/Algebra/Group/StableSteinberg.lean` | The original finite-rank-labelled presentation; root addition, disjoint commutators, ordered chain commutators, and stabilization are its four relator constructors |
| `StableSteinbergUniversal.lean`, `StableSteinbergCentrality.lean` | Actual universal central lifting and central kernel |
| `StableSteinbergSymbols.lean` | Original ordered defect, direct Aglib symbol lift, and positive commutator marking |
| `StableSteinbergKernelGeneration.lean` | `defectSubgroup_eq_kernel`, `kernel_le_stage_two`, and `milnorToKernel_surjective` |
| `KTheory/Field/MilnorKTwoComparison.lean` | The original Milnor-to-projective/upper-module maps and their field-map squares |
| `KTheory/Plus/StableFiberPerfectness.lean` | Actual stable-fiber perfectness; no external perfectness premise remains |
| Aglib `KTheory/MilnorK/CompatibilityK2.lean` | Ordered symbols, bilinearity, `twoEquiv`, and field-map compatibility |
| Aglib `KTheory/MilnorK/K2/Symbols.lean` | Steinberg, self, and skew relations plus symbol lifting/uniqueness |

The pinned mathlib Coxeter sources supply basic braid equalities and length
machinery. `GroupTheory/Coxeter/Basic.lean` still lists the full reduced-word
Matsumoto theorem as a TODO. Its name refers to Coxeter words, not the field
K2 theorem. No unlocated reduced-word theorem or full finite symmetric-group
BN-pair interface may enter a proof silently. Use explicit type-A matrix
arguments or make the required word argument a separately proved obligation.

## Why the previous normalizer models do not close the gap

The scratch split monomial construction has an explicit disjoint-Weyl
commutator equal to the Milnor coefficient `{-1,-1}`. The original Steinberg
words commute. The same scratch investigation constructs a genuine real
Milnor sign detector for which this coefficient is nonzero. Thus an injection
of coefficients into that split model does not extend it to the required
original group.

The positive-quadratic-form Clifford graph repairs that disjoint relation.
Its proposed original-Weyl normalization has a further mismatch diagnosed by
hand; that diagnosis is not a released formal counterexample to every possible
repair of the constructed group. In particular, a free
diagonal coordinate outside a Weyl pair has an unwanted sign contribution.
The appropriate geometric target is determinant one. The proposed switch
to a negative quadratic form has not been compiler-checked and is not a
released supplier.

Preserve these checked models and obstructions as diagnostics. Reusing their
finite Bruhat geometry does not import their invalid global-extension claim.
Do not continue alternating Clifford signs without first proving the complete
finite normalization interface below.

Universal centrality, generation of the kernel, the newly proved Schur/fiber
comparison, and positive product marking do not themselves prove injectivity
of the Milnor map. A faithful detector for the original Milnor coefficients
is still required.

## Fixed arrows and normalization tests

Write `M = MilnorK.K F 2`, `St` for the original stable presentation, and
`E` for the original stable elementary subgroup. The selected arrows are

```text
M --milnorToKernel--> ker(St -> E)
  --steinbergKernelToRightProjectiveKTwo--> original right-projective K2
  --rightProjectiveUpperModuleKEquiv--> original upper finite-module K2.
```

Keep `w(a) = x01(a) x10(-a^-1) x01(a)` and `h(a) = w(a) w(-1)`.
The required value of the Milnor symbol is the original ordered defect
`h(a) h(b) h(ab)^-1`. Its commutator marking is
`[h01(a), h02(b)] = c(a,b)`. The final positive field theorem is exactly

```lean
Field.milnorToUpperModuleKTwo F (MilnorK.symbol ![a, b]) =
  Additive.ofMul (FieldSymbols.unitProduct F a b)
```

Every normalizer prototype must prove, at its actual source elements:

1. `W(-a) = W(a)^-1` and `H(a) = W(a) W(-1)`.
2. The positive ordered defect and the positive `01,02` commutator above.
3. Diagonal and Weyl conjugation with the actual signed permutation matrices.
4. Disjoint Weyl commutation and the adjacent type-A rank-two relation.
5. The central `{-1,-1}` terms at parameter `-1`; they cannot be set to zero.

These are universal identities. Small examples and a real sign example are
useful regression consumers, not a replacement for their proofs.

## M1: root-coordinate torus and its actual Weyl automorphisms

Start with the determinant-one torus in simple-coroot coordinates. For
`n >= 3`, the coordinates are units `s_0,...,s_(n-2)`, representing the
product of diagonal coroot matrices `h_(i,i+1)(s_i)`. This avoids a free
determinant coordinate.

A concrete candidate on `M × (Fˣ)^(n-1)` has coefficient cocycle

```text
C(s,t) = sum_i {s_i,t_i} - sum_(i+1 < n-1) {s_(i+1),t_i}.
```

Here every bracket is the supplied ordered Aglib pair symbol. This displayed
formula is a proposed construction requiring its own proof, not an accepted
replacement for the older coordinate model. Prove normalization, the cocycle
identity, associativity, inverse formulas, and injectivity of `m |-> (m,1)`.
Derive the diagonal matrix map and its literal simple-root values.

The first two roots must give positive defect `{a,b}` and the positive
commutator of the coroots `01` and `02`. The latter has coroot coordinates
`(b,b,1,...)`. Check those calculations before building a larger group.

Construct the automorphisms implementing conjugation by the signed simple
Weyl matrices. Their action on root lifts must include the central correction;
an honest coordinate permutation of order two is not automatically correct.
Prove the square as the appropriate inner automorphism, distant commutation,
and the adjacent braid identity on every generator and coefficient. Explicitly
declare whether a formula describes an automorphism or its inverse.

**Output:** one actual torus group, coefficient injection, matrix projection,
and proved signed automorphisms, with exact normalization equations. A family
of unspecified automorphisms satisfying the target laws is not an output.

## M2: a faithful lifted determinant-one normalizer

Extend the M1 torus by signed simple Weyl lifts. Use the type-A part of the
classical extended-Weyl construction as the starting route. If a concrete
Clifford realization is retained, it must first satisfy the M1 normalization
tests and be compared to the actual signed matrix lifts.

The required result is a group `Ntilde_n` with an actual surjective map to the
finite determinant-one monomial matrices and central kernel, containing the
proved torus and its Milnor coefficient subgroup. The coefficient injection must survive the actual
quotient. Prove this using the identified graph/kernel intersections, not by
assuming the desired normal form or a central-extension record.

Retain actual lifts of `W_i(-1)` and `H_i(t)`, their conjugations, squares,
distant relations, and adjacent rank-two relations. Check the relationship
between the `01` and `02` sections. Keep characteristic assumptions explicit.

**Acceptance:** all five normalization tests above hold as equalities in the
constructed group, with the original Milnor coefficients embedded faithfully.
No extension of the whole stable GL group is requested. Classifying an
auxiliary cover's entire kernel is unnecessary if coefficient faithfulness
and all required relations have been proved directly.

M1 and M2 share the same mathematical owner. Their signs and quotient
identifications are too coupled for independent concurrent implementations.
The pure type-A permutation-presentation subproblem M2b has a separate owner:
its marked square/distant/braid presentation is now proved equivalent to the
actual finite permutation group. It supplies the quotient-kernel step without
a generic Coxeter reduced-word theorem. A concrete torus-times-permutation
action certifies the torus injection; the source generator with square
`H_i(-1)` is `W_i(-1)`. The original `W_i(1)` has square `H_i(-1)^-1`.

## M3: matrix Bruhat data and the complete rank-two branches

Reuse the frozen scratch finite-matrix results: actual all-rank Bruhat
existence, uniqueness of its monomial factor, upper-unitriangular invariance,
diagonal equivariance, and left/right simple-Weyl updates. They retain genuine
finite GL units and can be restricted to determinant one. Their canonical
packaging and independent review remain separate.

Extract a projection `v(g)` to the actual monomial factor. Establish the
precise update formulas with the same `W(1)`/`W(-1)` convention as M1/M2.
Work with original matrix multiplication throughout.

For the left/right rank-two comparison, separate the cases where the
transported simple roots are distinct, equal, or opposite. In the opposite
case, cover zero parameters and the vanishing crossing denominator before
using any inverse. The existing `crossing_diamond` proves only its displayed
nondegenerate symbol equality. It does not prove the missing matrix cases or
the equality of transformations on all states.

**Independent output M3a:** exact matrix factorization and pivot branch
lemmas, including the degenerate cases, without an assumed lifted normalizer.
This can proceed in parallel with M1/M2.

**Join M3b:** once M2 is fixed, define the lifted state set

```text
S_n = { (g,ntilde) | g is an actual determinant-one matrix,
                      projection(ntilde) = v(g) }.
```

It is inhabited at the identity and has a faithful Milnor-translation action.
Define the actual upper-unipotent, torus, and simple-Weyl permutations of
`S_n`. Prove their inverses and state-preservation. Each branch uses the
previously proved matrix update, with its literal coefficient correction.

## M4: finite actions of the original Steinberg relators

The selected minimal target is a faithful coefficient action, rather than a
classification of every central extension. For every sufficiently large
finite rank, construct actual permutations `R_ij(a)` of `S_n` satisfying:

```text
R_ij(a) R_ij(b) = R_ij(a+b)
[R_ij(a),R_kl(b)] = 1                 if j != k and l != i
[R_ij(a),R_jk(b)] = R_ik(ab)           for distinct i,j,k.
```

The disjoint condition includes roots sharing a row or a column; checking
only four distinct indices is insufficient. These must be equalities of
permutations on every state, not just equations of their matrix projections.

First prove the actual left/right transformations commute on every state,
using M3's complete branches and the lifted torus identities. Their regular
action supplies an actual group over the determinant-one matrix group, with
central kernel equal to the faithful Milnor translations. Define additive
root sections by conjugating the actual upper-root sections and prove their
covariance under lifts of the actual product-one diagonal matrices.

There is now an independently accepted conditional reduction for this last
root-relation step, covering characteristic zero and matrix dimension at
least five. Each matrix-trivial commutator error lies in the central kernel.
A single balanced diagonal lift scales one input by two and fixes the other;
for a chain it scales the output root by the same factor. Product-one weights
use a coordinate outside the at most four root indices. Additivity and the
shared-row relation then make conjugation square the error, while centrality
fixes it. Thus the error is one. Identical roots follow directly from
additivity. No torsion-free hypothesis on the Milnor group is needed.

The checked reduction has 52 defining-origin declarations, including a literal
GL5(Q) interface client. It does not construct the required extension, root
sections, or diagonal covariance. Applying it therefore waits for the actual
M3b group; it replaces a separate general reduced-word argument, without
removing the lifted left/right coherence obligation. Any alternative proof
using reduced words must supply word independence itself; the missing mathlib
theorem is not an available supplier.

Compute the original words `w(a)`, `h(a)`, and `h02(b)` in this action and prove
that the ordered defect acts as translation by exactly `{a,b}`. This is the
essential coefficient detector. Do not introduce a record with the desired
defect formula as an unproved field.

**Output:** actual finite permutation actions with all three relators and
positive ordered-defect equality proved. A universal central extension of the
finite SL group and unstable Steinberg embedding injectivity are not needed.

## M5: stable transfer without a new stabilization-coherence project

There is a useful principal-selected reduction that can be proved separately
from M1--M4. A detector at every sufficiently large finite rank can be
assembled through an eventual quotient of a product of groups. Compatible
maps between the state sets are then unnecessary.

Let `P = product_n Perm(S_n)` and let `Z` be the subgroup of families that
equal the identity for all sufficiently large `n`. Prove that `Z` is normal
and form the actual quotient `P/Z`. This is a dependent product; an ordinary
constant-target `Filter.Germ` API does not directly provide it.

For an original generator `(r,i,j,a)`, use `R_(cast i)(cast j)(a)` in coordinate
`n >= max(r,5)` and identity below that threshold. Verify each of the four
constructors of `StableSteinberg.Relator` after passing to the quotient:
the first three hold eventually by M4, and the stabilization relator holds
because the actual cast indices eventually coincide.

For `m : M`, use the family of translations by `m`. These give a homomorphism
into `P/Z`. It is injective: eventual identity permits evaluation at one
sufficiently large identity state, and finite coefficient faithfulness gives
`m = 0`. Show that the composite with the original `milnorToKernel` is this
homomorphism by its proved ordered pair values and supplied Milnor generation.
This proves injectivity of the original Milnor map.

**Boundary:** the eventual-quotient reduction is valid only with actual M4
actions and markings. A conditional reduction is not the completed Matsumoto
theorem. Keep the temporary input explicit and replace it with the constructed
family before exposing the final endpoint.

This approach avoids proving injectivity of finite Steinberg stabilization,
normalizer stabilization, or a filtered colimit of permutation actions. If
literal stabilization is already available at no extra cost, it is an
alternative implementation of this transfer, not an additional milestone.

The conditional M5 reduction now has strict compilation, complete scoped
checks, and independent ordinary acceptance. Its frozen scratch source is
`StableDetectorTransfer.lean`, SHA256
`3197412e3f2de6717d4c662e7ba8393ad163bb68f6cb0ff9907648c6c5bb8e0c`.
It needs one common rank threshold and readout for every Milnor coefficient.
The state types need not have finite cardinality. M4's actual detector family
remains open; this conditional source is not yet adopted into the library.

## T: finish the actual Steinberg/Quillen comparison

The geometric/singular proof route is now independent of M1--M5. Its suppliers
construct the actual commuting square and whole periodic capping homotopy,
the original connecting commutator formula, and the marked Hurewicz map.
The actual square cycle is lower triangle `00,10,11` minus upper triangle
`00,01,11`.

The final detector retains these signs:

```text
original Steinberg defect -> inverse transported target sphere
                         -> negative oriented square class
                         -> negative integral bar torus
                         = original algebraic Schur marking.
```

The final equality on all kernel elements uses the proved all-rank defect
generation. Preserve the original cover projection, `basepointPath`,
`pathTransport`, connecting map, and `zeroCompletionPositiveKEquiv`.
No source simple-connectedness or full Hurewicz isomorphism is required.

The final composite and its actual consumers have independent complex
mathematical acceptance in the canonical fifteen-module package. The native
bar/Schur and singular providers occupy their algebraic/topological owners;
the documented prose sign of `W d2 - id` is corrected without changing the
accepted proof. Provider-first normal builds and the fresh 595-declaration
normal audit pass, with a joint import of the prior and new 31 defining roots.

After T and M5, combine injectivity with existing surjectivity and define the
positive field equivalence from the same original homomorphism. Its field-map
naturality follows from the existing original-map square. Inverse naturality
must be derived from that square and bijectivity, not selected independently.

## D: DVR boundaries and the origin application

These branches use the positively marked *surjection*, so they do not wait
for Matsumoto injectivity. This is an important dependency separation.

1. Define the lower field map using the original upper map followed by the
   inverse canonical same-category `smallKUniverseEquiv`. Prove its literal
   value on `DvrSymbols.loweredUnitProduct` and discharge surjectivity from
   the actual stable-fiber perfectness theorem.
2. Define the observed boundary using the original local DVR boundary, the
   canonical residue promotion, and the original field `moduleDet`.
   For any Milnor class, lift its tame value to a local unit, subtract the
   ordered `{unit,uniformizer}`, and use the supplied tame-kernel unit span.
   Unit-unit boundary zero and the proved positive unit/uniformizer formula
   give compatibility on the entire original Milnor source.
3. Obtain the reverse ordered formula from actual Milnor skew symmetry and
   the same marked map. Test both orders with the retained original arrows;
   retain the given fraction field through `fractionFieldRestrictionExact`.
4. With an actual residue ring section, prove original generic G2 injectivity
   from `SplitResidueDvr`. Lift a generic class along the proved Milnor
   surjection. Boundary zero implies tame zero, hence membership in the
   unit-symbol span. Lift those pairs to original lower G2 of the DVR and use
   the proved generic injectivity to reflect generation.
5. Construct the section for the actual smooth-curve origin from its
   coefficient-field map and residue identification. Transport to projective
   K2 only through an actual applicable regular K/G comparison. A result on
   lower G2 alone does not silently inhabit a projective K2 record.
6. Prove the original generic and closed scheme-K pullback values of the same
   genuine unit pairs. For the given fraction field and the actual residue
   field, follow the original K pullback by the field's original KToG/affine
   comparison and identify the result with the lower Milnor map of the mapped
   ordered units. This part does not need Milnor injectivity. Apply the final
   negative inverse normalization only after that equivalence is proved.

The frozen scratch pair supplies steps 1--4, including a given-field boundary
theorem and an actual affine-line origin section over arbitrary fields, with
Q/F2/F3 clients. Strict compilation, scoped lint, its full 183-origin axiom
audit, and independent mathematical review pass. The general origin and R5 normalization
adapters remain separately identified consumers. They must retain
`T = -D_Q after F_1` and `N = -mu_+^-1 after F_2` after the equivalence is
available. No arbitrary local-ring Milnor presentation is requested.

The bounded D5 scheme endpoint has independent acceptance and normal builds,
with all scoped checks for 91 declarations, including real origin clients. It uses the native
`Scheme.KToGPIDEquiv` for the actual Dedekind localization and actual positive
scalar/cube unit pairs, with their literal KToG/affine image. D6 has independent
acceptance and normal builds for the original generic/closed K-pullback
values, with 38 checked producer declarations. Normal-artifact final checks
cover the complete non-Matsumoto batch; direct finite-projective aliases and
broader R5 records remain separate.

## Parallel execution and acceptance order

Start new mathematical work only after this investigation and plan are written.
Use the following disjoint assignments, with fresh bounded context:

| Work package | Executor selection | Exact write responsibility | First acceptance condition |
| --- | --- | --- | --- |
| M1/M2 | Mathematics complex, Astra/max | New scratch root-coordinate torus/normalizer family; frozen older models read-only | Actual root-coordinate torus and signed automorphisms satisfy all finite normalization tests |
| M3a | Mathematics, Sol6.1/max | New scratch matrix-only rank-two branch family | Complete pivot-case formulas on original finite matrices, reusing fixed Bruhat suppliers |
| M5 reduction | Mathematics, Sol6.1/max | New scratch eventual-product transfer | Four original relators and faithful coefficient transfer proved with exact finite-input boundary |
| T | Existing complex mathematical owner, then independent complex review | Final frozen original-map detector and its evidence | Original all-field comparison injectivity, then source-bound independent acceptance |
| D | Existing mathematical owner, then independent ordinary review | Fixed two-leaf DVR pair and real section client | Section-free boundary compatibility distinguished from section-dependent generation |
| Accepted-source production | Support complex, Sol6.1/high | Separately assigned canonical scratch packaging | Strict native-format sources, exact proof provenance, complete origin coverage, actual consumers |

The principal owns M3b/M4 integration and the final map/equivalence decisions.
M1/M2 and M3a join only at a fixed normalization interface. Return concrete
failed identities or counterexamples to the principal immediately; preserve
the last useful checked state and revise the route. Do not build successive
conditional certificates instead of the actual missing construction.

Workers remain read-only outside explicitly assigned scratch paths. The
principal is the only native package/cache and Git writer. Use
`/private/tmp/r5-investigations/quillen-low-degree-20261018/` for scratch, with
separate real directories and guarded output realpaths/inodes. No compiler
output may traverse a borrowed native symlink.

At a coherent fixed result, run only the affected strict leaf/provider checks,
15 native scoped linters and text checks, meaningful field/original-map
clients, and complete defining-origin transitive axiom audits. Include private
and generated declarations, `env.checked`, and only `propext`,
`Classical.choice`, and `Quot.sound`. Reuse matching source/pin evidence;
do not thin an inventory to a predicted declaration count.

Independent mathematical acceptance precedes release of a new load-bearing
closure. Canonical regrouping must preserve exact statements/proofs through
a recorded map and expose any new proof obligation. Final native adoption uses
normal provider-first builds, affected facade generation/layout checks, and
the smallest actual downstream consumer. Whole-root rebuilding is not a
normal checkpoint requirement.

Record separately: proved mathematics, independent acceptance, native source
adoption, normal build/test evidence, and publication. The final Q4 completion
claim requires the same positively marked equivalence on the original groups,
its literal symbol values and field-map squares, with no remaining detector,
central-extension, normalization, perfectness, or generation premise.
