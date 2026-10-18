# The original characteristic-zero Matsumoto construction

[Injectivity](Injectivity.lean) proves
`Quillen.StableSteinberg.milnorToKernel_injective_charZero` for the existing
`milnorToKernel F`, with only `[Field F] [CharZero F]`. The proof constructs
the finite roots, central extension, original-word marking and coefficient
readout used by the actual stable presentation. No detector or marking premise
remains in this endpoint. The lower finite constructions below have their own
all-field scopes; their existence does not remove characteristic zero from
the final injectivity theorem.

## Coroot torus and signed Weyl automorphisms

[Torus](Torus.lean) uses the existing ordered Aglib coefficient group
`M = MilnorK.K F 2`. With `r` simple-coroot coordinates `s,t : Fin r → Fˣ`,
its explicit cocycle is

```text
C(s,t) = sum_i {s_i,t_i} - sum_(j+1 < r) {s_(j+1),t_j}.
```

The multiplication on pairs of diagonal data and coefficients adds the two
coefficients and `C(s,t)`. Bilinearity gives normalization and the cocycle
identity; the native group includes the actual inverse formulas. The map
`m ↦ (1,m)` is injective and central. The matrix projection is the product of
the literal simple-coroot diagonal matrices, so it has determinant one and
retains their exact simple-root values; there is no free determinant coordinate.

In matrix dimension at least three, the first simple coroot has positive
defect `{a,b}`. The coroot `02` has coordinates `(b,b,1,...)`, and its
commutator with coroot `01` gives the same positive ordered pair. These actual
coordinates fix the later original-word marking.

[Weyl](Weyl.lean) constructs signed simple-Weyl automorphisms with their
Milnor-valued central corrections. Their squares are the specified inner
automorphisms, and their distant and adjacent braid relations hold on the
actual torus. [LiftedWeyl](LiftedWeyl.lean) realizes them as transformations
of the concrete torus/permutation state, rather than assuming an unspecified
family of automorphisms satisfying the desired laws.

## Faithful genuine normalizer

[Normalizer](Normalizer.lean) generates `LiftedNormalizer F r` by the actual
torus transformations and signed simple-Weyl transformations. The state action
proves `normalizerTorus_injective` and `normalizerCoefficient_injective`.
The [adjacent permutation presentation](../../../../Aglib/Algebra/Group/Perm/AdjacentPresentation/README.md)
identifies the quotient by the torus with the actual finite permutation group;
it supplies the square/distant/braid quotient-kernel step without an assumed
general reduced-word theorem.

[MatrixBasics](MatrixBasics.lean) and [NormalizerMatrix](NormalizerMatrix.lean)
give the actual matrix homomorphism. Its range is precisely the determinant-one
monomial matrices, and its whole kernel is the faithfully embedded central
Milnor coefficient subgroup. Faithfulness survives the constructed quotient;
it is not assumed as a normal-form or central-extension input.

The normalizer retains the lifts `W_i(-1)` and `H_i(t)`, their conjugations,
squares, distant relations and adjacent rank-two relations. In these conventions
`W_i(-1)` squares to `H_i(-1)`, whereas `W_i(1)` squares to its inverse.
[TorusTransporter](TorusTransporter.lean) and
[WeylTransporter](WeylTransporter.lean) compare the actual lifted elements over
their displayed matrices, including positive transport of the specified
adjacent ordered pair. Pure signed monomial recurrences remain in the
[generic signed-section family](../../../../Aglib/LinearAlgebra/Matrix/GeneralLinearGroup/SignedSection/README.md);
the Milnor-valued normalizer and its faithfulness belong here.

## Lifted Bruhat states and the complete extension

The [generic matrix Bruhat family](../../../../Aglib/LinearAlgebra/Matrix/Bruhat/README.md)
supplies literal factorization, the monomial projection `v(g)`, and the
equal/opposite/distinct root-update branches, including zero parameters and
vanishing crossing denominators. The arbitrary-matrix reduction preserves the
same four monomial factors for `g`, `W_i(1)g`, `gW_k(-1)` and
`W_i(1)gW_k(-1)`. A nondegenerate crossing-symbol identity alone is insufficient
for the full state comparison.

[BruhatActions](BruhatActions.lean) uses the actual lifted states

```text
S_r = { (g, ntilde) | g is a determinant-one matrix,
                      projection(ntilde) = v(g) }.
```

They have the original identity state and a faithful Milnor-translation action.
The actual upper-unipotent, torus and simple-Weyl permutations retain their
inverses, state-preservation laws and literal coefficient corrections.
[BruhatCoherence](BruhatCoherence.lean) proves the lifted left/right comparisons,
using every matrix branch and the genuine torus identities, not just their
matrix projections.

[BruhatLeftGroup](BruhatLeftGroup.lean) and
[BruhatExtension](BruhatExtension.lean) form the actual left and right groups.
Every left operator commutes with the entire right group. Right transitivity
makes evaluation at the original base state injective on the left group.
Consequently the left-group projection covers exactly the determinant-one
matrices, and its **whole** kernel is the range of the faithful central Milnor
translations. These extension statements hold over every field. No universal
central-extension classification of finite SL or unstable Steinberg embedding
injectivity is needed.

## Actual all-root sections and common diagonal covariance

[RootSections](RootSections.lean) is an all-field construction from a central
projection covering determinant-one matrices, a specified torus lift, one
additive base-root section and its exact diagonal covariance. Conjugation
through a central kernel depends only on the projected conjugator. The
constructed determinant-one matrix transports therefore give additive sections
for every distinct ordered root, with the original elementary-matrix images.
The sections retain simultaneous covariance under one common product-one
diagonal lift; they are not unrelated choices of lifts for individual roots.

[Injectivity](Injectivity.lean) supplies this interface in the actual extension:
`bruhatBaseRootSection` is the upper `01` section, and `bruhatRootSections`
constructs all roots from it. Surjectivity onto determinant-one matrices,
base additivity and primitive covariance are native theorems about these
constructed objects. The general provider keeps its explicit inputs; the final
injectivity endpoint supplies them rather than exposing them as new premises.

## Central-error doubling and the three root laws

[FiniteRootLifting](FiniteRootLifting.lean) proves the root-law reduction for
characteristic-zero fields in matrix dimension at least five, using the actual
sections and common diagonal covariance. The desired identities are

```text
R_ij(a) R_ij(b) = R_ij(a+b),
[R_ij(a), R_kl(b)] = 1                 if j != k and l != i,
[R_ij(a), R_jk(b)] = R_ik(ab)           for distinct i,j,k.
```

The disjoint condition includes shared-row and shared-column roots, not only
four distinct indices. These are identities in the actual group and hence of
permutations on every state, not merely equalities after matrix projection.

A matrix-trivial commutator error is central. Product-one diagonal weights use
a coordinate outside the at most four root indices: a single diagonal lift
doubles one input and fixes the other, scaling the output root by the same
factor in the chain case. Additivity and the shared-row relations make
conjugation square the error, while centrality fixes it. The generic
[central-kernel doubling lemmas](../../../../Aglib/Algebra/Group/Hom/CentralKernel.lean)
then force the error to be one. Identical-root relations follow from additivity.
This argument needs no torsion-free hypothesis on the Milnor coefficient group.

## Positive marking of the original Milnor map

For units `a,b`, the original words are
`w(a) = x01(a) x10(-a^-1) x01(a)` and `h(a) = w(a) w(-1)`;
the original ordered defect is `h(a) h(b) h(ab)^-1`.
The finite `h01`/`h02` words and the constructed lifted-torus elements have
equal **GL projections**. They are not asserted to be equal lifts.
Central-kernel lift-independence identifies their commutators, and the explicit
coroot commutator gives translation by the positive ordered symbol `{a,b}`.
No equality between a finite defect and a finite commutator is assumed.

Only after constructing the eventual stable representation below does the
native `StableSteinberg.commutator_h_h02` identity identify this value with
the original ordered defect. The finite producer
supplies the matrix projections, torus commutators and readout for every
coefficient; a desired marking equation is not left as an unproved record field.
Universal centrality, kernel generation and positive product marking by
themselves do not prove Milnor-map injectivity; the faithful coefficient action
above supplies the necessary additional construction.

## Shifted finite family and eventual quotient

In [Injectivity](Injectivity.lean), detector rank `n` uses
`BruhatLeftGroup F (n+1)` acting on `BruhatState F (n+1)`, of matrix dimension
`n+2`. Original roots use two literal `Fin.castSucc` inclusions. The common
eventual cutoff is five. The finite coefficient operator has its actual
readout on the original identity state for every Milnor coefficient. Finite
rank does not assert that the state type has finite cardinality.

[DetectorTransfer](DetectorTransfer.lean) forms the dependent product
`P = product_n Perm(S_n)` and its quotient by the normal subgroup of families
equal to the identity for all sufficiently large `n`. An original generator
of rank `r` acts by its constructed finite-root operator for
`n >= max(r,5)` and by the identity below that threshold.

The four original `StableSteinberg.Relator` constructors hold in this quotient:
additivity, disjoint commutation and the ordered chain commutator hold
eventually by the finite laws; stabilization holds because the actual cast
indices eventually coincide. Compatible maps between state sets, normalizer
stabilization and injectivity of finite Steinberg stabilization are not inputs.

The family of translations by a coefficient defines a homomorphism to `P/Z`.
If its class is trivial, evaluation at one sufficiently large identity state
and finite coefficient faithfulness give that the coefficient is zero.
Positive ordered marking and the supplied Milnor generators identify this
homomorphism with the image of the **same original** `milnorToKernel`.
This proves its characteristic-zero injectivity with no residual finite-model
premise. The conditional eventual-product/detector interfaces retain their
stated hypotheses; the final provider discharges them with the constructed family.

## Field and DVR comparison boundary

The [field family](../../../../KTheory/Field/README.md) owns the original
right-projective and upper finite-module equivalences for `Field` plus `CharZero`,
their positive ordered marking and same-universe field-map naturality.
The [scalar-action family](../../../../KTheory/LowDegreeScalarAction/README.md)
owns the same negative inverse and the raw/inverse DVR determinant formulas.
All-field finite constructions do not supply an infinite positive-characteristic
Milnor equivalence or an arbitrary-DVR local Milnor presentation.

## Primary source locators and normalization warnings

Hideya Matsumoto, *Sur les sous-groupes arithmetiques des groupes semi-simples
deployes*, Ann. Sci. ENS (4) **2** (1969), 1--62:
[original article and DOI](https://numdam.org/articles/10.24033/asens.1174/),
[original PDF](https://www.numdam.org/article/ASENS_1969_4_2_1_1_0.pdf).

| Locator, printed pages | Relevance and boundary |
| --- | --- |
| Chapter II, Theorem 5.10 and Corollary 5.11, 30--31 | Infinite-field central-extension/symbol classification; type A is the relevant non-symplectic case |
| Lemmas 6.1--6.3, 33--36 | Extended Weyl relations and their signs; a split permutation action does not replace them |
| Lemmas 6.5--6.6, 38--40 | Torus automorphisms and the normalizer construction |
| Lemmas 6.7--6.11, 40--43 | Actual transformations of the lifted Bruhat set and rank-two reduction |
| Lemmas 7.1--7.2 and the following calculation, 44--47 | Left/right transformation comparison, including non-generic pivot branches |

The identified PDF has SHA-256
`4ac51e1290e2ab3c633d5a55378eb078f88d824bb3d28aac3585fce0595db5ca`.
In Lemma 6.5 the displayed generator formula is for the inverse automorphism;
its square is inner conjugation, not an involution. The central section of a
nonsimple coroot must match the original Steinberg word. The disjoint-Weyl correction `{-1,-1}` of a split monomial normalization
cannot be silently set to zero: the original words commute, and the genuine
extended-Weyl relations must be retained.

Charles Weibel, *The K-book*, III, Theorem 6.1 and Definition 6.2,
[printed chapter pages 48--49](https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.III.pdf),
locate the field-symbol statement and refer its proof to Milnor, section 12.
Their tame-symbol convention must be compared with the native ordered
unit/uniformizer formula before transporting signs. These classical locators
do not replace the native constructions above or enter Lean as axioms.
