# Ring plus construction and original Q comparison

## Imports

| Import | Interface |
| --- | --- |
| `Quillen.KTheory.Plus.StableZeroFiberHomology` | All-ring original stable-zero cover and homology setup: path-connected pullback with perfect pi1, actual integral quasi-isomorphism and original fiber-pi1 equivalence; homotopy-fiber perfectness remains separate |
| `Quillen.KTheory.Plus.StableFiberPerfectness` | Perfectness of the literal original stable-zero fiber over every ring, at its canonical constant-path point; theorem-valued specialization to the existing field-fiber alias |

## Ring plus and scalar extension

The selected public facade is `Quillen.KTheory.Plus`. Names below are relative
to `Quillen.FiniteProjectiveModule`.

| Import after `Quillen.` | Public names |
| --- | --- |
| `KTheory.Plus.StableGeneralLinearPlus` | `StableCompletion.stableZeroMap_isPlusConstruction` |
| `KTheory.Plus.ProjectiveCompletionZeroLoops` | `StableCompletion.zeroCompletionToOriginalQLoops_isWeakHomotopyEquivalence` |
| `KTheory.Plus.ProjectiveCompletionLoopHomotopyEquiv` | `completionToOriginalQLoopsHomotopyEquiv`, `originalQComparisonHomotopyEquiv`, `StableCompletion.zeroCompletionToOriginalQLoopsHomotopyEquiv` |
| `KTheory.Plus.ProjectiveCompletionLoopLabels` | Actual standard component and stage labels |
| `KTheory.Plus.ProjectiveCompletionLoopNaturality`, `KTheory.Plus.ProjectiveCompletionZeroLoopNaturality` | Actual ordinary naturality homotopies for the full and zero-component standard maps |
| `KTheory.Plus.ProjectiveOriginalPlusProduct` | `OriginalKZeroPlusProduct`, `originalPlusProductToQLoopsHomotopyEquiv`, `originalQLoopsPlusProductHomotopyEquiv` |
| `KTheory.Plus.ProjectiveOriginalPlusProductNaturality` | `originalPlusProductBaseChangeMap`, `originalPlusProductToQLoopsHomotopyEquiv_naturality` |
| `KTheory.Plus.ProjectiveCompletionPositiveKNaturality` | `StableCompletion.zeroCompletionPositiveKEquiv_baseChange` |
| `KTheory.Plus.ProjectiveCompletionZerothHomotopy` | `completionZerothHomotopyKZeroEquiv` and actual object-class naturality |
| `KTheory.Plus.ProjectiveTelescopeKZero` | `StableFreeRight.telescopeZerothHomotopyKZeroEquiv` and original stage classes |
| `Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeUniversal` | `rightBaseChangeUnit`, `rightBaseChangeHomEquiv`, `rightBaseChangeLift`, `rightBaseChange_existsUnique` |

The public standard comparison is one inner-loop reversal after the original
generic loop/fiber inverse. Its prescribed track reflects the inner loop
coordinate and retains the outer path direction. The actual comparison's
component label is `grade(input) - grade(basepoint)`; the zero-stage label is
`[P] - [rankOnePower n]`. Positive comparisons use the original loop-degree
shift and mapped-track transport, with no dimension-parity factor. See
[standard comparison normalization](StandardComparison.md).

The comparison homotopy equivalences retain those exact standard forward maps and the
original track. The product uses discrete original K₀ and the particular
`StableCompletion.ZeroComponent` certified by `stableZeroMap_isPlusConstruction`.
Its neutral slice, original classifier and standard labels are retained.
Ring change of the product-to-loop map is by ordinary homotopy with the
original K₀ and zero-completion maps. No natural chosen inverse, strictly
pointed naturality, H-space, A∞ or infinite-loop splitting is asserted.

The raw finite-free and idempotent-image scalar owners are
`Quillen.Aglib.LinearAlgebra.Matrix.RightScalarExtension` and
`Quillen.Aglib.Algebra.Category.ModuleCat.MatrixImageScalarExtension`. The literal
balanced tensor comparison, original unit/composition agreement, exactness
and all-degree K-map equality are proved in the focused tensor imports above.
Raw module and ring universes are independent; the original finite-projective
source remains `Category.{u, u}`, and mixed-ring-universe comparisons lift the
target explicitly. The original K-map and topological ring-change interfaces
retain their common-ring-universe bounds. The [homological comparison](#homological-plus-certificate-and-q-comparison)
records these scopes and the plus certificate's coefficient universe `u + 1`.
Automatic comparison and ordinary uniqueness on actual Hausdorff CW spaces for original
`IsPlusConstruction.{u,u,u}` certificates are now included. Common-universe
chain/certificate transport, CW subtype/ULift geometry and the mixed-universe
original-space assembly are also included. These results do not supply
arbitrary CW-homotopy-type transport or prescribed-track coherence.

## Ring plus construction

For every unital ring `R : Type u`, including noncommutative rings and the
zero ring, the independent zero component of projective completion satisfies
the explicit homological plus specification for every target local system in
coefficient universe `u + 1`. The exact standard map to the identity component
of original Q loops is a homotopy equivalence with its prescribed track. The
whole original Q-loop space is homotopy equivalent to discrete original K₀
times this specific plus model. Its product-to-loop map has ordinary homotopy
naturality under common-universe ring change; positive K-group comparisons
retain their basepoint corrections. No natural chosen inverse or infinite-loop
splitting is asserted. At stage `(n, P)` the standard class is `[P] - [R^n]`;
[standard normalization](StandardComparison.md) gives the actual sign formulas.

The matrix-image ring-change functor has the additive scalar-extension Hom
universal property for arbitrary ambient target modules, with independent
source-ring, target-ring and target-module universes. Literal noncommutative
balanced tensors identify with the original finite-projective scalar extension,
including its unit and composition coherence.

For original plus maps on actual Hausdorff CW subtypes, comparison homotopy
equivalences and ordinary uniqueness are constructed without finite-dimensional,
countable or locally finite restrictions. Mixed spaces retain a displayed
common coefficient universe. Actual CW structures are required; arbitrary
CW-homotopy-type transport, coherence relative to prescribed under-source
tracks and a natural chosen inverse remain separate. See
[the classical CW guide](../../Topology/PlusConstruction/ClassicalCW.md).

## Original covering and fiber homology

[`Covering.Pullback`](../../Topology/Covering/Pullback.lean) and
[`PullbackFiber`](../../Topology/Covering/PullbackFiber.lean) use the
same literal matching-pair subtype in independent space universes. A simply
connected total cover gives the original first-projection kernel equivalence
and the actual mapAt fiber-pi1 equivalence, retaining projection and connecting
equations. Path connectedness follows under the stated source path-connectedness
and raw-pi1-surjectivity hypotheses.

The original covering-fiber chain comparison uses this shared subtype.
[`PullbackCoveringHomologyUniverseLift`](../../Topology/LocalCoefficients/PullbackCoveringHomologyUniverseLift.lean)
extends it to source `Type u` and target/cover `Type (max u v)` by lifting only
the source. Its successor specialization retains the original mixed chain
map, integral coefficient object and second projection.

[`ProjectiveCompletionCover`](ProjectiveCompletionCover.lean)
constructs an actual surjective simply connected cover of the original
`ZeroComponent R` from the categorical component-cover theorem.
[`StableZeroFiberHomology`](StableZeroFiberHomology.lean)
then supplies, for every ring, a path-connected literal pullback with perfect
pi1, the original integral-chain quasi-isomorphism and the actual equivalence
to the original stable-fiber pi1.

[`H2CapDescent`](../../Topology/LocalCoefficients/H2CapDescent.lean)
constructs the marked finite-cycle/commutator argument for injective maps.
[`H2Perfectness`](../../Topology/HomotopyFiber/H2Perfectness.lean)
then uses the original LES and genuine mapping-cylinder transport: a
path-connected space with perfect pi1 mapping to a simply connected target
has perfect actual fiber pi1 when its original integral H2 map is surjective.
The theorem assumes neither CW structure nor simply connected source.
[`StableFiberPerfectness`](StableFiberPerfectness.lean)
applies it to the constructed covering data and transfers the result by the
original fiber-pi1 bijection. The literal original stable-zero fiber is
therefore perfect over every ring, at its canonical constant-path basepoint.

## Ring plus construction and comparison with Q

For an arbitrary unital ring `R : Type u`, the library constructs the projective
group-completion space independently of the Q-construction. Its zero component
satisfies the explicit homological plus specification for the original
stable-BGL map and every target local system in coefficient universe `u + 1`.
The exact standard map from that component to the identity component of
original Q loops is a homotopy equivalence, retaining its original forward map
and prescribed basepoint track. The whole original Q-loop space is homotopy
equivalent to discrete original K₀ times this specific plus-certified model.
Positive K-group comparisons retain their basepoint-path corrections; the
product-to-loop map has ordinary homotopy naturality under ring change.

The genuine path components of projective completion and its original
projective telescope identify with original Quillen K₀. The matrix-image
change-of-rings functor also has the scalar-extension Hom universal property
against arbitrary ambient target modules. Noncommutative rings and the zero
ring are included throughout; no regularity, noetherian, flatness, or invariant
basis number assumption is added to these ring-specific statements.

The [documentation map](../../../docs/README.md) supplies the neighboring topics;
[exact-category guide](../README.md) records the original Q/K interface,
and [spectral and Bass guide](../Bass/README.md) records the separate spectral theory.
[classical CW guide](../../Topology/PlusConstruction/ClassicalCW.md) describes comparison and ordinary
uniqueness for original plus maps on actual Hausdorff CW subtypes, including
the mixed-universe theorem and its coefficient bound.

## Public imports

Use `import Quillen.KTheory.Plus` for the selected ring plus interfaces. For a
smaller interface, choose an individual module:

| Import after `Quillen.` | Public interface |
| --- | --- |
| `KTheory.Plus.ProjectiveCompletionLoopHomotopyEquiv` | `originalQComparisonHomotopyEquiv` and `StableCompletion.zeroCompletionToOriginalQLoopsHomotopyEquiv` |
| `KTheory.Plus.ProjectiveOriginalPlusProduct` | `OriginalKZeroPlusProduct`, `originalPlusProductToQLoopsHomotopyEquiv`, and `originalQLoopsPlusProductHomotopyEquiv` |
| `KTheory.Plus.ProjectiveOriginalPlusProductNaturality` | `originalPlusProductToQLoopsHomotopyEquiv_naturality` |
| `KTheory.Plus.ProjectiveCompletionLoopLabels` | Actual standard stage and component labels |
| `KTheory.Plus.ProjectiveCompletionZerothHomotopy` | `completionZerothHomotopyKZeroEquiv` and its object-class and naturality formulas |
| `KTheory.Plus.ProjectiveTelescopeKZero` | `StableFreeRight.telescopeZerothHomotopyKZeroEquiv` and its stage formula |
| `Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeUniversal` | `rightBaseChangeUnit`, `rightBaseChangeHomEquiv`, `rightBaseChangeLift`, and `rightBaseChange_existsUnique` |

The declaration names in this table are relative to
`Quillen.FiniteProjectiveModule`. Module paths record mathematical ownership;
declaration namespaces describe the actual constructions.

## Objects and degree convention

Right `R`-modules are represented as left modules over `Rᵐᵒᵖ`.
The direct-sum core groupoid of finite projectives has an action-localization
category `S⁻¹S`, named `StableCompletion.Completion R`. Its realization is
`ClassifyingSpace (StableCompletion.Completion R)`, and its zero path component
is `StableCompletion.ZeroComponent R`.
`StableCompletion.stableZeroMap R` is the constructed stable-BGL map into this
component, with the specified `StableCompletion.basepointPath R`.

The library's exact-category `KSpace` is `BQ`, and `K n` is `π_(n+1)(BQ)`.
Consequently, `zeroCompletionPositiveKEquiv R n` identifies
`π_(n+1)(ZeroComponent R)` with original `K_(n+1)`, using the component inclusion,
the Q-loop comparison, path transport, and the loop-degree shift. Its index
`n = 0` gives K₁. The K₀ result instead classifies actual path components.

At a completion object, the virtual class is the numerator class minus the
denominator class. At an original projective-telescope vertex `(n, P)`, the
class is `[P] - [rankOnePower n]`. These formulas use finite projective
complements, without assuming every projective is stably free or classifying
free objects by a numerical rank.

## Homological plus certificate and Q comparison

`Quillen.Topology.PlusConstruction.Basic` defines `IsPlusConstruction` by an
explicit specification: source and target are path-connected, the specified
fundamental-group map is surjective with the given perfect kernel, and the
original local-coefficient chain map is a quasi-isomorphism for every target
system in the stated coefficient universe.

`stableZeroMap_isPlusConstruction` proves those fields for the actual stable
elementary subgroup, original map, and original basepoint path. The chain-map
statement retains the explicit universe lift and every homology degree. The
ring-specific proof uses stable elementary algebra, action localization,
twisted singular chains, filtered homology comparisons, and restriction to the
actual zero component. The plus certificate does not use the later Q-loop
comparison or K₀ classification as a premise.

`zeroCompletionToOriginalQLoops` is a specified map to the identity component
of loops on the Q-construction of finite projective right modules.
`zeroCompletionToOriginalQLoops_isWeakHomotopyEquivalence` covers every
homotopy degree, including degree zero. The displayed basepoint track comes
from the constructed comparison; strict preservation of the basepoint is not
required or asserted.

## Exact original comparison homotopy equivalence

[`ProjectiveCompletionLoopHomotopyEquiv`](ProjectiveCompletionLoopHomotopyEquiv.lean)
upgrades the exact standard comparison using the actual constructed
realization domination of original compact-open Q loops. The source is the
original completion realization; no domination or inverse is an additional
hypothesis. `completionToOriginalQLoopsHomotopyEquiv R U` retains the full
comparison at every displayed basepoint `U`, and
`originalQComparisonHomotopyEquiv` specializes to the additive zero pair.
Their forward maps are definitionally the original standard maps.

`StableCompletion.zeroCompletionToOriginalQLoopsHomotopyEquiv` restricts this
equivalence to the actual source and target zero components. Its forward map
is proved equal to `zeroCompletionToOriginalQLoops`; the accompanying
`zeroCompletionHomotopyEquivBasepointPath_val` preserves every point of the
prescribed standard track. The inverse homotopies are ordinary homotopies.
Neither a strictly pointed inverse nor naturality of a chosen inverse follows
from this construction. The [exact-comparison client](../../../examples/downstream/Consumer/OriginalQLoopHomotopyEquiv.lean)
checks these literal maps and tracks.

## Original K₀ times the original plus model

[`ProjectiveOriginalPlusProduct`](ProjectiveOriginalPlusProduct.lean)
defines `OriginalKZeroPlusProduct R` as the discrete original K₀ of finite
projective right modules times `StableCompletion.ZeroComponent R`.
`originalPlusProductToQLoopsHomotopyEquiv` gives the actual product-to-original-
Q-loop equivalence; `originalQLoopsPlusProductHomotopyEquiv` is its reverse.
The second factor is precisely the independent model certified above by
`stableZeroMap_isPlusConstruction`, not an arbitrary plus model.

The product's neutral slice is exactly the standard zero-component comparison,
and its basepoint track is the unchanged standard track. The reverse map's
first coordinate is the original continuous K₀ classifier. Its value on the
standard comparison is the algebraic completion grade, including the actual
stage formula `[P] - [rankOnePower n]`. Off the neutral slice the forward map
is literal right concatenation of the zero-component loop with the selected
K₀ representative; that order is retained.

`originalPlusProductToQLoopsHomotopyEquiv_naturality` proves ordinary homotopy
naturality of this forward map for common-universe ring maps. On the factors,
`originalPlusProductBaseChangeMap` uses the original K₀ map and original
zero-completion ring-change map. This supplies no natural chosen inverse,
strict representative section, H-space, A∞, or infinite-loop splitting.
The [original-product client](../../../examples/downstream/Consumer/OriginalPlusProduct.lean)
uses the actual plus factor, normalized neutral slice, labels and naturality.

## Ring-change naturality

`zeroCompletionPositiveKEquiv_baseChange` retains the actual
`zeroCompletionBaseChangeMap`, its displayed basepoint path, and
`rightBaseChangeExact.KMap`. Source and target rings share the stated common
universe. Identity and composition for the corrected positive maps follow from
the original K-map laws and the comparison's injectivity.

`completionZerothHomotopyKZeroEquiv_baseChange` uses the quotient map induced
by the original continuous completion map and the original KMap₀. The telescope
component equivalence retains the original finite-stage vertices and virtual
classes. The all-points homotopy for the completion-to-Q-fiber square and the
finite corrected homotopy-group naturality statements retain their own tracks.

The independent downstream client
[`Consumer.RingPlusNaturality`](../../../examples/downstream/Consumer/RingPlusNaturality.lean)
uses the public interface for the exact positive square, corrected identity and
composition, virtual object classes, a noncommutative matrix ring, and a map
from the integers to the zero ring.

The modules `ProjectiveCompletionLoopNaturality` and
`ProjectiveCompletionZeroLoopNaturality` construct actual continuous homotopies
between the standard comparison/ring-change composites, first in the full
original Q-loop space and then in its actual constant-loop component. The
component homotopy has exactly the ambient values. The proof cancels genuine
loop/fiber homotopy equivalences and retains the original fiber paths; the
standard homotopy reflects the inner coordinate of each resulting loop. Equality on homotopy
groups is not used to infer homotopy of maps.

These are ordinary homotopies of maps into a loop space. No loop-unit-fixed
homotopy or identification of the unit-evaluation track with the separately
prescribed correction paths is asserted. The standard correction paths reflect
the inner coordinate of the specified generic-inverse tracks. The independent client
[`Consumer.ProjectiveCompletionLoopNaturality`](../../../examples/downstream/Consumer/ProjectiveCompletionLoopNaturality.lean)
constructs paths at arbitrary points and checks the exact component restriction.

## Remaining comparisons

The statements above keep the following mathematical boundaries explicit:

- The ring certificate quantifies coefficient universe `u + 1`. Explicit
  common-universe transport is proved, but does not enlarge a certificate
  that quantified only smaller coefficients. The included mixed-universe
  automatic CW theorem retains actual Hausdorff CW inputs and the explicit
  common coefficient bound; the ring certificate alone does not supply CW
  structures on arbitrary models.

- Actual-CW ordinary uniqueness is included. Arbitrary CW-homotopy-type
  transport and coherence relative to prescribed under-source tracks are
  not supplied by that theorem.

- Path-class endpoint/universality and actual-CW simply connected cover
  constructions are included. Supplied-cover interfaces retain their
  explicit simply connected covers and commuting lift; the chosen-cover
  branch constructs lifts but retains its covers, cover points and pushout
  hypotheses. The automatic actual-CW branch supplies these data internally.

- Ambient, zero-component and product forward-map naturality use ordinary
  homotopies. Strict pointedness, identification of naturality unit tracks
  with separately prescribed correction paths, and natural chosen inverses
  are not asserted. No H-space, A∞ or infinite-loop splitting is supplied.

- Raw tensor and general-module universes are independent, while the original
  finite-projective source interface and original K-map retain their stated
  size bounds. A categorical ULift pseudofunctor packaging is not asserted by
  the literal-carrier coherence equations.

- Independent universes in raw scalar extension do not enlarge the common
  ring universe of the topological naturality theorem.

## Mathematical background

The mathematical background includes Grayson's
[*Higher algebraic K-theory II*](https://www.graysonfamily.org/dan/Papers/HigherAlgKThyII.pdf),
Weibel's [*K-book*, chapter III](https://www.math.rutgers.edu/~weibel/Kbook/Kbook.III.pdf),
and Miller–Palmer's
[*A twisted homology fibration criterion and the twisted group completion theorem*](https://mdp.ac/papers/twisted-group-completion-theorem/1409.4389v1.pdf).
These references provide background; the public statements and hypotheses are
the Lean declarations identified above.

Validation policy is in [CONTRIBUTING](../../../CONTRIBUTING.md#tests-and-checks)
and the [global trust boundary](../../../docs/ARCHITECTURE.md#trust-checks).
