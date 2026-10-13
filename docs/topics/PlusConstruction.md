# Ring plus construction and comparison with Q

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

The [documentation map](../README.md) supplies the neighboring topics;
[ExactCategories.md](ExactCategories.md) records the original Q/K interface,
and [SpectraAndBass.md](SpectraAndBass.md) records the separate spectral theory.
[ClassicalCWPlus.md](ClassicalCWPlus.md) describes comparison and ordinary
uniqueness for original plus maps on actual Hausdorff CW subtypes, including
the mixed-universe theorem and its coefficient bound.

## Public imports

Use `import Quillen.KTheory.Plus` for the selected ring plus interfaces. For a
smaller interface, choose an individual module:

| Import after `Quillen.` | Public interface |
| --- | --- |
| `KTheory.Plus.StableGeneralLinearPlus` | `StableCompletion.stableZeroMap_isPlusConstruction` |
| `KTheory.Plus.ProjectiveCompletionLoopHomotopyEquiv` | `originalQComparisonHomotopyEquiv` and `StableCompletion.zeroCompletionToOriginalQLoopsHomotopyEquiv` |
| `KTheory.Plus.ProjectiveOriginalPlusProduct` | `OriginalKZeroPlusProduct`, `originalPlusProductToQLoopsHomotopyEquiv`, and `originalQLoopsPlusProductHomotopyEquiv` |
| `KTheory.Plus.ProjectiveOriginalPlusProductNaturality` | `originalPlusProductToQLoopsHomotopyEquiv_naturality` |
| `KTheory.Plus.ProjectiveCompletionLoopLabels` | Actual standard stage and component labels |
| `KTheory.Plus.ProjectiveCompletionZeroLoops` | `StableCompletion.zeroCompletionToOriginalQLoops_isWeakHomotopyEquivalence` |
| `KTheory.Plus.ProjectiveCompletionPositiveKNaturality` | `StableCompletion.zeroCompletionPositiveKEquiv_baseChange` |
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

## Standard comparison normalization

The public `completionToOriginalQLoops` and `originalQComparison` use exactly
one inner-loop reversal after the original generic loop/fiber inverse.
The Q-construction, positive object classes, `K n = π_(n+1)(BQ)`, K-maps,
algebraic completion grades and loop-degree shift retain their definitions.
Let `q_U` be the specified loop-valued basepoint track of that inverse at the
original fiber point. At outer track parameter `s` and inner loop parameter
`t`, the prescribed standard track is `q_U(s)(1 - t)`. The outer track
direction is retained.

At a displayed vertex `U`, the public component label is
`grade(input) - grade(U)`. At the additive zero pair and standard zero stage
it is exactly the algebraic grade; a nonzero-grade basepoint contributes its
displayed subtraction. In particular the stage `(n, P)` has Q-loop class
`[P] - [rankOnePower n]`. `ProjectiveCompletionLoopLabels` proves these actual
comparison formulas.

Positive comparisons use the original loop shift and mapped-track transport.
Reflection of one inner-loop coordinate induces inversion in the shifted
homotopy group, with no dimension-parity factor. Generic loop reversal reverses
concatenation order; inversion is packaged as a group map only in the already
commutative positive K targets. See
[standard comparison normalization](../reference/StandardSignMigration.md)
and the [public client](../../examples/downstream/Consumer/StandardSignMigration.lean).

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

### Exact original comparison homotopy equivalence

[`ProjectiveCompletionLoopHomotopyEquiv`](../../Quillen/KTheory/Plus/ProjectiveCompletionLoopHomotopyEquiv.lean)
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
from this construction. The [exact-comparison client](../../examples/downstream/Consumer/OriginalQLoopHomotopyEquiv.lean)
checks these literal maps and tracks.

### Original K₀ times the original plus model

[`ProjectiveOriginalPlusProduct`](../../Quillen/KTheory/Plus/ProjectiveOriginalPlusProduct.lean)
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
The [original-product client](../../examples/downstream/Consumer/OriginalPlusProduct.lean)
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
[`Consumer.RingPlusNaturality`](../../examples/downstream/Consumer/RingPlusNaturality.lean)
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
[`Consumer.ProjectiveCompletionLoopNaturality`](../../examples/downstream/Consumer/ProjectiveCompletionLoopNaturality.lean)
constructs paths at arbitrary points and checks the exact component restriction.

## Scalar extension by its universal property

For `f : R →+* S`, `rightBaseChangeHomEquiv f P N` is an additive equivalence
between `Sᵐᵒᵖ`-linear maps from the actual change-of-rings object and
`f.op`-semilinear maps from `P` into any ambient target module `N`. Its forward
map is literally precomposition by `rightBaseChangeUnit f P`.
`rightBaseChangeLift`, its unit equation and uniqueness theorem, and
`rightBaseChange_existsUnique` express the same universal extension. The unit
and Hom equivalence are natural in the projective source and the target module.

The construction passes from finite-free coordinate extension in
`Algebra.Matrix.RightScalarExtension`, through idempotent images in
`Algebra.Category.ModuleCat.MatrixImageScalarExtension`, to the actual
finite-projective presentation equivalence. Source-ring, target-ring, and
ambient target-module universes may be independent in this algebraic interface.
The target need not be finite or projective. This does not assert an adjunction
within finite-projective subcategories: restriction of scalars need not
preserve finite projectives.

[`Consumer.RingScalarExtension`](../../examples/downstream/Consumer/RingScalarExtension.lean)
checks the literal unit, Hom map, uniqueness and naturality, including
noncommutative and zero-ring examples.

## Literal balanced tensor and the original scalar extension

`Quillen.Algebra.Module.RightScalarExtension` defines `RightScalarExtension.Tensor`
as the literal quotient of `S ⊗[ℤ] M` by the balancing relations
`(f r * s) ⊗ m - s ⊗ (op r • m)`. It proves that the right-submodule relation
span equals the integer span, constructs pure tensors, and proves balanced
biadditive and right-module semilinear universal properties. Ring and module
carrier universes are independent; no commutativity or flatness is assumed.
[`Consumer.BalancedRightTensor`](../../examples/downstream/Consumer/BalancedRightTensor.lean)
checks the public universal-property interface.

`Quillen.Algebra.Category.ModuleCat.RightScalarExtension` gives the actual
additive tensor functor, source naturality, identity and composition linear
equivalences, and the triple-composition equality `compEquiv_assoc` on literal
carriers. The original scalar-extension universal property constructs
`rightTensorBaseChangeEquiv`, with actual inverse maps. Its source naturality
and its agreement with the pre-existing `rightBaseChangeId` and
`rightBaseChangeComp` retain the original units. Rectangular-matrix naturality
and the explicit idempotent-image comparison are also proved.

The finite-projective tensor functor is exact because it preserves the actual
splittings of inherited conflations. It requires neither flatness nor
commutativity. `rightTensorBaseChangeExact_KMap` identifies its original
zero-normalized K-map with the unchanged `rightBaseChangeExact.KMap` in every
degree, within the original common-ring-universe K-map interface.

Raw tensor carriers and the general module functor have independent universes.
The original finite-projective source interface remains `Category.{u, u}` for
`R : Type u`; the mixed-ring-universe natural isomorphism explicitly lifts the
original target by `ModuleCat.uliftFunctor`. It does not make all carriers
definitionally equal or enlarge that existing finite-projective source scope.
Triple coherence is a proved equality on literal tensor carriers; categorical
ULift bookkeeping is not separately packaged as a pseudofunctor-coherence
structure. The older `rightBaseChangeTensorIso` concerns direct sum and is a
different comparison.

[`Consumer.BalancedTensorBaseChange`](../../examples/downstream/Consumer/BalancedTensorBaseChange.lean)
checks the lifted naturality square, original composition and all-degree K-map
identification. [`Consumer.FiniteProjectiveBaseChangeUnitCoherence`](../../examples/downstream/Consumer/FiniteProjectiveBaseChangeUnitCoherence.lean)
checks the original identity/composition units.

## Regular local coefficient foundation

The actual integral regular system is the free module on path classes from a
chosen basepoint. Transport is postcomposition; inverse-path transport is
proved and basepoint monodromy is faithful without an abelian hypothesis.
`RegularGroupRing` identifies the fiber with the integral group ring on the
original first homotopy group. Under Mathlib's multiplication convention the
transport formula is left multiplication. `CoefficientLift` and
`RegularUniverseLift` put these coefficients in a displayed sufficient universe
and preserve path transport and faithful monodromy.
[`Consumer.RegularLocalCoefficients`](../../examples/downstream/Consumer/RegularLocalCoefficients.lean)
checks commutation detection, orientation and inverse lifted transport.

These regular systems support the simply-connected homological weak Whitehead
and supplied-cover twisted Whitehead theorems. Actual metric realization and
loop geometry also construct the domination used in the exact original-Q
comparison above. See the [foundations guide](HomotopyFoundations.md) for their
hypotheses, original maps and covering boundary.

## Whitehead for actual simplicial realizations

`Quillen.Topology.Realization.Whitehead` constructs
`Realization.homotopyEquivOfWeakHomotopyEquivalence` for the actual realizations
of `X Y : SSet.{u}`. Its forward continuous map is exactly the given weak
homotopy equivalence. A cube/simplex boundary-pair homeomorphism, realized
boundary lifting and skeletal monomorphism lifting construct a global inverse;
the actual simplicial cylinder supplies the second inverse homotopy. No chosen
inverse or target-bearing compact-HELP certificate is assumed.

The inverse homotopies are ordinary, unbased homotopies. The generic
supplied-domination upgrade retains its explicit domination data. For the
original Q-loop comparison, the metric/numerable construction now supplies
that data, so the exact map is genuinely upgraded as described above. This
does not by itself identify an arbitrary CW-type model or arbitrary plus model.
[`Consumer.RealizationWhitehead`](../../examples/downstream/Consumer/RealizationWhitehead.lean)
checks the unchanged forward map and actual inverse-homotopy consequences.

## Actual classical CW plus comparisons

`Quillen.IsPlusConstruction.classicalCWPlusUnique` proves the following: for actual Hausdorff CW
subtypes `A`, `B`, `C` in `Type u`, the original maps `f`, `g`, points `a`, `b`,
`c`, tracks `γ`, `δ`, subgroup `N`, and original `IsPlusConstruction.{u,u,u}`
certificates yield a homotopy equivalence `h : B ≃ₕ C` with `h ∘ f` homotopic
to `g`. Every continuous `k : B → C` with `k ∘ f` homotopic to `g` is ordinarily
homotopic to `h`. Covers, commuting lifts, the canonical double cylinder and
its pushout proof are constructed; no desired-equivalence certificate is
supplied. There is no finite-dimensional, countable or locally finite
restriction.

The [classical CW guide](ClassicalCWPlus.md) also records the now included
mixed-universe original-space theorem. `classicalCWPlusUnique_successor`
consumes the literal original `IsPlusConstruction.{u,u+1,u+1}` certificates;
the general `u`, `v`, `w` theorem requires both original certificates for all
target systems in `U = max u v w z`. The constructed CW subtype/ULift and
chain/certificate adapters return the equivalence and ordinary homotopies to
the original spaces. Actual Hausdorff CW hypotheses remain required; these
results do not supply arbitrary CW-homotopy-type transport or prescribed-track
coherent uniqueness.

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

## Related reading and verification

The mathematical background includes Grayson's
[*Higher algebraic K-theory II*](https://www.graysonfamily.org/dan/Papers/HigherAlgKThyII.pdf),
Weibel's [*K-book*, chapter III](https://www.math.rutgers.edu/~weibel/Kbook/Kbook.III.pdf),
and Miller–Palmer's
[*A twisted homology fibration criterion and the twisted group completion theorem*](https://mdp.ac/papers/twisted-group-completion-theorem/1409.4389v1.pdf).
These references provide background; the public statements and hypotheses are
the Lean declarations identified above.

Run `bash scripts/check.sh --rehash` for the integrated library and independent
client. It checks imports, source structure, placeholders, script tests,
compilation, environment and text lint, and both explicit transitive axiom
audits. The allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.
These checks concern encoded proofs and their foundation dependencies; they do
not by themselves certify correspondence with a classical source theorem.
