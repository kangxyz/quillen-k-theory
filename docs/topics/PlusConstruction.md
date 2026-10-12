# Ring plus construction and comparison with Q

For an arbitrary unital ring `R : Type u`, the library constructs the projective
group-completion space independently of the Q-construction. Its zero component
satisfies the explicit homological plus specification for the original
stable-BGL map and every target local system in coefficient universe `u + 1`.
A specified map from that component to the identity component of original Q
loops is a weak homotopy equivalence. Positive K-group comparison maps are
natural under ring change, with their displayed basepoint-path corrections.

The genuine path components of projective completion and its original
projective telescope identify with original Quillen K₀. The matrix-image
change-of-rings functor also has the scalar-extension Hom universal property
against arbitrary ambient target modules. Noncommutative rings and the zero
ring are included throughout; no regularity, noetherian, flatness, or invariant
basis number assumption is added to these ring-specific statements.

The [documentation map](../README.md) supplies the neighboring topics;
[ExactCategories.md](ExactCategories.md) records the original Q/K interface,
and [SpectraAndBass.md](SpectraAndBass.md) records the separate spectral theory.

## Public imports

Use `import Quillen.KTheory.Plus` for the selected ring plus interfaces. For a
smaller interface, choose an individual module:

| Import after `Quillen.` | Public interface |
| --- | --- |
| `KTheory.Plus.StableGeneralLinearPlus` | `StableCompletion.stableZeroMap_isPlusConstruction` |
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

## Remaining comparisons

The statements above keep the following mathematical boundaries explicit:

- General CW existence, characterization, uniqueness, and a universal mapping
  property of plus constructions are not formalized.
- The Q-loop comparison is a weak homotopy equivalence; a homotopy-equivalence
  upgrade and a natural whole-space `K₀ × BGL⁺` splitting are not supplied.
- The homological certificate quantifies coefficient universe `u + 1`.
  Arbitrary further coefficient-universe transport is not inferred.
- No separate based homotopy between the chosen loop-map composites or strict
  pointedness is asserted by finite corrected-homotopy-group naturality.
- The scalar-extension Hom property does not construct a separate literal
  noncommutative balanced-tensor carrier or an isomorphism to that carrier.
  `rightBaseChangeTensorIso` concerns direct sum and is a different comparison.
- The independent universes in raw scalar extension do not enlarge the common
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
