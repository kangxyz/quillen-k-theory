# Mathematical scope

The library develops algebraic K-theory through exact-category Q-constructions,
Waldhausen S-constructions, geometric models, and explicit comparisons. The Q/S
models are connective. Bass negative groups are separate functorial cokernel
recursions; finite spectral stages and a geometric telescope are also constructed.
Lean declarations specify the actual objects, maps, hypotheses, and parameter
ranges. This guide records their principal interfaces and remaining boundaries.

## Available families

| Family | Current scope |
| --- | --- |
| Exact categories and Q-construction | Exact structures, restricted spans, composition, exact functors, and canonical K-maps |
| Classical K₀ | Exact and Waldhausen object presentations, original object classes, inverse identities, and all-class exact-functor naturality |
| Ring plus comparison | Independent homological stable-BGL model, original zero-component Q-loop weak equivalence, corrected positive K-map naturality, and completion/telescope K₀ components |
| Finite-projective scalar extension | Matrix-image change of rings with a natural semilinear unit and the additive Hom universal property against arbitrary target modules |
| Dévissage and resolution | Abelian finite-filtration dévissage and admissible finite-resolution comparisons |
| Serre and G-localization | Specified Serre quotients, finite-module G-theory, and connective tails |
| Scheme K/G-theory | Vector bundles, finite-type/coherent sheaves, restriction, K→G, and noetherian open/closed localization |
| Regular K→G | Regular affines; quasi-compact regular schemes with the resolution property |
| Perfect complexes | Strict/local models, derived local perfectness, change of cofibrations, support, and bounded-flat representatives |
| Model comparisons and pullback | Vector-bundle/strict equivalence on every scheme; affine strict/local equivalence; perfect pullback between quasi-compact schemes; explicit Gillet–Waldhausen term hypotheses |
| Connective localization | Quasi-compact opens of qcqs schemes, positive equivalence, exact K₀ image, boundary, and connective tails |
| Auxiliary support, excision, and Mayer–Vietoris | Natural supported localization; open-cover support excision; connective two-open sequence and matching K₀-class gluing |
| Finite pushforward | Coherent G and finite-flat vector-bundle/strict-perfect K direct images on locally noetherian schemes, with canonical comparison laws |
| Derived sheaf operations | Bounded-below direct image, flasque/affine units, composition, projection formula, and canonical ordinary/derived base-change mates |
| Projective-line geometry | Actual two-chart line, tautological line and quotient, cohomology/direct image, twisted diagonal triangles, and QC-single flat base change |
| Spectra and stable localization | Iterated S Ω-spectrum, additive K-comparison, signed looping, stable fiber sequence, coherent-homotopy quotient, and categorical stable localization |
| Finite homotopy excision | All-point connectivity, finite cube HELP, original double-cylinder gap bound, and S-model/finite Bass-stage stable cone sequences |
| Telescopes and Ω replacement | T1 finite-stage representatives and stable colimits, strict cone/pushout interchange, track-defined maps, and loop-tail Ω replacement |
| Bass groups and finite stages | Affine/scheme/supported cokernel recursions, strict Laurent seed and iterates, raw one-step comparisons, and natural finite-stage bottom-group isomorphisms |
| Ambient and supported Bass telescopes | Actual towers, natural negative-class maps, signed coefficient cone sequences, stable Bass self-maps, and the support-forgetting square |

[Library.md](Library.md) gives import paths, migration instructions, and qualified
interfaces. [ThomasonTrobaugh.md](ThomasonTrobaugh.md) gives the geometric route.
Generic finite-type sheaf categories are defined over arbitrary rings and schemes;
their abelian, Serre, exact-category, and G-theory theorems retain their stated
noetherian or locally noetherian hypotheses.

## Degree zero and geometric models

The exact-category object-generated Grothendieck group modulo conflation
relations is naturally isomorphic to original Quillen K₀, with independent object
and morphism universes. The original completed-loop map to the fundamental group
of the realized nerve is bijective; continuous-path generation is proved within
the stated topology and realization dependencies.

For small Waldhausen categories with matching object and morphism universes,
the original based object-loop map from the weak-arrow/cofibration-pushout
presentation is a bundled natural isomorphism to fine S-construction K₀. Its
inverse is the original realized grading. With independent universes, actual
small-model quotient and realization transport gives an equivalence retaining
original object classes and canonical exact-functor K-maps; its inverse is the
transported grading. Naturality covers every exact functor. No cylinder,
factorization, or presentation premise is added. The literal perfect-complex
specialization retains `PerfectK X 0` and original restriction for open immersions;
the triangulated-derived Grothendieck presentation remains a separate comparison.

Vector-bundle K and strict-perfect K have pullback for every scheme map, and
their comparison holds on every scheme. Strict/local equivalence holds on
affines. Perfect K and localized perfect spectra have arbitrary pullback between
quasi-compact schemes. Coherent G pullback requires flat maps of locally
noetherian schemes. Regular affine K→G has no finite Krull-dimension restriction;
the nonaffine comparison retains quasi-compactness and the resolution property.

Finite coherent direct image is exact for actual finite maps on locally
noetherian schemes. Finite-flat vector-bundle and strict-perfect direct images
use the same sheaf maps and retain K→G and vector-bundle/strict compatibility.
Target noetherianity is used to make finite flat affine modules projective.
The installed D+ direct image agrees with strict finite-flat direct image under
those hypotheses. Intrinsic D+ perfect preservation is proved for affine source
and finite flat map to a locally noetherian target.

## Localization, excision, and degree zero

For an open immersion `j : U ⟶ X`, `PerfectOpenK j n` uses perfect objects on
`X` with weak equivalences detected on `U`. The relative sequence retains the
actual support-forgetting map and homotopy-fiber boundary. Its surjective K₀
map lands in this relative group.

For quasi-compact quasi-separated (qcqs) `X` and quasi-compact `U`, relative
restriction is an equivalence in positive degrees. At zero it is injective with
image exactly `(perfectKRestrict j 0).range`. The tail

```text
K₁(X) → K₁(U) → K₀(X on X ∖ U) → K₀(X) → K₀(U)
```

is exact at its three interior positions; surjectivity onto final `K₀(U)` is
not asserted. Principal affine opens are included over every commutative ring,
including localization at zero.

Ordinary localization is natural for arbitrary commuting qcqs open-pair squares
with quasi-compact opens. With auxiliary acyclicity open `T`, relative boundary
naturality requires only quasi-compact ambient bases; relative restriction also
requires quasi-compact localization opens. The actual absolute boundary and
positive inverse are natural for arbitrary commuting support/localization
squares with qcqs bases and both opens quasi-compact. Flatness and cartesianness
are not required. Support inclusions and forgetting support are included.

The supported relative bounded-flat comparison includes K₀ with only
quasi-compact ambient `X`, arbitrary opens, and no quasi-separatedness. Support
excision includes every nonnegative degree when the localization image and
auxiliary open cover `X`, with actual extension-by-zero inverse and no
compactness/separation hypothesis. A quasi-compact two-open cover of qcqs `X`
has the connective Mayer–Vietoris sequence and matching local K₀-class gluing.
Its overlap map is first restriction multiplied by the inverse of the second.
The supported version retains a quasi-compact auxiliary open. Neither overlap
K₀ surjectivity nor a negative boundary follows from these connective results.

## Derived sheaves and the two-chart projective line

Quasicoherent sheaves are acyclic for affine direct image, without finite,
flat, or noetherian hypotheses. Flasque sheaves are acyclic for every scheme
map; arbitrary direct image preserves quasi-isomorphisms of bounded-below
flasque complexes, with invertible installed D+ unit and no upper bound.
The canonical bounded-below derived composition and projection formula retain
the original ordinary arrows and unit equations. The projection formula uses
finite locally free coefficients. Tensor restriction and local tensor exactness
use actual sheafification and affine finite-free retractions.

Ordinary affine quasicoherent base change is invertible on genuine cartesian
squares of spectra without flatness or finite-generation assumptions. The
canonical derived flat mate has natural unit, shift, horizontal/vertical pasting,
and open-cover equations. It is invertible on every bounded-below complex for
open base change, and on quasicoherent singles and their shifts for affine
morphisms with flat base change. General bounded-below flat-base-change
invertibility is not inferred from those single-sheaf results.

The actual two-chart projective line over any commutative ring is qcqs, with flat
separated projection and original Laurent gluing. Its global sections are `R`.
Quasicoherent cohomology vanishes above degree one. The structure module and
tautological quotient have no positive cohomology; the negative tautological
line has zero cohomology in every degree. The quotient sections are `R × R`
through its original projection. For the relative projection, the structure
module has canonical direct image the base structure module and no positive
derived images; the negative line has zero derived image in every degree.
Affine-base vector-bundle and bounded-complex comparisons retain the original
geometric unit and installed D+ unit.

The original twisted diagonal sequence `p₁*L → p₂*Q → Δ_*Q` is short exact
with its actual cokernel, signed chart scalars, and closed diagonal. Its tensor
and derived/projected triangles retain incidence, quotient, and connecting arrows;
the projected third vertex is the single of `E ⊗ Q`. The relative signed Čech
triangle and the canonical flat-base-change isomorphism for the original
projection concern quasicoherent singles, including zero and nonreduced bases.
They do not supply coefficient perfection or projective-bundle generation.

## Spectra and Bass groups

The original iterated S Ω-spectrum has additive `originalKStableEquiv` in every
nonnegative degree, including K₀, and zero negative stable groups. Arbitrary
exact functors retain original K-maps without a chosen-zero equality premise;
normalized raw maps have whole homotopy laws, and localized maps have literal
identity/composition laws. Parameter looping transposes loop/structure coordinates
and has the signed all-integer stable shift. Actual path-space fibers have an
all-integer stable long exact sequence. Whole coherent squares give fiber maps
and boundary naturality; connectivity for connective inputs uses K₀ surjectivity.

The original double-cylinder gap has connectivity `r` for `p`- and `q`-connected
attaching maps when `r + 1 ≤ p + q`, including actual fiber nonemptiness and all
fiber points. For `f : E ⟶ F`, the canonical cone-fiber comparison is
`E ⟶ homotopyFiber (mappingConeInclusion f)`, using the original cone cylinder.
S-level growth and point HEP discharge stable cone-fiber excision
for original S-model maps and actual finite Bass-stage arrows. Their signed cone
sequences retain the original comparison and boundary. Exact filtered colimits
also discharge the cone sequence for actual Bass telescope coefficient maps.
General stable cofiber excision on arbitrary prespectra remains separate.

T1 reduced telescopes have common finite-stage representatives, eventual equality,
and canonical homotopy/stable colimit comparisons in all signed degrees.
Track-defined maps retain supplied whole cylinders; generic exactness still
requires stagewise exactness. Strict cone/pushout interchange needs neither T1
nor point HEP. The original loop-tail telescope is an Ω replacement under
levelwise T1, with all-component weak structure maps, a natural stable unit,
and an actual fiber comparison. Stable maps between genuine Ω-prespectra are
exactly complete weak maps at every level, without connectedness or T1.
This does not imply cofiber preservation of the replacement.

Bass groups use actual affine, scheme, and supported cokernel recursions with
homotopical perfect K₀ seeds. Index `i` means degree `-i`. Scheme pullback uses
quasi-compact schemes; supported recursion needs a quasi-compact ambient base
and arbitrary vanishing open. The affine and scheme recursions agree naturally,
with literal K₀ at zero. The contraction preserves pointwise right exactness and
cokernels at every stage.

The original Laurent unit and null tracks construct the raw Bass step, its
coefficient maps, and bounded-flat/perfect single-step and seed comparisons.
Cocartesian sections give a genuine strict diagram and an unconditional natural
Laurent seed `F → B(F)`, with all transitions `B^i(seed)`. Evaluation compares
the strict and raw one-step maps at every level, including zero; the original
bounded-flat/perfect step comparison is completely weak at positive levels and
stable in every integer degree. Full all-iterate geometric comparison remains
a separate obligation.

For every finite stage `i`, the already-defined `negativeKFunctor i` is naturally
isomorphic to its stable group at degree `-i`, retaining the original Laurent
quotient and second-chart sign. That stage has zero stable groups below `-i`.
Composing with its original telescope inclusion gives a natural negative-class
map, with no injectivity, surjectivity, or stabilization assertion. The actual
ambient telescope maps stably to its own Bass image in every integer degree;
this preserves the original seed and initial inclusion without assuming finite
seed transitions stable. The localized perfect spectrum also has a natural
initial map to this telescope, without a nonnegative-group isomorphism claim.

For every open immersion into `Spec R`, the fixed-open `Under R` section diagram,
supported Laurent seed, finite tower, and telescope are constructed. T1 and seed
compatibility premises are concretely discharged. The supported telescope has
the same all-integer stable Bass self-map, and its whole support-forgetting
square with the ambient self-map commutes. At the identity algebra it retains
the actual pulled-back open, related to the original by its projection isomorphism.
The geometric acyclic-support cone compares stably to the coarse relative-open
model, and relative-open section evaluation is an all-level homotopy equivalence.
The supported-section null cylinder and scalar categorical-cofiber class
transport do not identify that endpoint with all perfect complexes of the open
or prove the Laurent-unit boundary formula.

## Ring plus-construction work

For every unital ring `R : Type u`, the independently constructed zero component
of projective completion satisfies the homological plus specification for the
original stable-BGL map and every target local system in coefficient universe
`u + 1`. Its specified map to the identity component of original Q loops of
finite projective right modules is a weak homotopy equivalence. The original
positive K-group comparison is natural under actual ring-change maps in a
common universe, retaining the specified basepoint paths and original KMap.
Noncommutative and zero rings are included without additional hypotheses.

The genuine path components of projective completion and the original
projective telescope identify with the original Quillen K₀. The actual object
and stage formulas retain numerator-minus-denominator classes; completion
component naturality uses the original continuous map and KMap₀. This proves
the original telescope component obligation, not a natural whole-space splitting.
The independent homological plus proof does not use the later Q comparison
or K₀ classification.

The constructed matrix-image ring-change functor satisfies the
scalar-extension Hom universal property against arbitrary ambient target
modules, with a natural semilinear unit and unique target-linear lifts. The
raw algebra permits independent ring and target-module universes without
commutativity or flatness hypotheses. A separate literal noncommutative
balanced-tensor carrier and comparison to that carrier remain unconstructed.
General CW characterization/uniqueness, an HE upgrade, and a natural
`K₀ × BGL⁺` splitting are not asserted. Loop-map naturality is proved on finite
homotopy groups with the stated corrections, without a separately packaged
based homotopy between the chosen loop-map composites.
[PlusConstruction.md](PlusConstruction.md) records the exact interfaces,
coefficient universes, and remaining boundaries.

## Remaining comparisons

- Fixed-degree finite Bass-transition stabilization, bijectivity of the natural negative-class maps into the telescope, and classical telescope negative-group identification.
- Full all-iterate comparison with the original geometric Bass tower, the fundamental theorem, and Laurent-unit boundary/relative-loop basepoint calculations, including the zero-section class and possible Nil terms.
- Supported-section cone stability, its geometric localization comparison, full nonconnective Thomason–Trobaugh localization, negative boundaries, and nonconnective descent, retaining the K₀ image obstruction.
- Proj identification, the full twisting-sheaf family, coefficient perfection, projective generation, and the projective-bundle formula. The finite-coefficient retract criterion remains conditional on its projectivity/splitting and uniform finite-window assumptions.
- General-source perfect preservation by derived direct image, unrestricted unbounded derived pushforward, and general bounded-below flat-base-change invertibility.
- Strict/local equivalence on arbitrary nonaffine schemes and perfect pullback on arbitrary non-quasi-compact schemes.
- General stable cofiber excision, the remaining quotient homotopy-invariance questions, and a standard stable model structure or triangulation for the categorical localization.
- The triangulated-derived Grothendieck presentation of perfect objects, general exact-category dévissage/localization, and full Serre-pair coherence.
- Cross-universe transport beyond the explicit small-model and common-ring-universe plus-comparison interfaces, literal noncommutative tensor-product scalar-extension identification, and higher raw-spectrum/telescope coherence.

Regularity alone does not give the resolution property. Finite cube HELP does
not imply arbitrary compact HELP, and endpoint collar deformation alone does
not supply vertical lifting. Keep the stated hypotheses when composing interfaces.

## Verification

Verification uses Lean `v4.34.1` with mathlib pinned to
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The complete pipeline covers import
generation, layout and placeholder checks, script tests, library/tests,
Batteries environment lint, native mathlib text lint, downstream clients, and
explicit audit replay including private project declarations. The organized
`v0.4.1` source passes this complete local pipeline: 2,331 production modules,
444 maintained test modules, and 51 script tests. Native text-style checks cover
2,806 sources. The library audit covers 36,423 project declarations, including
private helpers; the downstream audit covers 182 declarations. Checks are
incremental and retain unchanged build outputs. Allowed foundation axioms are
`propext`, `Classical.choice`, and `Quot.sound`.

The complete entry is `bash scripts/check.sh --rehash`. A scoped matched
typechecking measurement is in [Performance.md](Performance.md). See
[Architecture.md](Architecture.md#trust-checks) for declaration coverage and
[CONTRIBUTING.md](../CONTRIBUTING.md#typechecking-performance) for profiling.
Successful checks concern encoded statements and audited foundation dependencies
in the checked environment. Mathematical interpretation and applicability need
their own assessment; passing checks supplies no absent comparison theorem.
