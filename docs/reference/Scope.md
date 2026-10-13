# Mathematical scope

This reference summarizes the encoded mathematical coverage and remaining
comparisons across the library. The [documentation map](../README.md) leads to
object-specific guides; the [API reference](API.md) locates their public imports
and maps. Exact statements, universes, and proof inputs remain in Lean source.

Definitions construct objects and maps. A comparison theorem with named
hypotheses proves its stated implication; applications must supply those
hypotheses or use an available construction that realizes them. A public
interface or a successful compilation does not supply an additional comparison.

## Available families


| Family | Current scope |
| --- | --- |
| Exact categories and Q-construction | Exact structures, restricted spans, composition, exact functors, and canonical K-maps |
| Waldhausen theory | S-construction, additivity, Q/S comparison, and approximation/cofinality/fibration with their stated input data |
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
| Laurent and Čech finite models | Finite-defect parametrices, projector/module homotopy models, actual sheaf Čech comparisons, and perfect derived projection images for vector-bundle singles and explicitly bounded vector-bundle complexes |
| Projective-line geometry | Actual two-chart line, tautological line and quotient, cohomology/direct image, twisted diagonal triangles, and QC-single flat base change |
| Spectra and stable localization | Iterated S Ω-spectrum, additive K-comparison, signed looping, stable fiber sequence, coherent-homotopy quotient, and categorical stable localization |
| Finite homotopy excision | All-point connectivity, finite cube HELP, original double-cylinder gap bound, and S-model/finite Bass-stage stable cone sequences |
| Telescopes and Ω replacement | T1 finite-stage representatives and stable colimits, strict cone/pushout interchange, track-defined maps, and loop-tail Ω replacement |
| Bass groups and finite stages | Affine/scheme/supported cokernel recursions, strict Laurent seed and iterates, raw one-step comparisons, and natural finite-stage bottom-group isomorphisms |
| Ambient and supported Bass telescopes | Actual towers, natural negative-class maps, signed coefficient cone sequences, stable Bass self-maps, and the support-forgetting square |
| Full-open coefficient models | Original restriction/null diagrams, signed finite cone comparisons, fine and graded Bass towers/telescopes, pointwise geometric evaluation and graded telescope vanishing |

The subject guides cover [exact categories](../topics/ExactCategories.md),
[Waldhausen theory](../topics/Waldhausen.md),
[dévissage, resolution, and localization](../topics/Localization.md),
[scheme K/G-theory](../topics/SchemeKTheory.md),
[perfect-complex localization](../topics/PerfectComplexes.md),
[spectra and Bass groups](../topics/SpectraAndBass.md), and
[ring plus construction](../topics/PlusConstruction.md).

## Degree zero and geometric models

For an exact structure, `K n` is `π_(n+1)(BQ)`. Its object-and-conflation
Grothendieck group identifies naturally with original K₀. The Waldhausen
weak-arrow/cofibration-pushout presentation also identifies with original K₀,
with explicit small-model transport for independent object and morphism
universes. These are the stated presentations, without an inferred
triangulated-derived presentation of perfect objects.

Vector-bundle/strict-perfect comparison and their pullbacks accept every scheme
map. Affine strict/local comparison includes every nonnegative degree.
Perfect pullback accepts arbitrary maps between quasi-compact schemes; coherent
G pullback requires flat maps between locally noetherian schemes. Regular
affine K→G has no finite Krull-dimension bound; the nonaffine comparison also
requires quasi-compactness and the resolution property.

Finite coherent direct image is exact for finite maps of locally noetherian
schemes. Finite-flat vector-bundle and strict-perfect direct images retain
their canonical comparison maps. The derived preservation theorem for perfect
objects retains its affine-source and finite-flat hypotheses.

Finite-filtration dévissage is abelian. The resolution theorem requires actual
objectwise finite admissible resolution towers and the stated resolving closure
conditions; no common length bound is needed. Generic Waldhausen approximation,
fibration, and dense cofinality retain their own cylinder, factorization,
closure, or lifting data rather than asserting them for every structure.

## Localization, excision, and degree zero

For every open immersion `j : U ⟶ X`, relative `PerfectOpenK j n` uses perfect
objects on `X` with weak equivalences detected on `U`. Its connective fiber
sequence includes a surjection onto relative K₀. Identifying that group with
the actual open endpoint is a separate comparison.

For qcqs `X` and quasi-compact `U`, relative restriction is an equivalence in
positive degrees. At zero it is injective with image exactly
`(perfectKRestrict j 0).range`. Thus

```text
K₁(X) → K₁(U) → K₀(X on X ∖ U) → K₀(X) → K₀(U)
```

is exact at its three interior positions. It supplies neither surjectivity
onto final K₀ nor a negative boundary. Principal affine opens include every
commutative ring and localization at zero.

Ordinary localization naturality retains commuting qcqs open-pair squares and
quasi-compact opens. Supported relative comparison includes K₀ with only
quasi-compact ambient base and arbitrary opens. Support excision uses an actual
open cover, without an inferred compactness or separation hypothesis.
A quasi-compact two-open cover of qcqs `X` gives connective Mayer–Vietoris and
matching K₀-class gluing, with overlap map first restriction times inverse
second restriction. It does not assert overlap-K₀ surjectivity.

## Derived sheaves and the two-chart projective line

Affine quasicoherent and arbitrary flasque acyclicity give the specified
bounded-below derived direct-image comparisons. Derived composition retains
its original ordinary arrows; the projection formula uses finite locally free
coefficients. Ordinary affine quasicoherent base change is invertible on
cartesian spectra squares without flatness or finite-generation hypotheses.

The derived flat mate has unit, shift, pasting, and open-cover equations.
Invertibility covers bounded-below open base change and affine quasicoherent
single-sheaf inputs and shifts under flat base change. General bounded-below
flat-base-change invertibility is a further obligation.

The actual two-chart line over every commutative ring has its Laurent gluing,
cohomology and relative direct-image calculations. The twisted diagonal exact
sequence and projected triangles retain their original arrows. New finite-defect
parametrices construct finite-projective Čech models from the actual chart
modules. Every finite locally free sheaf on the line has an intrinsically
perfect original derived projection image; the result extends to explicitly
bounded complexes with finite locally free terms. This construction uses the
split-kernel finite-parametrix argument and does not discharge the separate
support-window premises of the older finite-coefficient retract criterion.

Arbitrary locally-perfect representation and preservation, projective
generation, and the projective-bundle formula remain separate. The precise
sheaf and bounded-complex hypotheses are in
[scheme K/G-theory](../topics/SchemeKTheory.md).

## Spectra and Bass groups

The genuine iterated S-construction gives a connective Ω-spectrum and the
original additive K-comparison with its stated strict-zero or chosen-path
interfaces. Based prespectra have all-integer stable groups and signed shifts.
Path-space stable fibers have an all-integer long exact sequence; categorical
stable localization does not itself supply a model structure or triangulation.

Finite cube HELP and the original double-cylinder gap establish the stated
finite excision comparisons. S-model and actual finite Bass-stage maps have
the proved stable cone-fiber comparisons. Arbitrary compact HELP and general
stable cofiber excision are not inferred from these specializations.

T1 reduced telescopes have finite-stage representatives, eventual equality,
and homotopy/stable colimit comparisons. Track-defined maps retain their whole
cylinders. The loop-tail Ω replacement uses its levelwise T1 hypothesis; its
fiber comparison does not imply cofiber preservation.

Bass index `i` denotes degree `-i`. Affine, scheme, and supported negative
groups are actual cokernel recursions with their original K₀ seeds. At finite
stage `i`, the original negative group identifies with the stable group in
degree `-i`, and lower stable groups vanish. The telescope inclusions give
natural negative-class maps without a proved bijectivity or stabilization
claim. The ambient and supported telescopes have their own stable Bass
self-comparisons; these do not identify them with the classical nonconnective
geometric theory. Fixed-open constructions retain their actual `Under R`
domains and support-forgetting squares.

For an open immersion `j : U ⟶ Spec R` with quasi-compact `U`, the actual
quotient-graded full-open section diagram has a coefficient-natural whole
Laurent self-track contraction and a natural nullhomotopy of its original
Bass seed. Every original graded Bass transition has zero stable map in every
integer degree; T1 finite-stage representatives then give zero stable groups
for its actual reduced graded telescope. The argument assumes neither
individual-stage vanishing nor an unconstructed seed null.

The fine-to-graded seed square is proved. The actual fine tower/telescope and
induced grading maps, original restriction coefficient transformation,
canonical whole localization null and signed initial/finite cone comparisons
are constructed. Pointwise fine section evaluation is stable to the explicitly
lifted bounded-flat prespectrum, and to the perfect prespectrum for compact U;
chosen-zero normalization and original K-equations remain explicit.
The original r seed square and canonical whole-null seed equations are now
constructed. The same compatible finite null family gives a stable telescope
cone descent; graded signed vanishing makes the original coarse-to-fine r∞
stable. The supported telescope cone and the original whole-null fiber compare
to this constructed fine completion, retaining the actual signed boundary.
The native global C/F/G Models now have actual cofinality, honest K₀ image
exactness, canonical nulls, original Laurent seeds and whole seed/null squares.
Their literal towers and graded contraction prove the original r∞ stable for
qcqs ambient schemes and quasi-compact opens. Actual auxiliary-supported
Models, supported quotient grading and unit/relative-track evaluation are also
supplied. Auxiliary-supported cofinality, honest K₀ image/kernel, canonical null
and signed initial cone are proved. Basic global support has the actual
same-null cone/fiber comparison to the fine completion and original signed
boundary. The auxiliary-supported original seeds, whole null-transition
equations, finite/telescope comparisons and stable r_Z∞ are also proved.
The native auxiliary fiber-forget localization and completed geometric
evaluation remain separate. Intrinsic Laurent unit K₁
classes and native O/O(−1) two-summand chart formulas are proved, without a
projective-line K-equivalence or initial-seed preservation claim. The canonical
native flat-base-change mate now covers all intrinsic perfect inputs, and
affine perfect coefficients have an objectwise chosen positive projection
isomorphism and actual O(−1) vanishing. This supplies no perfect pushforward for
arbitrary P¹ inputs or projective generation. Actual native/pair polynomial
zero evaluation also splits the original common corner in all recursive Bass
degrees, without supplying its middle exactness or seed stabilization.
Original native section/span evaluation now has levelwise equivalence and
literal span/cone/loop HEP/T1. The P¹ line/quotient determinant pairing and
canonical tautological pullback-tensor comparison are proved over arbitrary
rings/maps. Conditional finite-attachment tools preserve actual strict chart
windows; their global epimorphism/QC-representative inputs remain separate.
The signed Bass span quotient and natural short exact row are proved under
their explicit original retraction/excision/collapse data; native realization,
recursive middle exactness and original seed preservation remain open.
These constructions do not identify classical Kᴮ. The current dependency plan is in the
[TT localization roadmap](../development/TTLocalization.md).

## Ring plus construction

For every unital ring `R : Type u`, the independent zero component of
projective completion satisfies the explicit homological plus specification
for all target local systems in coefficient universe `u + 1`. The specified
original Q-loop map is a weak homotopy equivalence. Positive comparison
naturality retains common-universe ring maps and their basepoint corrections.
Actual completion and telescope components identify with original K₀;
none of these statements supplies a whole-space splitting.

The matrix-image ring-change functor has the additive scalar-extension Hom
universal property for arbitrary ambient target modules, with independent
source-ring, target-ring, and target-module universes. This does not construct
a separate literal noncommutative balanced-tensor carrier. General CW
characterization/uniqueness, arbitrary coefficient-universe transport, a
homotopy-equivalence upgrade, and a separate based homotopy of the chosen
loop-map composites remain outside the stated interfaces.

## Remaining comparisons


- Fixed-degree finite Bass-transition stabilization, bijectivity of the natural negative-class maps into the telescope, and classical telescope negative-group identification.
- Full all-iterate comparison with the original geometric Bass tower, the fundamental theorem, and Laurent-unit boundary/relative-loop basepoint calculations, including the zero-section class and possible Nil terms.
- Normalized geometric chart-composition and complete seed/iterate/telescope evaluation, native auxiliary fiber-forget localization, and classical Thomason–Trobaugh identification, retaining the original K₀ image and signed boundary. Basic global supported localization and auxiliary-supported coarse-to-fine completion are proved.
- Proj identification, the full twisting-sheaf family, arbitrary locally-perfect coefficient preservation and bounded representation, projective generation, and the projective-bundle formula. The older finite-coefficient retract criterion retains its own projectivity/splitting and support-window assumptions; vector-bundle and explicitly bounded vector-bundle projection perfection are proved by the new finite-defect route.
- General-source perfect preservation by derived direct image, unrestricted unbounded derived pushforward, and general bounded-below flat-base-change invertibility.
- Strict/local equivalence on arbitrary nonaffine schemes and perfect pullback on arbitrary non-quasi-compact schemes.
- General stable cofiber excision, the remaining quotient homotopy-invariance questions, and a standard stable model structure or triangulation for the categorical localization.
- The triangulated-derived Grothendieck presentation of perfect objects, general exact-category dévissage/localization, and full Serre-pair coherence.
- Cross-universe transport beyond the explicit small-model and common-ring-universe plus-comparison interfaces, literal noncommutative tensor-product scalar-extension identification, and higher raw-spectrum/telescope coherence.

Regularity alone does not give the resolution property. Finite cube HELP does
not imply arbitrary compact HELP, and endpoint collar deformation alone does
not supply vertical lifting. Keep the stated hypotheses when composing interfaces.

## Verification

The pinned environment is Lean `v4.34.1` and mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`. From the library checkout, run
`bash scripts/check.sh --rehash`. The complete pipeline checks import
generation, module layout, placeholders, script tests, library and maintained
test builds, environment and text lint, the independently configured client,
and explicit replay of both transitive axiom audits including private project
declarations. The allowed foundation axioms are `propext`, `Classical.choice`,
and `Quot.sound`.

Exact trust coverage is described in [architecture](../development/Architecture.md#trust-checks);
[contributing](../../CONTRIBUTING.md) owns commands and dependency policy.
[Performance](../development/Performance.md) records bounded matched
measurements. Successful checks concern encoded statements and their audited
foundation dependencies. Mathematical interpretation and source correspondence
need their own assessment; passing checks proves no absent comparison.
