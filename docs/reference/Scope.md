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
| Ring plus comparison | Independent homological stable-BGL model, exact standard zero-component Q-loop homotopy equivalence, original K₀-times-plus product, and ordinary forward-map ring-change naturality |
| Finite-projective scalar extension | Matrix-image change of rings, additive Hom universal property and literal noncommutative balanced-tensor identification with exact finite-projective base change |
| Classical CW plus comparison | Constructed comparison homotopy equivalences and ordinary uniqueness for original plus maps on actual Hausdorff CW spaces, with an explicit common coefficient universe for mixed spaces |
| Dévissage and resolution | Abelian finite-filtration dévissage and admissible finite-resolution comparisons |
| Serre and G-localization | Specified Serre quotients, finite-module G-theory, and connective tails |
| Scheme K/G-theory | Vector bundles, finite-type/coherent sheaves, restriction, K→G, and noetherian open/closed localization |
| Regular K→G | Regular affines; quasi-compact regular schemes with the resolution property |
| Perfect complexes | Strict/local models, derived local perfectness, change of cofibrations, support, and bounded-flat representatives |
| Model comparisons and pullback | Vector-bundle/strict equivalence on every scheme; affine strict/local equivalence; canonical lower-bounded-to-original perfect K comparison on quasi-compact schemes; perfect pullback between quasi-compact schemes; explicit Gillet–Waldhausen term hypotheses |
| Connective localization | Quasi-compact opens of qcqs schemes, positive equivalence, exact K₀ image, boundary, and connective tails |
| Auxiliary support, excision, and Mayer–Vietoris | Natural supported localization; open-cover support excision; connective two-open sequence and matching K₀-class gluing |
| Finite pushforward | Coherent G and finite-flat vector-bundle/strict-perfect K direct images on locally noetherian schemes, with canonical comparison laws |
| Derived sheaf operations | Bounded-below direct image, flasque/affine units, composition, projection formula, and canonical ordinary/derived base-change mates |
| Laurent and Čech finite models | Finite-defect parametrices, projector/module homotopy models, actual sheaf Čech comparisons, and perfect derived projection images for vector-bundle singles and explicitly bounded vector-bundle complexes |
| Projective-line geometry | Actual two-chart line, tautological line and quotient, original all-coefficient D+ diagonal triangles and genuine roof naturality, intrinsic-perfect bounded QC/strict models and perfect original derived projection images over arbitrary commutative rings |
| Spectra and stable localization | Iterated S Ω-spectrum, additive K-comparison, signed looping, stable fiber sequence, coherent-homotopy quotient, and categorical stable localization |
| Finite homotopy excision | All-point connectivity, finite cube HELP, original double-cylinder gap bound, and S-model/finite Bass-stage stable cone sequences |
| Telescopes and Ω replacement | T1 finite-stage representatives and stable colimits, strict cone/pushout interchange, track-defined maps, and loop-tail Ω replacement |
| Bass groups and finite stages | Affine/scheme/supported cokernel recursions, strict Laurent seed and iterates, raw one-step comparisons, an objectwise first-to-second seed map, and natural finite-stage bottom-group isomorphisms |
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

On the actual two-chart line, objectwise global strict models and perfect
original derived projection images are also proved for every intrinsic perfect
D+ input over an arbitrary commutative ring. Natural exact models on genuine
roofs, projective generation, and the projective-bundle formula remain separate. The precise
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
groups are actual cokernel recursions with their original K₀ seeds. Affine
finite-stage comparisons identify the original group with degree `-i`, with
vanishing below that degree. The compact native ambient comparison also
identifies the original scheme recursion on every coefficient fiber with its
finite-stage degree `-i` group, preserving coefficient maps and the original
Laurent quotient. Its finite comparison and original negative-class telescope
map are natural under scheme restriction between compact endpoints. The actual
ambient seed/telescope restriction needs no compactness premise and preserves
all original cylinder/inclusion faces and identity/composition. Supported
original-group comparisons remain separate. Affine and compact native ambient
telescope inclusions give original natural class maps without proved bijectivity or stabilization
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
Native auxiliary fiber-forget localization now retains the actual union-support
fiber, original forward seeds, whole canonical null and same-null telescope
cone/fiber maps with their signed boundary. Final fine stability requires
compact P,Q,T and quasi-separated Q. Completed geometric evaluation remains
separate. Intrinsic Laurent unit K₁
classes and native O/O(−1) two-summand chart formulas are proved, without a
projective-line K-equivalence or initial-seed preservation claim. The canonical
native flat-base-change mate now covers all intrinsic perfect inputs, and
affine perfect coefficients have an objectwise chosen positive projection
isomorphism and actual O(−1) vanishing. The intrinsic-perfect pushforward producer described below supplies the
objectwise P¹ result; natural projective generation remains separate. For qcqs bases the actual native polynomial restriction pair has the kernel
of the original signed Laurent difference in every nonnegative degree.
The native first coordinate and its coefficient cone have the original
positive identity and negative polynomial-scalar chart formulas over
quasi-compact bases; the cone is supported outside the positive range.
The forgotten cone K-class and terminal boundary identification remain separate.
Actual native/pair polynomial
zero evaluation also splits the original common corner in all recursive Bass
degrees, without supplying its middle exactness or seed stabilization.
Original native section/span evaluation now has levelwise equivalence and
literal span/cone/loop HEP/T1. The P¹ line/quotient determinant pairing and
canonical tautological pullback-tensor comparison are proved over arbitrary
rings/maps. Conditional finite-attachment tools preserve actual strict chart
windows. The global top-cycle epimorphism and finite strictification are now
produced for bounded-below termwise-QC locally perfect representatives on P¹
over arbitrary R; actual Rp preserves their perfection. A genuine bounded
termwise-QC model is also constructed for every intrinsic perfect D+ input;
its global strict model and perfection under original Rp follow without a
supplied replacement or noetherian premise. Naturality and an exact
Waldhausen roof model remain separate. Normalized evaluation/composition and
chart/cylinder pasting, the original whole-track cone evaluation and positive
source-null/one-step seed comparison have independent mathematical acceptance.
The cone evaluation is weak at every level. Both actual mixed fillers now
supply the original two-chart seed comparison, with no mixed-comparison input
left to the caller. `CoefficientBassSeedIteration.stepMap` constructs the
objectwise first-to-second raw Bass map with its original cone inclusion,
cylinder and loop-coordinate formulas. Second-stage coefficient compatibility,
coherent all-iterate/telescope comparisons and initial-seed invertibility
remain open. The composite polynomial attachments and native precomposed and
postcomposed cube evaluations give additional fixed faces, without a global
categorical coherence theorem.
The original polynomial coefficient unit square and whole original-span unit
are now constructed, with exact chart tracks and cylinder parameterization.
Both Laurent chart unit squares are supplied; the whole Bass identity still
requires its missing six-face cube or another complete original comparison.
One eight-slot split-normalization simplex and its six displayed-component
triangle lifts are constructed. Their assembled evaluation is now proved
equal to the exported original triple track on all levels and parameters,
with whole-value-preserving producer factorizations. One merged 18-node
diagram and the exact full original double-square scalar rectangle are now
supplied, including complete geometric route faces and continuous three-side
collapse. The generic terminal chart pause retains explicit lift premises.
Both original Bass chart pauses and the full prescribed bottom surface now
share a merged 44-simplex, with six anchored reference/full dependent-node
equalities and literal shared scalar edges at their original speeds. Generic
varying-family composition uses the actual realization-product homeomorphism,
with independent parameters and structure time. A separate actual 30-simplex
now realizes the entire original H0 cylinder face, its four scalar edges at
native speed, degree-zero loops, point and independent structure laws. The
joint H0/chart/bottom family and whole H1/M surfaces now belong to one
actual 139-simplex. `MWholeNativeCube` constructs the genuine six-face
composition cylinder, with all twelve whole edges, original level zero and
independent structure time. `MWholeCubeConsumers` gives the original
comparison, cone and parameter-looped step composition without a supplied
cube or compatibility premise. Independent review and fresh canonical
checks cover all 1,619 defining origins, including 54 private names; ROOT
and full-private coverage agree. The separate unit cube, raw tower,
telescope and classical identification remain open. The first Godement functor on
all scheme module sheaves is exact, flasque-valued and has its original natural
monic germ unit. Its exact cokernel iteration now supplies the natural augmented
flasque sheaf resolution and original augmentation quasi-isomorphism, preserving
short exact sequences. Its actual natural totalization now retains every
lower bound, has flasque terms, preserves short exact sequences and
degreewise monomorphisms, and has the original augmentation quasi-isomorphism
on every Plus complex over every scheme. Genuine weak maps are preserved;
the installed derived-unit comparison Q(f_*T(K))≅Rf_*(Q(K)) is natural for
every scheme map. The exact perfect/flasque model and roof K comparison
remain separate from that totalization result. The actual flasque-perfect
Waldhausen inclusion and Godement total now give two forward weak units and
mutually inverse original K-maps on every scheme in every nonnegative degree,
including zero. Their literal composite inclusion into all perfect complexes
is bijective on quasi-compact schemes. Actual pushforward preserves short
exact sheaf and complex sequences with flasque first terms without bounds.
The literal lower-bounded locally-perfect inclusion
now induces the original delooping weak equivalence and canonical K-map
bijection on every quasi-compact scheme, including degree zero. Its actual
opposite-App2/S-duality proof uses no Godement or global truncation-exactness
premise. Literal exact G₀=p_* and G₁=p_*T(−⊗L)[1] now act on the actual
flasque-perfect model, with an exact product and natural original installed
unit/augmentation/shift comparisons over every R including zero. Actual exact
Phi now totalizes the original O/O(-1) sum and agrees with the EXISTING native
two-summand functor and K-map after literal model inclusion and actual affine
transport. Naturality in coefficient-complex maps at each fixed R, original
chosen zeros and both Product.KEquiv maps are retained in every degree,
including zero. The canonical positive unit on original strict affine
coefficients is a genuine quasi-isomorphism; its actual weak span proves the
original positive K-map equality, and the literal strictTotal source K-map is
bijective in every nonnegative degree. The literal model signed shift now
induces inversion on original K-groups for every scheme and natural degree.
The original determinant-normalized Euler conflation, weak-zero middle and
actual additivity prove K(E2[1])=K(E0) on strict affine coefficients; its
canonical connecting isomorphism is separately retained.
[`FlasqueGPhiMatrix`](../../Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/FlasqueGPhiMatrix.lean)
proves the actual product-category K(G)∘K(Phi)=id and literal composite
KMap(Phi⋙G)=id for every R and every natural degree, including zero. The four
actual entries, proved strictTotal K-map surjectivity and unchanged original
product K-equivalence are independently reviewed and native.
[`FlasquePhiInverse`](../../Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/FlasquePhiInverse.lean)
now proves the opposite K(Phi)∘K(G)=id and the literal composite KMap(G⋙Phi)=id
through the actual three endpoint weak spans and original diagonal
additivity. Both original model K-map composites are identity; the EXISTING
nativeTwoSummandKMap is bijective over every affine R and natural degree,
including zero. nativeAffineTwoSummandKEquiv retains its literal forward
map. Independent complex ordinary review, original public-root interfaces
and complete origin audits passed. P5 now supplies original native open
K-map naturality, global projection perfection on every quasi-compact base,
and exact literal native G0/G1 with their original units and signed shift.
For every base open Z, acyclicity of K on literal p^-1 Z implies acyclicity
of both coefficients on Z, without quasi-separatedness or compactness of Z. These six
native sources have independent complex ordinary reviews, native ROOT
interfaces and complete checked-origin coverage of 84 prerequisite and
124 coefficient declarations. The actual native Phi model and original
inverse-image supported boundary square are also supplied. The EXISTING
native two-summand K-map is now bijective on every qcqs base, and its
original supported map is bijective for every compact base open, in every
natural degree including zero. `NativeGlobalBundle` and `NativeGlobalSupport`
retain the literal forward maps and original product coordinates through
actual Mayer–Vietoris/localization ladders and two-stage affine-cover induction.
Independent complex ordinary reviews and native ROOT/checked-origin coverage
passed. The actual canonical positive unit and native negative/Euler
entries now give original GΦ=id on every quasi-compact base.
`P5NativeGlobalInverse` uses the independently proved Phi bijection to
give ΦG=id on qcqs bases and identifies the actual geometric G with the
EXISTING nativeGlobalTwoSummandKEquiv.symm. Both original ordered
coordinates and product K-equivalence are retained. Independent complex
ordinary review, strict 200k source coverage, 36 current ROOT examples and
all 377 checked defining origins passed; ROOT and full-private coverage agree.
Actual LEFT-L tensor followed by totalization now maps the original diagonal
conflation to exact functors, with native additivity in every natural degree.
`FlasquePhiColumns` retains the literal positive and unshifted negative
column expression for K(Phi)∘K(G); the actual three endpoint identifications
now close the affine inverse.
The original diagonal tensor sequence now extends to all bounded-below module
coefficients as a genuine complex SES and canonical D+ triangle. Its whole-functor
localization retains inverse roofs, original connecting maps and naturality;
the projected third term is naturally R(− tensor Q). Explicit whole original
vector-bundle single correspondence is supplied. Natural intrinsic-perfect
generation is now proved on the actual two-chart P¹ over every commutative R,
including zero, with the original endpoint maps, specified contractions,
negative shifted incidence and perfect G₀/G₁ coefficients. The actual affine
two-summand K inverse and original native qcqs/support K-bijections are
supplied, including the actual native qcqs geometric G inverse. The broader
projective-bundle formula remains separate.
The signed Bass span quotient and natural short exact row are realized for
the actual ambient, open, supported and auxiliary-supported coefficient Model
families at every finite stage and in every integer degree. Polynomial zero
evaluation and finite Model geometry construct their original retraction,
excision and collapse data. The original family hypotheses remain; recursive
chart middle exactness and original seed preservation remain open.
These constructions do not identify classical Kᴮ. The current dependency plan is in the
[TT localization roadmap](../development/TTLocalization.md).

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
[standard normalization](StandardSignMigration.md) records the direct refactor.

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
[the classical CW guide](../topics/ClassicalCWPlus.md).

## Remaining comparisons


- Fixed-degree finite Bass-transition stabilization, bijectivity of the natural negative-class maps into the telescope, and classical telescope negative-group identification.
- Full all-iterate comparison with the original geometric Bass tower, the Laurent splitting and original fine [T] terminal boundary, including the zero-section class and possible Nil terms. The positive exact row on PerfectK(Spec R) and the original relative scalar-to-cofiber boundary are proved; they do not close these remaining comparisons.
- Complete original raw iterate/telescope evaluation and classical Thomason–Trobaugh identification, retaining the original K₀ image and signed boundary. Normalized geometric chart-composition, original cone/null/one-step seed comparison, basic global supported localization and auxiliary-supported section-completion localization are proved.
- Proj identification, the full twisting-sheaf family, and the general projective-bundle formula. Intrinsic-perfect D+ generation and both actual affine model K-map inverse laws are supplied over every commutative ring. Both actual native qcqs model inverse laws and identification of geometric G with the EXISTING native inverse are supplied, together with original compact-open supported Phi bijectivity, in every natural degree including zero. Literal forward maps, signs and product normalization are retained. Native projection perfection and exact coefficient/support preservation hold on general quasi-compact bases. The separate specialized endpoint-unit/connecting and arbitrary-base-map comparisons remain open.
- General-source perfect preservation by derived direct image, unrestricted unbounded derived pushforward, and general bounded-below flat-base-change invertibility.
- Strict/local equivalence on arbitrary nonaffine schemes and perfect pullback on arbitrary non-quasi-compact schemes.
- General stable cofiber excision, the remaining quotient homotopy-invariance questions, and a standard stable model structure or triangulation for the categorical localization.
- The triangulated-derived Grothendieck presentation of perfect objects, general exact-category dévissage/localization, and full Serre-pair coherence.
- Cross-universe transport beyond the explicit small-model and common-coefficient plus-comparison interfaces, coherent natural chosen inverses, and higher raw-spectrum/telescope coherence.

Regularity alone does not give the resolution property. Finite cube HELP does
not imply arbitrary compact HELP, and endpoint collar deformation alone does
not supply vertical lifting. Keep the stated hypotheses when composing interfaces.

## Verification

The pinned environment is Lean `v4.34.1` and mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`. All normal workflows must use
incremental checks of the changed or missing required modules and their affected
consumers, reusing trusted artifacts and compatible validation evidence under
[the validation policy](../../CONTRIBUTING.md#tests-and-checks). Complete coverage
may combine that retained evidence with new affected-scope checks; merge,
integration, or release alone does not require the complete pipeline.

For explicit comprehensive diagnostics and declared CI coverage,
`bash scripts/check.sh --rehash` checks import
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
