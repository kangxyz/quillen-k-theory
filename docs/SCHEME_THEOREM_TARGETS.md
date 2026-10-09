# Scheme K/G-theory: theorem contracts and first implementation path

Audit date: 2026-10-09. These are mathematical targets, not claims that the scheme theorems have already been formalized. The completed input is the small-abelian canonical connective localization theorem in `Quillen/Localization/Serre/LocalizationTheorem.lean`, together with `Quillen/Devissage/Homotopical.lean`.

**Recommended first endpoint:** connective G-theory localization for a noetherian scheme and an open subscheme. Build the actual coherent-sheaf categories and actual restriction quotient equivalence. This uses the completed abelian theorems directly. Define vector-bundle K-theory alongside the coherent foundations when its exact structure is available. Perfect-complex and nonconnective localization are separate, later endpoints.

## 1. Three different theories

### 1.1 Vector-bundle Quillen K-theory

For a scheme `X`, let `Vect(X)` be finite locally free `O_X`-modules, with all sheaf morphisms between them. Its conflations are the sheaf short exact sequences whose three terms are finite locally free. These sequences are locally split; they need not split globally. Using only globally split sequences would define the wrong exact category in general.

Set

`Kᵛᵉᶜ_n(X) = π_(n+1)(BQ(Vect(X)), 0)`, for `n : ℕ`,

after the size transport described below. No noetherian, regular, finite-dimensional, quasi-compact, or separated hypothesis is needed merely for this exact category and connective definition. Finite rank means locally finite rank, not a chosen global constant rank. See [Stacks, 0B37](https://stacks.math.columbia.edu/tag/0B37) for the exact structure.

For every scheme morphism `f : X → Y`, pullback carries vector bundles to vector bundles and preserves these locally split sequences. Thus it induces the canonical contravariant maps. Do not justify this by claiming that pullback is exact on all sheaves. A locally split sequence stays split after pullback, which proves the required restricted exactness. The identity/composition statements must include the usual pullback natural isomorphisms before applying exact-functor K-theory.

### 1.2 Coherent-sheaf G-theory

For a locally noetherian scheme `X`, let `Coh(X)` be the full category of coherent `O_X`-modules. It is abelian, with kernels, cokernels and short exact sequences computed in sheaves: [Stacks, 01Y0](https://stacks.math.columbia.edu/tag/01Y0). Define

`G_n(X) = K_n(Coh(X))`, for `n : ℕ`.

On a locally noetherian scheme, coherent sheaves are exactly finitely presented sheaves, equivalently quasi-coherent sheaves of finite type: [Stacks, 30.9.1](https://stacks.math.columbia.edu/tag/01XY). Thus the existing finite-presentation predicate is a valid candidate definition, provided its closure and comparison theorems are actually proved.

**Ambient-category warning:** `Coh(X)` is Serre in `QCoh(X)`, but only weak Serre in all `O_X`-modules. Closure under kernels/cokernels of maps *between coherent objects* and extensions is enough to construct its abelian category. Closure under arbitrary subobjects in `X.Modules` is false. The subobject/quotient statement requires quasi-coherence: [Stacks, 01Y1](https://stacks.math.columbia.edu/tag/01Y1). In particular, do not instantiate `IsSerreClass` for coherence in the category of all sheaves.

The first localization theorem below assumes **noetherian**, not merely locally noetherian. Here noetherian includes quasi-compactness. It implies quasi-separatedness, and every open subscheme is noetherian and quasi-compact; an additional separatedness hypothesis is unnecessary. See [Stacks, 01P0](https://stacks.math.columbia.edu/tag/01P0).

### 1.3 Perfect-complex K-theory

`Perf(X)` denotes perfect complexes with their derived/Waldhausen enhancement and quasi-isomorphisms. Perfect means locally quasi-isomorphic to bounded complexes of finite locally free modules. It does not mean that a global bounded vector-bundle representative has already been chosen.

Use distinct names for the connective spectrum `Kᵖᵉʳᶠ(X)` and its nonconnective extension `Kᴮ(X)`. Applying the present Q-construction to the underlying additive category of perfect objects is not a definition of either one: the weak-equivalence/derived structure is essential. Sources are [Thomason–Trobaugh (TT), §§3 and 6–7](https://gwern.net/doc/math/1990-thomason.pdf#page=66), and [Stacks, 0656](https://stacks.math.columbia.edu/tag/0656) for the affine perfect-complex definition.

For `X` locally noetherian, inclusion of vector bundles into coherent sheaves gives a comparison `Kᵛᵉᶜ_n(X) → G_n(X)`. It is not generally an isomorphism. The maps from vector bundles to perfect complexes, and from perfect complexes to coherent-derived G-theory under suitable hypotheses, are further comparison theorems, not definitional equalities.

## 2. First localization endpoint: supported coherent sheaves

Let `X` be a noetherian scheme, let `j : U ↪ X` be an open immersion, and put `Z = |X| \ |U|`. Initially `Z` is a closed topological subset; no scheme structure on it is needed. Define

`Coh_Z(X) = { F ∈ Coh(X) | j*F ≅ 0 }`.

Prove this is equivalently the condition `Supp(F) ⊆ Z`. Restriction is exact and its kernel is a Serre subcategory of the *coherent* abelian category. Write `G⁽ᶻ⁾_n(X) = K_n(Coh_Z(X))`.

The required geometric quotient theorem is

`Coh(X) / Coh_Z(X) ≌ Coh(U)`.

Its forward functor must be induced by the actual restriction `j*`, with a proved natural isomorphism

`quotientFunctor ⋙ quotientRestriction ≅ restriction`.

After constructing that equivalence and transporting sizes, apply the proved Serre theorem to obtain a boundary

`∂_n : G_(n+1)(U) → G⁽ᶻ⁾_n(X)`

and, for every `n : ℕ`, the three exactness identities

1. `range(G⁽ᶻ⁾_n(X) → G_n(X)) = ker(G_n(X) → G_n(U))`;
2. `range(G_(n+1)(X) → G_(n+1)(U)) = ker(∂_n)`;
3. `range(∂_n) = ker(G⁽ᶻ⁾_n(X) → G_n(X))`.

The low-degree tail is

`G_1(X) → G_1(U) → G⁽ᶻ⁾_0(X) → G_0(X) → G_0(U) → 0`.

The last arrow from `G_0(X)` is surjective. Here `G_0` is the actual homotopical `π₁ BQ`, so the current proof does not need to detour through the unproved Grothendieck-group comparison. Until that comparison or a separate commutativity theorem is established, use the existing group-valued Lean API without claiming its commutative-group instance has been proved.

At the space level, the inherited formal endpoint is bijectivity on every homotopy set, including `π₀`, for the canonical map from `BQ(Coh_Z(X))` to the actual homotopy fiber of the quotient map, followed by the geometric quotient equivalence. A literal comparison to the fiber of the actual `j*` map needs the natural-isomorphism and fiber-transport construction. A global homotopy inverse must not be claimed from the current weak-comparison theorem.

### 2.1 Proving the quotient equivalence, rather than assuming it

The following is a concrete proof plan using the verified scheme lemmas. It is the mathematical work to formalize; none of its conclusions belongs as an unproved field of a purported scheme-localization instance.

1. **Exact restriction and kernel.** Build the actual exact functor `j* : Coh(X) → Coh(U)`. A map becomes an isomorphism precisely when its kernel and cokernel restrict to zero. Hence restriction inverts the actual Serre-quotient denominators and descends to the quotient.
2. **Essential surjectivity.** Every coherent sheaf on `U` extends to one on `X`. For this noetherian setting, apply finite-type quasi-coherent extension [Stacks, 0G41](https://stacks.math.columbia.edu/tag/0G41), and then the coherent/finite-type comparison. This does not say `j_*` itself preserves coherence.
3. **Fullness.** Given `φ : F|_U → G|_U`, find a coherent subsheaf `F' ⊆ F`, equal to `F` over `U`, to which `φ` extends. The inclusion `F' → F` is a denominator, giving the required quotient roof. This is [Stacks, 0FD0](https://stacks.math.columbia.edu/tag/0FD0). On noetherian `X`, [Stacks, 01YB](https://stacks.math.columbia.edu/tag/01YB) supplies the stronger description using `I^m F` for an ideal defining the complement.
4. **Faithfulness.** A quotient morphism is represented by a suitable fraction. If its restriction vanishes, its numerator has image in `Coh_Z(X)` after passing to the representative's source and target. Exactness then kills that image in the quotient. Alternatively prove that the induced exact functor has zero kernel and use the abelian-category criterion for faithfulness. This step must concern all quotient morphisms, not just original sheaf maps.
5. **Canonical comparison.** Promote the resulting fully faithful, essentially surjective functor to an equivalence. Prove equality of the induced K-homomorphisms after the natural-isomorphism identification. Transfer every exactness position and the boundary through those specific equivalences.

An exact functor with the right kernel is not by itself a quotient equivalence. An arbitrary equivalence of K-groups is also insufficient to identify the canonical restriction and inclusion maps.

## 3. Replacing the support term by the closed subscheme

Let `i : Z₀ ↪ X` be a closed immersion of schemes whose underlying image is `Z`, and let `I` be its quasi-coherent ideal. Since `X` is noetherian, `Z₀` is noetherian. The target is a canonical isomorphism

`G_n(Z₀) ≅ G⁽ᶻ⁾_n(X)`

induced by `i_*`, for every `n : ℕ`.

This is **dévissage, not an equivalence of the two abelian categories**. The essential image of `i_*` consists of sheaves killed by `I`; support in `Z` only implies annihilation by some power of `I`. Use:

- Exact, fully faithful pushforward and its annihilator description: [Stacks, 01QY](https://stacks.math.columbia.edu/tag/01QY).
- The coherent version: [Stacks, 087T](https://stacks.math.columbia.edu/tag/087T).
- For each coherent `F` supported in `Z`, existence of some `m` with `I^m F = 0`: [Stacks, 01Y9](https://stacks.math.columbia.edu/tag/01Y9).

Inside the abelian category `Coh_Z(X)`, the property `IF = 0` contains zero and is closed under subobjects, quotients and finite products. It need not be extension closed. Construct the actual finite filtration

`0 = I^m F ⊆ I^(m-1) F ⊆ … ⊆ IF ⊆ F`.

Each successive quotient is killed by `I`, hence comes from a coherent sheaf on `Z₀`. No uniform exponent for all coherent sheaves is needed. This matches the hypotheses of the completed `Devissage.KMap_bijective` exactly, after the small-model and categorical-equivalence transports.

The resulting geometric sequence is

`… → G_(n+1)(U) → G_n(Z₀) →[i_*] G_n(X) →[j*] G_n(U) → …`,

ending `G_0(Z₀) → G_0(X) → G_0(U) → 0`. The boundary is the support boundary followed by the inverse of the proved pushforward K-isomorphism.

Consequences within the same machinery include invariance of G-theory under a nilpotent closed thickening, and `G_n(X_red) ≅ G_n(X)` for noetherian `X`. Do not transfer this nil-invariance claim to vector-bundle K-theory: it is false in general.

## 4. Size and universe obligations

The current localization theorem takes `(C : Type u) [Category.{u} C] [Abelian C]`. The actual category `X.Modules` has sheaf objects in a larger universe than its morphisms. The notation `Coh(X)` does not resolve this mismatch.

There are two legitimate routes, and their claims should remain distinct:

1. **Larger-universe first implementation.** Use mathlib's `AsSmall` to lift both objects and morphisms to a common sufficiently large universe. Transport the actual abelian/exact structure, restriction functor, support property and quotient. Prove the canonical K-map comparison. This does not prove essential smallness in the original base universe, but can legitimately feed the existing single-universe theorem at a larger level.
2. **Essentially small model.** Prove local smallness and a set of isomorphism-class representatives, then use `SmallModel`/`equivSmallModel` and transport the same data. [Stacks, 01BC](https://stacks.math.columbia.edu/tag/01BC) constructs a representative set for finite-type sheaves on any fixed ringed space. The coherent and finite-locally-free classes are isomorphism-invariant subclasses. This is a concrete route to their essential smallness, not an axiom.

A chosen skeleton alone does not automatically give strict restriction functors, matching zeros, or commutative K-diagrams. Build the functors by conjugating with the chosen equivalences and retain unit/counit natural isomorphisms. Prove independence of the chosen small model at the canonical-map level. If mixed-universe comparisons are not yet available, state the higher-universe endpoint honestly and postpone universe-lowering independence as an explicit separate theorem.

Do not replace coherent sheaves with all small sheaves merely to satisfy universe parameters. That would change the theory, not solve its size problem.

## 5. Comparison and perfect-localization contracts

### 5.1 Safe K/G comparison targets

The most direct Q-theoretic target is the canonical inclusion

`K_n(Vect(X)) → K_n(Coh(X))`

under the geometric hypothesis that every coherent sheaf has a **finite resolution by finite locally free sheaves**. Together with the actual vector-bundle exact structure and its closure under kernels of surjections, this is the resolving-subcategory application of Quillen's resolution theorem. That theorem is new work if this route is selected; the completed abelian dévissage theorem does not replace it.

A first concrete test case is `X = Spec R` for a commutative noetherian regular ring `R`. Every finite `R`-module has a finite resolution by finite projectives; importantly this is an objectwise finite-resolution statement, not a claim of a uniform global dimension bound. See [Stacks, 0656, Lemma 15.76.14](https://stacks.math.columbia.edu/tag/0656). One may next treat regular noetherian schemes with the resolution property, proving the global finite-resolution assertion from enough vector-bundle surjections, locally finite projective dimension and quasi-compactness. A finite-dimensional hypothesis is a sufficient optional simplification, not part of the first G-localization theorem and not required for the regular perfect/coherent comparison below.

For noetherian regular `X`, perfect objects coincide with bounded coherent-cohomology objects: [Stacks, 0FDC](https://stacks.math.columbia.edu/tag/0FDC). Turning that statement into a higher-K equivalence additionally needs the actual enhanced comparison/Gillet–Waldhausen machinery. It cannot be inferred from a bare triangulated-category slogan in the present Q library.

For a scheme with an ample family of line bundles in TT's sense (including its quasi-compactness convention), TT 3.9–3.10 identify vector-bundle Quillen K-theory with connective perfect K-theory. Under only qcqs plus the resolution property, [Stacks, 0FDJ](https://stacks.math.columbia.edu/tag/0FDJ) directly proves a **Grothendieck K₀** comparison; that source alone is not an all-degree theorem and is not the missing homotopical K₀ comparison in this project.

### 5.2 Exact TT localization scope and tail

Let `X` be quasi-compact and quasi-separated, and `j : U ↪ X` with `U` quasi-compact. Put `Z = X \ U`. Define `Perf_Z(X)` by acyclicity on `U`.

- **Connective:** [TT 5.1](https://gwern.net/doc/math/1990-thomason.pdf#page=91) gives localization after replacing `Kᵖᵉʳᶠ(U)` by the covering spectrum with positive groups unchanged and degree zero `im(K₀(X) → K₀(U))`. In particular, the sequence through `K₀(Perf_Z(X)) → K₀(X) → K₀(U)` is exact where there are adjacent arrows; there is no general terminal surjection onto `K₀(U)`.
- **Nonconnective:** [TT 7.4](https://gwern.net/doc/math/1990-thomason.pdf#page=119) gives `Kᴮ(Perf_Z(X)) → Kᴮ(X) → Kᴮ(U)` as a homotopy-fiber sequence. Its long exact sequence runs through `K₀(U) → Kᴮ_(-1)(Perf_Z(X))` and on into negative degrees.

Neither statement requires noetherianity, regularity, finite dimension, an ample family, or separatedness. These cannot be dropped from *comparison theorems* just because they are unnecessary for TT localization itself. Both supported terms mean perfect complexes on `X` with support, not automatically perfect complexes on the closed subscheme `Z₀`.

The restriction `Perf(X)/Perf_Z(X) → Perf(U)` is, in general, only essentially surjective after idempotent completion. TT 5.2.2–5.2.4 identify the extension obstruction and supply the fraction calculus; the `K₀` obstruction explains the connective tail. Do not insert an unproved, uncompleted quotient equivalence as a field. Even a regular closed immersion alone must not be used here to assert `K(Z₀) ≅ K(Perf_Z(X))` without its own valid dévissage/purity hypotheses and proof.

## 6. Basic properties: scope of the early API

Keep the first properties close to actual exact functors:

- Scheme isomorphisms induce K/G isomorphisms, with identity/composition coherence.
- Vector-bundle K-theory has pullback for every scheme morphism, as in §1.1.
- G-theory has exact open restriction, and flat pullback between noetherian schemes. General nonflat pullback on coherent sheaves is not exact. A finite-Tor-dimension derived pullback belongs to the later complex model.
- Finite morphisms between noetherian schemes, in particular closed immersions, have exact coherent pushforward; [Stacks, 01Y6](https://stacks.math.columbia.edu/tag/01Y6) gives the finiteness and higher-direct-image facts. General proper pushforward requires derived functors, not just an `ExactFunctor` instance for ordinary `f_*`.
- Tensoring by a fixed vector bundle is exact on vector bundles and coherent sheaves. A K-ring structure, an all-degree product, or descent of its action to algebraic K₀ requires additional product/additivity/comparison proofs.
- Nilpotent-thickening invariance for noetherian G-theory is the immediate dévissage application in §3.

Homotopy invariance, projective-bundle formulas, general proper pushforward, localization for perfect complexes, and nonconnective spectra are important subsequent properties, but none is supplied merely by defining the groups.

## 7. Practical implementation order and acceptance gates

At the start of this audit, the pinned mathlib provides the actual abelian `Scheme.Modules`, open restriction machinery, a finite-presentation predicate implying quasi-coherence, and the affine equivalence `AlgebraicGeometry.Scheme.Modules.tildeEquiv`. It does not already provide the required coherent abelian category, its full closure API, or the geometric Serre quotient equivalence. Concurrent foundation work does not count as a verified endpoint until built, imported and audited.

1. **Actual finite sheaf objects and restriction.** Define the full finite-presentation subcategory and the finite-locally-free property on real scheme modules. Prove restriction preserves the predicates. Prove exact open restriction in the ambient sheaf category; the vanishing predicate there is a legitimate Serre predicate, but its K-theory is not G-theory.
2. **Noetherian coherent abelian structure.** First prove affine noetherian closure via the actual module/sheaf equivalence. Then globalize using the locality of finite presentation and exactness. Establish kernels, cokernels, extensions, finite sums and zero. Either construct the coherent abelian full subcategory directly via weak-Serre closure, or first construct the needed abelian QCoh category. Do not demand false arbitrary-subobject closure in all sheaves.
3. **Size and exact-functor transports.** Use the smallest required larger-universe adapter first if it avoids delaying genuine scheme work. Preserve zero/basepoint and canonical K-map identities. Record any remaining smaller-universe independence theorem explicitly.
4. **Definitions and small basic properties.** Define actual `G_n(X)` and, once its nonsplit exact structure is proved, `Kᵛᵉᶜ_n(X)`. Identify the affine versions with finite modules and finite projectives. Retain the distinction between those categories and all modules.
5. **Supported coherent localization.** Build `Coh_Z(X)`, prove §2.1's extension and fraction lemmas, construct the actual quotient equivalence, and apply the completed Serre theorem. A useful first complete test is a principal open `D(f) ⊆ Spec R` for a commutative noetherian ring. It must use the actual localization functor and actual affine-sheaf comparisons; a parameter carrying a desired quotient equivalence is only an adapter, not this theorem.
6. **Closed-immersion dévissage.** Build the ideal-power filtration and exact `i_*` comparison; conclude the geometric `G(Z₀) → G(X) → G(U)` sequence and nil-invariance.
7. **Comparison work when needed.** Prove the resolution theorem only when advancing the selected vector-bundle K/G comparison. Begin enhanced perfect-complex/nonconnective machinery as a separately named target; do not make it a prerequisite for the noetherian G sequence.

The two major new geometric proofs are coherent closure and the restriction quotient equivalence. A structure bundling these as assumptions can be useful internally, but cannot be advertised as proving scheme localization. The final theorem must quantify over the stated schemes and morphisms and discharge those assumptions from their geometry.

## 8. Source and verification notes

- [Quillen, *Higher algebraic K-theory I*](https://link.springer.com/chapter/10.1007/BFb0067053): §4 resolution, §5 abelian dévissage/localization, §7 scheme K′-theory. The original scan's indexed text confirms the vector-bundle/coherent distinction. The Rochester and EPFL full-PDF fetches failed during this audit, so no new printed page number is claimed from those fetches. The coherent-scheme contract above is independently reconstructed from the linked Stacks lemmas and the inspected, completed local Serre/dévissage proofs.
- [Thomason–Trobaugh, *Higher Algebraic K-Theory of Schemes and of Derived Categories*](https://gwern.net/doc/math/1990-thomason.pdf): original-paper scan inspected at 1.11.7, 3.8–3.14, 5.1–5.2 and 7.4. PDF page numbers in links are one-based; printed pages for 5.1 and 7.4 are 337 and 365 respectively.
- The individual Stacks tags are the primary, version-stable references for the scheme ingredients. Stacks' algebraic/triangulated K₀ results are not substituted for higher-K or homotopical-K₀ proofs.
- Local files inspected: `ExactFunctor.lean`, `KTheory.lean`, `KMapFunctoriality.lean`, `KMapHomotopyEquivalence.lean`, `ClassifyingSpace.lean`, `DevissageSetup.lean`, `DevissageHomotopical.lean`, `SerreLocalizationTheorem.lean`, `docs/STATUS.md`, `docs/PLAN.md`, and the pinned mathlib's scheme-module and small-category files. This document changes no Lean proof and reports no new Lean build.
