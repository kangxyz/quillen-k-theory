# Independent review: canonical K-to-G for Spec(PID)

Reviewed 2026-10-09, independently of the proof author and the earlier length-one reviewer. No proof source was changed.

## Endpoint contract

`Scheme.KToG_pid_bijective R n` has only a commutative ring object `R`, `IsDomain R`, `IsPrincipalIdealRing R`, and `n : ℕ` as inputs. It proves bijectivity of the existing public `Scheme.KToG (Spec R) n`. `KToGPIDEquiv` uses that very homomorphism, and `KToGPIDEquiv_toMonoidHom` is proved by reflexivity. No resolution, homotopy-equivalence, target-equivalence, or categorical-contractibility hypothesis is hidden in this PID endpoint.

## Geometric bridge checked

1. A finite module has an actual finite free surjection with a finite kernel over a noetherian ring. Over a PID, the kernel is torsion-free by injectivity into the free module and hence free. This provides an actual length-one resolution, with all maps and short exact stages retained.
2. A finite projective module gives genuine finite local sheaf bases: freeness over prime localizations spreads to principal opens and is transferred to the actual sheaf over-site. Conversely, a local sheaf basis gives free localized global sections; the free-locus criterion proves the finite presented module projective. The noetherian affine equivalence therefore identifies actual vector bundles with finite projective modules.
3. The inverse affine module/coherent-sheaf equivalence is an exact functor. It carries the actual module resolutions to actual coherent resolutions. The endpoint is the original coherent sheaf, transported using the equivalence unit. Isomorphism transport and exact-functor transport preserve resolution length.
4. The canonical vector-bundle inclusion lifts to the full subcategory of vector bundles in the chosen small coherent category. The lift is proved fully faithful and essentially surjective, and its exact structure is proved to be the original transported vector-bundle exact structure. The proof does not infer exact equivalence from categorical equivalence alone.
5. `vectorBundleSmall_factor` identifies the composite of that lifted exact equivalence with the inherited exact inclusion as the original canonical small comparison, definitionally. The all-degree length-one resolution theorem therefore proves bijectivity of precisely the existing `Scheme.KToG` map.

## Resolution/source review

The seven resolution modules were read independently: `Finite`, `Closure`, `QCalculus`, `Covers`, `FullQ`, `InheritedQ`, and `LengthOne`. They store actual conflation towers; derive admissible-subobject closure by pullback comparison; construct actual cover and subobject comma contractions; distinguish inherited Q from the larger full ambient Q-subcategory; and identify the forward classifying map, including zero normalization, with the canonical exact-inclusion K-map.

This matches the length-one proof in [Weibel, Chapter V, Proposition 3.1.1, pp. 20–21](https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.V.pdf). The general finite-resolution theorem additionally needs length-stratum iteration and union passage. That work is not supplied by the reviewed length-one theorem.

The broader geometric contract is also accurately bounded: [Stacks 066Z](https://stacks.math.columbia.edu/tag/066Z) gives object-dependent finite projective resolutions over regular noetherian rings without a uniform finite Krull-dimension assumption. The pinned mathlib source defines geometric regularity but does not provide that regularity-to-finite-projective-dimension bridge. For nonaffine vector-bundle K-theory, global resolution hypotheses matter; [Stacks 0F8A](https://stacks.math.columbia.edu/tag/0F8A) supplies the resolution property for quasi-compact regular schemes with affine diagonal. The present endpoint proves the PID affine case, not a general regular-scheme comparison.

## Verification evidence

Substantive source scope: the seven resolution modules above, `Resolution/Transport`, and `Scheme/Regular/{Field,FiniteProjectiveResolution,AffineProjective,AffineResolution,SmallComparison}`. The old `Scheme/Regular/ResolutionTransport` was checked as a compatibility-only import of the actual `Resolution/Transport` source.

- Independent focused build: `logs/regular-pid-independent-build.log` (3348 jobs, successful).
- Full exact-source-module audit: `audits/RegularPIDIndependentAudit.lean`, including generated/private declarations and explicit arbitrary-universe endpoint examples.
- Audit log: `logs/regular-pid-independent-all-axioms.log`.
- Source fingerprints: `logs/regular-pid-independent-sources.sha256`.
- The repository source-token audit passed.

Final acceptance: **passed**. The audit checks **553 declarations in 13 substantive modules**, including all 386 declarations of the seven core resolution modules, 5 declarations in actual resolution transport, and 162 declarations in the five geometric modules. All depend only on `propext`, `Classical.choice`, and `Quot.sound`. Explicit arbitrary-universe PID endpoint examples compile, including the forward-map equality by `rfl`.

Per-module counts: Resolution Finite 98; Closure 14; QCalculus 15; Covers 94; FullQ 35; InheritedQ 108; LengthOne 22; Transport 5; Regular Field 39; FiniteProjectiveResolution 15; AffineProjective 31; AffineResolution 19; SmallComparison 58.

All 14 source fingerprints (including the compatibility-only wrapper) matched after verification. Manifest SHA-256: `579679849f263b17891fef5b85f09ea13c593f5f3ff1406fa5c5d66e5c8f59ae`. No mathematical correctness blocker was found in this scope. Later source-only low-dimensional regularity modules are outside this review.

Import-path update: the compatibility-only `Scheme/Regular/ResolutionTransport`
wrapper has been removed. `AffineResolution` now imports the actual
`Quillen.Resolution.Transport` directly; its proof body is unchanged.
