# Independent review: arbitrary global closed-support dévissage

Reviewed 2026-10-09 independently of the proof author. This extends the previously accepted arbitrary-ideal affine endpoint and actual open-localization/pushforward foundations.

## Mathematical contract

For an actual closed immersion i : Z → X with X noetherian, let j be the actual open complement of its image. The endpoint identifies genuine scheme G_n(Z) with the public supported coherent G_n(j) for every natural n, with the original geometric pushforward as the forward map after inclusion. It supplies the connective closed–open G-theory sequence and the surjective G₀ tail.

The core coherent category signatures expose local noetherianity of Z; the new NoetherianSource module derives it, and full noetherianity of Z, from the ambient hypotheses. There is no extra affine, principal-ideal, finite-resolution, regularity, or global-generation assumption. This is the dévissage/localization pattern of [Weibel, The K-book, Chapter V, Exercise 4.3 and Example 6.11](https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.V.pdf).

## Source review

The frozen list is `docs/GLOBAL_CLOSED_DEVISSAGE_SOURCES.txt`: 29 modules, 3,222 lines. Eighteen new modules were reviewed for this extension. All eleven shared modules in the prior affine independent fingerprint list are byte-identical to that accepted version. FiltrationFunctor was also reinspected alongside the new filtration transport.

1. Actual coherent pushforward is the ordinary module-sheaf pushforward restricted to the coherent full subcategory. Affine quotient presentations and actual open base change establish coherence and exactness. The G-map is its original canonical smallKMap.
2. Actual coherent pullback comes from the genuine scheme-module pullback. The affine extension-of-scalars comparison is obtained by uniqueness of the actual left adjoint. Coherence is proved on the pulled-back affine cover; no exactness of arbitrary closed pullback is claimed.
3. The unit-compatible open square is not chosen arbitrarily. It is constructed by two mates of the real direct-image composition square. The proof identifies the restricted global unit with the actual local unit and hence identifies their genuine kernels.
4. On affine quotient charts the closed pushforward image is proved to be exactly the ideal-annihilated objects. Quotient closure makes the actual adjunction unit epic. Affine detection gives global epimorphic units; the triangle identities and faithfulness then give actual full faithfulness. Subobject, quotient and finite-product closure are derived. GeneralAnnihilator independently characterizes the global image on genuine quotient charts and retains actual pushforward after forgetting the property.
5. The ordinary quotient M → M/IM factors through the actual unit by adjunction. Thus the unit kernel maps into IM. Exactness plus annihilation of the target prove the stronger equality of its range with IM. The annihilator exponent drops at each actual kernel step.
6. Actual supportedness supplies an annihilating ideal power on each affine chart. A finite affine subcover gives a maximum of the sheaf-specific exponents. Kernel iteration is proved compatible with open restriction and remains zero beyond a terminating stage. Stalk detection then proves global termination. The bound is not assumed or uniform over all coherent objects.
7. Unwinding the epimorphic unit kernels constructs genuine short exact filtration stages with killed-image factors. The filtration lifts into the actual supported abelian category using subquotient closure and then transports through its compatible small-model equivalence, preserving the real maps and final object.
8. Actual closed pushforward is an exact equivalence only onto the killed-image subcategory. Homotopical dévissage then compares that smaller subcategory with all supported objects. There is no asserted categorical equivalence from Coh(Z) to all supported sheaves.
9. The two supported G comparisons retain the existing upper-universe scheme G groups. The equalities closedSupportGEquiv_pushforward and closedSupportedGEquiv_pushforward identify the composite with the exact original pushforward map, including the standard-exact-structure and chosen-zero normalizations.
10. The boundary is the existing support-localization boundary followed by the inverse of the proved dévissage equivalence. All three recurring image–kernel identities are transported through those actual group equivalences. The original restriction map and its surjective degree-zero tail are preserved.

No semantic correctness blocker was found. The finite filtration, nilpotence, annihilator characterization, exactness, and equivalence conclusions are proved from the geometric inputs. They are not stored as theorem-shaped assumption fields.

## Verified endpoint scope

- Actual equivalence of Coh(Z) with the independently characterized ideal-annihilated coherent objects.
- Canonical all-nonnegative-degree G(Z)-to-supported-G equivalence.
- All three exactness positions for actual i_* and j*, including the full G₁/G₀ tail and surjective G₀(X) → G₀(U).

This does not prove a regular K-to-G comparison, perfect-complex localization, a nonconnective spectrum, or a cross-universe raw-realization identification. It does not add a new assertion of an ordinary global homotopy inverse for the existing localization fiber comparison. Public facade integration and archived-source verification are separate coordinator-owned steps.

## Verification and fingerprints

The independent current-source command `lake --rehash build Quillen.Scheme.Coherent.ClosedImmersion.GeneralLocalization Quillen.Scheme.Coherent.ClosedImmersion.IdealLocalization` passed with 3,694 jobs on Lean 4.34.0 and the pinned mathlib revision. Only style/linter warnings appeared. Evidence: `logs/global-closed-independent-build.log`.

Every source matches `logs/global-closed-20261009/sources.sha256`; that manifest has SHA-256 `b93bab4c3a35e56ebb885c105bf775d298b35c8d05c021d933d3823008e90a2f`. The final GeneralLocalization source additionally imports GeneralAnnihilator, AffineIdealKernel, and NoetherianSource; these import-only endpoint changes are included in the frozen hash. This reviewer changed no active proof source or import.

The independent post-build execution of `audits/GlobalClosedDevissageAudit.lean` passed all 696 declarations, including private/generated helpers, in all 29 required exact source modules, with only propext, Classical.choice, and Quot.sound. Evidence: `logs/global-closed-independent-all-axioms.log`. All 29 final frozen-source hash checks passed and are recorded in `logs/global-closed-independent-hash-check.log`.

Independent source, contract, current-source build, and transitive-assumption review are accepted for the arbitrary global closed-support dévissage and canonical connective G-localization endpoint. No active proof sources, public facades, or scripts were changed by this reviewer.
