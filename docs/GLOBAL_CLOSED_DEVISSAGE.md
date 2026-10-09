# General closed-subscheme dévissage and geometric G-localization

Completed geometric endpoint, 2026-10-09.

## Mathematical statement

Let X be a noetherian scheme and i : Z → X a closed immersion. Let j be the inclusion of the actual open complement of the image of i. The formal endpoint is the canonical isomorphism

G_n(Z) ≃ SupportedG_n(j)

induced by actual coherent sheaf pushforward. Its composite with the actual supported inclusion is exactly the original canonical smallKMap of i_*.

The full connective sequence has, for each natural n, all three exactness identities:

1. range(i_* : G_n(Z) → G_n(X)) = ker(j* : G_n(X) → G_n(U)).
2. range(j* : G_(n+1)(X) → G_(n+1)(U)) = ker(boundary_n).
3. range(boundary_n) = ker(i_* : G_n(Z) → G_n(X)).

The G₀ restriction is surjective, giving the complete actual homotopical G₁/G₀ tail.

## Canonical implementation

Import `Quillen.Scheme.Coherent.ClosedImmersion.GeneralLocalization`.
The namespace is `Quillen.CoherentScheme.ClosedImmersion.General`.

- `openComplement`, `openMap`: actual complement and inclusion.
- `coherentPushforwardExact`, `coherentPushforwardGMap`: actual i_* and its original canonical smallKMap.
- `coherentPullback`, `coherentAdjunction`: actual coherent pullback and the genuine restricted sheaf adjunction.
- `coherentAnnihilatorEquivalence`: actual i_* is an equivalence onto precisely the ideal-annihilated coherent sheaves, characterized independently on every genuine affine quotient chart.
- `coherentAnnihilatorEquivalence_comp_inclusion`: forgetting the annihilator proof gives precisely actual i_*.
- `closedSupportedGEquiv`: actual closed-scheme G is isomorphic to the public supported G-term.
- `closedSupportGEquiv_pushforward`, `closedSupportedGEquiv_pushforward`: exact original-map identification, including upper-universe small-model and basepoint choices.
- `closedConnectingHom`: support boundary followed by the inverse of the proved dévissage equivalence.
- `closed_open_longExact`, `closed_open_GZero_tail`: the complete connective exactness package.

The core category signatures accept local noetherianity of Z to form Coh(Z). This is derived from the geometric hypotheses: `closedSource_isLocallyNoetherian i` and `closedSource_isNoetherian i` prove the source is respectively locally noetherian and noetherian from the corresponding ambient hypotheses. It is no extra geometric restriction.

## The geometric proof is discharged

1. Actual affine pushforward is restriction of scalars. Closed affine quotient presentations and actual open base change prove global coherence and exactness of i_*.
2. Actual affine pullback is extension of scalars, by uniqueness of the genuine left adjoints. An actual pulled-back affine cover proves coherent pullback globally.
3. Two successive mates of the actual pushforward composition square give the canonical unit-compatible open base-change square. This identifies the actual unit kernels after open restriction.
4. The affine direct-image essential image is exactly annihilation by the actual quotient ideal. Its quotient closure makes the actual unit epimorphic. The global unit is epic by affine detection; the actual pushforward is consequently fully faithful. Its image contains zero and is closed under subobjects, quotients, and finite products.
5. The ordinary quotient map M → M/IM factors through the genuine unit by adjunction. Exactness and annihilation of the target prove `kernelUnit_range_eq_idealProduct`: the actual unit kernel has image exactly IM on finite global sections.
6. Genuine support gives a uniform annihilating I-power on each finite affine module. Each actual kernel step lowers the exponent. A finite actual affine subcover and the maximum of its object-specific bounds prove `kernelIterate_eventually_zero` globally.
7. The epimorphic unit therefore supplies actual short exact filtration stages, with annihilated factors. The filtration lifts into the real supported abelian category and transports through its compatible small presentation. The proved homotopical dévissage theorem applies to this constructed filtration.

No filtration, nilpotence, extension, or quotient-equivalence conclusion is inserted as a hypothesis. The ideal-annihilated category is distinct from the full supported category; their K-equivalence is genuine dévissage.

## Scope and verification

All public groups use the existing genuine upper-universe scheme G-theory (`u+1`) and the original smallKMap constructions. Degrees include actual homotopical degree zero. No cross-universe realization identification is introduced.

The 29 source modules are listed in `docs/GLOBAL_CLOSED_DEVISSAGE_SOURCES.txt`. Their frozen hashes are in `logs/global-closed-20261009/sources.sha256`.

Verification entry points:

```
lake build Quillen.Scheme.Coherent.ClosedImmersion.GeneralLocalization
lake env lean audits/GlobalClosedDevissageAudit.lean
python3 scripts/check_placeholders.py
```

The new geometric and categorical modules were checked serially with Lean 4.34.0, preserving the existing source bodies. The module-origin audit passed all 696 declarations in the 29 exact source modules, including private/generated declarations and all reflector, kernel-iteration, and filtration helpers; every dependency uses only `propext`, `Classical.choice`, and `Quot.sound`. The placeholder scan and frozen-source hash recheck also passed. Full evidence is under `logs/global-closed-20261009/`.
