# Arbitrary affine closed-subscheme dévissage

Verified 2026-10-09. This extends the principal endpoint to every ideal I of a commutative noetherian ring R.

## Completed endpoint

Import `Quillen.Scheme.Coherent.ClosedImmersion.IdealLocalization`.
Namespace `Quillen.CoherentScheme.ClosedImmersion.Ideal`.

- `closedMap R I`: genuine `Spec(R/I) → Spec R` closed immersion.
- `openMap R I`: inclusion of the actual open complement of `V(I)`.
- `coherentPushforwardExact`: restriction of the actual sheaf pushforward.
- `coherentClosedEquivalence`: equivalence onto precisely I-annihilated coherent objects.
- `coherentSupportedAway_iff_pow_le_annihilator`: actual support iff a single I-power annihilates all finite global sections.
- `supportFiltrationHypothesis`: genuine finite image filtrations, refined by actual pullbacks, whose factors are I-annihilated.
- `closedSupportedGEquiv`: public upper-universe G(Spec(R/I)) isomorphic to actual supported G(Spec R).
- `closedSupportGEquiv_pushforward` and `closedSupportedGEquiv_pushforward`: the equivalences preserve the original canonical exact-functor smallKMap of actual i_*.
- `affine_closed_open_longExact`: all three exactness positions in every degree, plus surjectivity at G₀ of the open complement.
- `affine_closed_open_GZero_tail`: the actual homotopical G₁/G₀ tail.

No equivalence with the entire supported abelian category is asserted. Support only gives I-power annihilation, and the passage to K-groups is genuine dévissage.

## Literal ideal-power filtration

Import `Quillen.Scheme.Coherent.ClosedImmersion.IdealPowerFiltration`.
The finite-module `idealPowerFiltration` uses actual submodules `I M`, actual quotients `M/I M`, and actual short exact sequences. The exponent decreases at each step. `coherentIdealPowerFiltration` carries this tower through the proved affine module/sheaf equivalence and ends at the original coherent sheaf, using the actual unit isomorphism.

The K-theory endpoint uses a second, independently constructed generator-image refinement. Both produce the same necessary class of I-annihilated factors; no independence-of-filtration axiom or conclusion-shaped hypothesis is introduced.

## Additional global infrastructure

`AffinePullback`, `GeneralPushforward`, and `GeneralPullback` establish genuine affine scalar-extension comparison and actual coherent pullback/pushforward along arbitrary closed immersions. The general pushforward is exact, and its canonical global G-map has the actual open-base-change square. The coherent adjunction's unit/counit are identified with the sheaf adjunction after forgetting coherence.

The general nonaffine endpoint is now completed in `GeneralLocalization`: actual unit/kernel base change, ideal-power exponent reduction, finite-cover nilpotence, the precise annihilator equivalence, and all canonical exactness positions. See `docs/GLOBAL_CLOSED_DEVISSAGE.md` for its proof and verification scope.

## Verification

```
lake build Quillen.Scheme.Coherent.ClosedImmersion.IdealLocalization \
  Quillen.Scheme.Coherent.ClosedImmersion.IdealPowerFiltration
lake env lean audits/IdealClosedDevissageAudit.lean
```

The initial endpoint build passed 3,673 jobs; the literal coherent ideal-power filtration build passed 3,132 jobs. The named mathematical endpoint audits show only `propext`, `Classical.choice`, and `Quot.sound`. No existing frozen source was edited.
