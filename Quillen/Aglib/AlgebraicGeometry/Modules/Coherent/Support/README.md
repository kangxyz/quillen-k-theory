# Coherent sheaves with finite closed support

## Local candidate interfaces

Closedness of support is detected on the original finite affine local models. On a noetherian spectrum, the principal affine supported small model is an exact categorical presentation of coherent sheaves supported on the complement.

These local general-theory candidates preserve the existing declaration namespaces, hypotheses and universes. Their K-theory applications remain in downstream modules.

- [`Locality.lean`](Locality.lean)
- [`PrincipalAffineSmallModel.lean`](PrincipalAffineSmallModel.lean)
- [`FiniteClosed.lean`](FiniteClosed.lean)
- [`FiniteClosedFamilies.lean`](FiniteClosedFamilies.lean)

`FiniteClosed` works on a locally Noetherian scheme with a finite set `S` whose
points are closed. `finiteSupportEquivalence` has the original finite sum of
singleton-supported inclusions forward and is exact in both directions. Its
components use actual restriction and extension by zero; the sum of their
original counits is a stalkwise isomorphism, and explicit retracts prove
coherence. `singletonSumIso` and the exact evaluation isomorphisms preserve
the original inclusions, including arbitrary zero objects off-coordinate and
empty `S`.

`FiniteClosedFamilies.reconstructionEquivalence` identifies the canonical
finite-support family of actual singleton-supported categories with coherent
sheaves of finite support in an injective closed-point family, on a locally
Noetherian scheme. Its original coproduct reconstruction is exact in both
directions and retains singleton and evaluation equations. On a Noetherian
scheme, `finitePointSupport_iff_support_subset` identifies its predicate with
ordinary support containment in the family's range.

The intended upstream paths are
`Aglib.AlgebraicGeometry.Modules.Coherent.Support.FiniteClosed` and
`Aglib.AlgebraicGeometry.Modules.Coherent.Support.FiniteClosedFamilies`.
Their downstream consumer
[`FinitePointAssembly`](../../../../../AlgebraicGeometry/Scheme/Coherent/ClosedImmersion/FinitePointAssembly.lean)
supplies upper-small coherent support assembly from public field-scheme
G-theory in every positive degree, with the original closed pushforwards.
That K-theory adapter remains outside the general candidate subtree.

The exact coherent splitting does not prove the supported stalk quotient, its fullness, or its essential surjectivity. The downstream R5 label `J2` denotes a second-support K₁ stratum, not degree two. These are separate from the finite-support categorical equivalences above.

## Declaration locators

These additional names use the same objects, hypotheses, and original maps as the linked construction sections. They are locators within those interfaces, not stronger comparison statements.

| Declaration / module | Construction and conditions |
| --- | --- |
| `closedSupportGEquiv` | [Local candidate interfaces](#local-candidate-interfaces) |
| `Quillen.Aglib.AlgebraicGeometry.Modules.Coherent.Support.FiniteClosed` | [Local candidate interfaces](#local-candidate-interfaces) |
