# Laurent quotients and finite Bass signs

The sign computations compare actual Laurent representatives, geometric
variable permutations and loop-coordinate words. Their inputs and degree
casts matter: exchanging two abstract cokernel presentations does not compute
the action of the original geometric double-cone permutation. The
[Bass guide](README.md) fixes the contraction and telescope conventions;
[geometric connecting maps](../../AlgebraicGeometry/PerfectComplexes/BoundedFlat/GeometricBoundary.md)
owns their perfect-complex boundary applications.

## Ordered double quotient and geometric swap

For a functor `F : D ⥤ AddCommGrpCat`, [TwoChartDoubleDescent](TwoChartDoubleDescent.lean)
retains the two original `contractionπ` projections in a fixed order. Their
composite is epimorphic. A map from the double Laurent group descends through
these projections when its two inner and two outer polynomial-chart
composites vanish. Coefficient maps and natural transformations preserve this
projection; the source category and `F` need no additivity hypothesis.

[SchemeDoubleContractionSwap](SchemeDoubleContractionSwap.lean) applies the
four chart equations to the actual independent Laurent-factor swap on
quasi-compact schemes. The resulting `doubleContractionSwapNatIso` is a
natural involution. Its representative equation `doubleContractionπ_swap`
keeps the literal geometric swap and both original quotient maps. The
involution's construction alone does not identify it with minus the identity.

[SchemeDoubleContractionBraid](SchemeDoubleContractionBraid.lean) descends the
three-factor braid through the original triple quotient.
[SchemeContractionBlockSwap](SchemeContractionBlockSwap.lean) keeps the
four-factor word and its adjacent-swap conjugacy on the fourfold quotient.
One-step sign propagation uses the sign at the single Laurent object;
two-step propagation uses it at the double Laurent object. These are
pointwise hypotheses, rather than a premise that a positive-Bass
transformation is invertible on every quasi-compact scheme.

## Double-Laurent representatives and degree minus two

[ConnectiveConeQuotient](../../Topology/Prespectrum/ConnectiveConeQuotient.lean)
keeps the actual point-cofibration and zero-offset connectivity assumptions
through unlooped spans and cones. The original cone inclusion is epimorphic
on stable H₀ and kills both chart maps.
[ModelDoubleLaurentQuotient](ModelDoubleLaurentQuotient.lean) discharges these
assumptions for an actual Model-valued scheme diagram and its first cone.
The literal double-Laurent inclusion is therefore epimorphic on H₀, with
all four polynomial-chart relations zero.

[ModelDoubleLaurentSign](ModelDoubleLaurentSign.lean) descends this precise
representative. If the independently defined `doubleContractionSwap` acts
by minus the identity, the actual geometric double-cone permutation acts
by minus the identity on H₀.
[ModelDoubleCorrection](ModelDoubleCorrection.lean) combines that result with
[SchemeConjugationSignedShift](SchemeConjugationSignedShift.lean). The
double-loop reversal contributes a second minus; the original finite
correction thus acts identically in degree `-2`. Both parameter shifts and
the complete `wordAt 2` transports occur in the theorem.

The ambient and supported applications in
[ParameterDoubleCorrection](../../AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterDoubleCorrection.lean)
conjugate this identity by their original finite negative-class comparison.
This conditional interface still requires the actual parameter-row H₀
quotient-swap sign. It neither infers a supported identity from an ambient
forgetful map nor supplies an all-index correction theorem by itself.

## Laurent words in every finite degree

[GeometricConeLaurentWordRepresentative](GeometricConeLaurentWordRepresentative.lean)
defines the literal inclusions

```text
J₀ = id,
Jₙ₊₁(X) = Jₙ(LX) ≫ j_(CⁿF)(X).
```

Here `L` is the original Laurent parameter functor and `C` the unlooped Bass
cone. Naturality and the `betaAt`/`wordAt` representative squares retain the
original `power_obj` transports.
[ModelLaurentWordQuotient](ModelLaurentWordQuotient.lean) proves H₀(`Jₙ`)
epimorphic for a zero-growth diagram.

[ModelConeZeroQuotient](ModelConeZeroQuotient.lean) constructs the natural
epimorphism from the two-chart contraction of H₀(`F`) to H₀(`CF`) by the
original chart descent. [TwoChartMapEpi](TwoChartMapEpi.lean) needs only the
Laurent component of an input transformation to be epimorphic.
[ConeZeroSign](ConeZeroSign.lean) then propagates the quotient minus sign
from `F` at `LX` to `CF` at `X`, using the actual quotient braid and swap
naturality. Its scalar-action transport is for actual endomorphisms; it does
not assume additivity of the cone functor.

[GeometricConeWordStableSign](GeometricConeWordStableSign.lean) computes the
insertion and accumulated word actions as `(-1)^n` and
`(-1)^(n.choose 2)`. The hypotheses are pointwise on a supplied Laurent-closed
family of quasi-compact parameters. The conclusion retains both original
`wordAt` equality casts.
[SchemeConjugationAllSign](SchemeConjugationAllSign.lean) transports the
accumulated scalar through the genuine parameter shifts. The literal loop
reversal has the same scalar, so their product acts identically in degree
`-n`. The generic result still requires the actual Model-row quotient-swap
sign on that family.

## Original ambient and supported negative classes

[ParameterCurrentNegativeCorrection](../../AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterCurrentNegativeCorrection.lean)
defines `negativeClassCorrection` using the unchanged finite-bottom
comparison and its inverse. Its correction square compares the independently
defined current class with the original fine class.
[ParameterNegativeSign](../../AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterNegativeSign.lean)
specializes the geometric-word and loop-reversal scalars to degree `-n`.

The application inputs are discharged separately in
[ParameterAmbientNegativeSign](../../AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAmbientNegativeSign.lean)
and [SupportedParameterNegativeSign](../../AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedParameterNegativeSign.lean).
Both expose `negativeClassCorrection_hom` and
`currentNegativeKComparison_fine` for every natural index. The ambient
statement assumes a compact quasi-separated parameter scheme. The supported
statement assumes the original open immersion, compact source and target,
and quasi-separated target. The supported proof uses its own two-unit
operations and coefficient/Spec transports.

These class squares identify the unchanged current and fine negative
comparisons. Their boundary consequences, the first boundary from K₀, and
the normalized basic and auxiliary rows are in
[geometric connecting maps](../../AlgebraicGeometry/PerfectComplexes/BoundedFlat/GeometricBoundary.md#original-negative-classes-and-boundaries).
Comparison with a separately prescribed raw geometric all-stage tower
remains distinct from these class formulas. The direct tensor/Bass realization
and original TT 7.4 localization theorem are recorded in
[row interfaces](RowInterfaces.md#returned-tensor-action-and-the-forward-operation).
