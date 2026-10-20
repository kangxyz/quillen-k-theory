# Genuine polynomial-chart transport

The `GlobalRawBassChartRelativeTransport*` family provides continuous whole-carrier
posttransport for the positive and inverse polynomial charts. Its input is an
arbitrary model `V`, a genuine polynomial reference `P`, a Laurent reference `G`,
and an actual isomorphism from `G` to `P ≫ chart(Y)`. It does not require a base
reference or a factorization through the polynomial projection.

## Actual references and whole transport

For a scheme arrow `a : X ⟶ Y`, the target polynomial reference is
`P ≫ polynomialArrow(a)`. The target Laurent reference is `P` followed by the
original five-node chart-square source. The target attachment uses the original
chart node indexed by `4`, whiskered by `P`; the Laurent postcomposition anchor uses the
original chart node indexed by `2` and the inverse of the given attachment isomorphism.
All dependent reference isomorphisms are retained.

`ChartRelativeTransport.transport` descends both original scalar pushouts. Its
comparison stage uses the original five-node chart path, followed by the full
original cylinder-height stage with the unchanged half split. Both tips remain
distinct. Laurent inclusion, both cylinder maps and both tips have exact formulas.

`transport_native` recovers the actual chart-cone map at every scalar point,
native level and source input. `plus_raw_native` and `minus_raw_native` then use
the original chart inclusions to recover `GlobalRawBass.coneMap`, not a replacement
cone map or an equality inferred from injectivity of native evaluation.

## The selected polynomial correction

`postCorrectedSquare` transports the existing selected polynomial composition
square. `plus_postCorrectedSquare_native` and `minus_postCorrectedSquare_native`
recover the original raw postmap applied to `InputComposition.coneHomotopy` on
every genuine positive or inverse polynomial-cylinder input. Composition time,
cone height and native input stay independent, and every selected correction
interior is preserved. The whole surface is continuous in the scalar carrier;
the existing compact native-family API supplies joint native continuity, based
points and independent structure time.

For source precomposition, reuse the unrestricted model-level
`CommonReferenceNerve.CutOpenPrecomp.map` and `map_native`. Their target references
are the actual precomposed polynomial and Laurent references, with left-whiskered
attachment isomorphisms and the explicit associator. No new pretransport
framework or projection factorization is needed.

This producer is separate from base-reference scalar-cone posttransport. It does
not supply the compatible projection-pasting higher fillers, a completed raw R2,
a same-convention second-stage producer, or the uniform successor theorem.
