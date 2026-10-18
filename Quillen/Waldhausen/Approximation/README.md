# Approximation interfaces

## Imports

| Import | Interface |
| --- | --- |
| `Quillen.Waldhausen.Approximation.Basic` | Generic approximation property |

## Approximation and structural cylinder data

An approximation witness `h` for
[`HasApproximationProperty W V F`](Basic.lean)
contains App1, reflection of weak equivalences, and the cofibration version of App2:
each `f : F.obj X ⟶ Y` factors as `F.map i ≫ p`, with `i : X ⟶ X'` a source
cofibration and `p : F.obj X' ⟶ Y` a target weak equivalence. Exactness is separate.

`HasApproximationProperty.KEquivGeneral h hF J n` requires
`[V.weq.HasTwoOutOfThreeProperty]` and
`J : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl W)`.
The original `deloopingMap hF` is then a weak homotopy equivalence and the original
`KMap hF n` is bijective in every degree, including zero, and is the forward map.

[`JointData`](../Fibration/Rows/JointFactorization.lean)
contains an exact arrow-to-extension functor, natural source and target injections
presenting a coproduct, and a coarse-weak projection factoring the original arrow.
This cylinder data is not inferred from Waldhausen axioms or App1/App2.
Approximation does not require the additional section identity below.
