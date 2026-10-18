# Integral bar homology candidates

These four modules extend the pinned Mathlib low-degree group-homology complex.
Their intended Aglib paths replace `Quillen.Aglib` by `Aglib`; their mathematical
namespace is `groupHomology.IntegralBar`.

| Module | Interface and exact hypotheses | Current consumers |
| --- | --- | --- |
| `IntegralBar` | Trivial coefficients over a commutative ring `k` and a group `G` in the stated common universe; perfectness of `G` for the chosen fillers, cocycle and bar extension. Restriction from `ULift ℤ` to integral modules and its homology/cycle comparison use an arbitrary group. | `PerfectBarExtension`, `Torus`, `Quillen.Topology.LocalCoefficients.SingularBar`, `Quillen.Algebra.Group.StableSteinbergSchur` |
| `PerfectBarExtension` | A perfect group and commutative coefficient ring for the linear filler construction `W d₂ - id`, which is negative identity on cycles; the extension-perfectness theorem uses lifted integral coefficients and a perfect group. | `CentralBarLifts` |
| `CentralBarLifts` | Descent of a bar-two-chain linear map that kills original three-boundaries; normalized sections and evaluations for a surjective group homomorphism with central kernel. The bar-extension lifting results retain the stated perfectness hypothesis. | `Quillen.Algebra.Group.StableSteinbergSchur` |
| `Torus` | The original `[g|h] - [h|g]` cycle for commuting elements over a commutative ring; the cocycle and bar-extension commutator statements retain perfectness. Simultaneous inversion is calibrated by an explicit three-chain over `ULift ℤ` for any group. | `Quillen.Algebra.Group.StableSteinbergSchur`, `Quillen.Topology.LocalCoefficients.SingularBarCalibration` |

The original bar differential, cycle quotient, central extension and signs remain
unchanged. The generic dependency closure contains only Mathlib and these general
candidates. The pinned Mathlib/Aglib source search found no existing declarations
named `barCocycle`, `cycleRetraction`, `BarExtension`, or `integerBarH2Iso` in the
searched owners; the actual low-degree and scalar-restriction interfaces are reused.
This records a candidate implementation and does not assert upstream acceptance.
