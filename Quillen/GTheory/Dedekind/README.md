# Dedekind residue support and localization

## Imports

| Import | Interface |
| --- | --- |
| `Quillen.GTheory.Dedekind.ResidueFieldAssembly` | Native positive-degree residue-field G-assembly into actual torsion support, with original pushforwards |
| `Quillen.GTheory.Dedekind.Localization` | Original native residue-coordinate kernel intersections and finite-family lifting under explicit generic-G1 injectivity |
| `Quillen.GTheory.Dedekind.FiniteResidueLocalization` | Finite actual height-one residue fields annihilate primary/support G2 and make original native localization and literal public generic G2 pullback injective, retaining supplied fraction fields; no generic-G1 premise |
| `Quillen.GTheory.Dedekind.LocalDvrBoundaryNaturality` | Original local-DVR boundary after actual generic extension equals global residue coordinates for G(n+2) → G(n+1); kernel intersections and finite-family lifting under original generic-G1 injectivity |
| `Quillen.GTheory.Dedekind.PrincipalDvrBoundaryComparison` | Actual principal scheme boundary equals the native local-DVR boundary, retaining the given fraction field and original closed/generic maps |

## Native Dedekind residue support

Import
[`Quillen.GTheory.Dedekind.ResidueFieldAssembly`](ResidueFieldAssembly.lean).
For a commutative Dedekind domain `R`,
`Quillen.DedekindResidue.residueFieldAssemblyKEquiv R n` identifies

```text
directSum_p Additive (G(p.asIdeal.ResidueField, n+1))
  ≃+ Additive (SupportedG(R⁰, n+1)).
```

The target is exactly the native torsion-support term of finite-module
localization. Primary decomposition, actual ideal-power filtrations and
quotient-ring dévissage prove the equivalence. The canonical algebra map
`R/p → p.asIdeal.ResidueField` supplies the original scalar-restriction
comparison. `residueFieldAssemblyKEquiv_of` and its finite-sum formula retain
the original support pushforwards. `supportedKMap_comp_residueFieldAssembly`
retains the sum of original R-restrictions into ambient G-theory. No
residue-field finiteness assumption is needed. K1 and K2 specializations are
explicit; the source is finite-module G-theory in the same native universe.

[`Dedekind.Localization`](Localization.lean)
detects the positive generic image by all native residue coordinates. Under
the explicit premise that the original generic G1 map is injective, every
finite residue-G1 family is the boundary of one generic G2 class, retaining
both the raw boundary-to-assembly equation and every coordinate.
[`LocalDvrBoundaryNaturality`](LocalDvrBoundaryNaturality.lean)
identifies the original local-DVR boundary after actual generic tensor
extension with each global residue coordinate in degrees
`G(n+2) → G(n+1)`. Its kernel-intersection theorem and finite-family lift
retain these actual local boundaries and the original generic-G1-injectivity
premise.

## Classical source locator

[Chapter V](https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.V.pdf), 6.6--6.7.3,
locates the Dedekind localization tail and specialization. Source conventions
must be compared with the library's actual maps before transporting signs.
