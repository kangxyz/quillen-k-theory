# Compatibility and integration history

## Native Aglib adoption in 0.10.0

The current source integration pins Aglib to
`2c34f185fa859e862661f939cd216b07bcccfb26`. Replace each retired import below directly
with its native owner; no forwarding modules or compatibility aliases remain.
The links identify exact source files at that pin.

| Removed import | Native import and pinned source |
| --- | --- |
| `Quillen.Aglib.Algebra.Module.MatrixPresentation` | [`Aglib.Algebra.Module.MatrixPresentation`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Module/MatrixPresentation.lean) |
| `Quillen.Aglib.Algebra.Module.FiniteParametrix` | [`Aglib.Algebra.Module.FiniteParametrix`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Module/FiniteParametrix.lean) |
| `Quillen.Aglib.Algebra.Module.MatrixBaseChange` | [`Aglib.Algebra.Module.MatrixBaseChange`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Module/MatrixBaseChange.lean) |
| `Quillen.Aglib.Algebra.Homology.ShortComplex.ProductSequence` | [`Aglib.Algebra.Homology.ShortComplex.ProductSequence`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Homology/ShortComplex/ProductSequence.lean) |
| `Quillen.Aglib.Algebra.Homology.MappingCone.Parametrix` | [`Aglib.Algebra.Homology.MappingCone.Parametrix`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Homology/MappingCone/Parametrix.lean) |
| `Quillen.Aglib.Algebra.Homology.MappingCone.Iso` | [`Aglib.Algebra.Homology.MappingCone.Iso`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Homology/MappingCone/Iso.lean) |
| `Quillen.Aglib.Algebra.Homology.ModuleCat.FiniteParametrix` | [`Aglib.Algebra.Homology.ModuleCat.FiniteParametrix`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Homology/ModuleCat/FiniteParametrix.lean) |
| `Quillen.Aglib.Algebra.Homology.ModuleCat.LaurentProjectorCech` | [`Aglib.Algebra.Homology.ModuleCat.LaurentProjectorCech`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Homology/ModuleCat/LaurentProjectorCech.lean) |
| `Quillen.Aglib.Algebra.Homology.ModuleCat.LinearMapConeShift` | [`Aglib.Algebra.Homology.ModuleCat.LinearMapConeShift`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Homology/ModuleCat/LinearMapConeShift.lean) |
| `Quillen.Aglib.Algebra.Homology.ModuleCat.LaurentModuleCech` | [`Aglib.Algebra.Homology.ModuleCat.LaurentModuleCech`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Homology/ModuleCat/LaurentModuleCech.lean) |
| `Quillen.Aglib.Algebra.Homology.ModuleCat.LinearMapConeIso` | [`Aglib.Algebra.Homology.ModuleCat.LinearMapConeIso`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Homology/ModuleCat/LinearMapConeIso.lean) |
| `Quillen.Aglib.Algebra.Polynomial.Laurent.MatrixProjector` | [`Aglib.Algebra.Polynomial.Laurent.MatrixProjector`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Polynomial/Laurent/MatrixProjector.lean) |
| `Quillen.Aglib.Algebra.Polynomial.Laurent.MatrixCech` | [`Aglib.Algebra.Polynomial.Laurent.MatrixCech`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Polynomial/Laurent/MatrixCech.lean) |
| `Quillen.Aglib.Algebra.Polynomial.Laurent.MatrixCutoff` | [`Aglib.Algebra.Polynomial.Laurent.MatrixCutoff`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Polynomial/Laurent/MatrixCutoff.lean) |
| `Quillen.Aglib.Algebra.Polynomial.Laurent.ProjectorCech` | [`Aglib.Algebra.Polynomial.Laurent.ProjectorCech`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Polynomial/Laurent/ProjectorCech.lean) |
| `Quillen.Aglib.Algebra.Polynomial.Laurent.ProjectorFiniteDefects` | [`Aglib.Algebra.Polynomial.Laurent.ProjectorFiniteDefects`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Polynomial/Laurent/ProjectorFiniteDefects.lean) |
| `Quillen.Aglib.Algebra.Polynomial.Laurent.Cutoff` | [`Aglib.Algebra.Polynomial.Laurent.Cutoff`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Polynomial/Laurent/Cutoff.lean) |
| `Quillen.Aglib.Algebra.Polynomial.Laurent.ModuleCech` | [`Aglib.Algebra.Polynomial.Laurent.ModuleCech`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Polynomial/Laurent/ModuleCech.lean) |
| `Quillen.Aglib.Algebra.Category.ModuleCat.FiniteMatrixBaseChange` | [`Aglib.Algebra.Category.ModuleCat.FiniteMatrixBaseChange`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Category/ModuleCat/FiniteMatrixBaseChange.lean) |

Transferred declarations use these native namespaces: `Quillen.Module` becomes
`Module`, `Quillen.ModuleComplex` becomes `ModuleCat`, and
`Quillen.LaurentCutoff` becomes `LaurentPolynomial.Cutoff`. Projector
declarations from `Quillen.LaurentProjector` become
`LaurentPolynomial.Projector`, except the declarations in the two
`ModuleCech`/`LaurentModuleCech` leaves, which become `ModuleCat.LaurentCech`.
The retained local homological `LaurentCech` extension also uses
`LaurentPolynomial.Cutoff`. Other local module and module-complex extensions
retain their existing namespaces; do not apply these replacements globally.

The upstream shift instances are
`CategoryTheory.NatTrans.mapCochainComplexPlus_commShift` and
`CategoryTheory.Functor.mapCochainComplexPlusCompIso_commShift`. Use
`FGModuleCat.linearAutToFGAut` in place of `FGModuleCat.linearAutToAut`.
The affine `AlgebraicGeometry.Scheme.PolynomialLaurent.polynomialZero` and its
projection lemmas become `polynomialZeroSection` and its projection lemmas;
the arbitrary-scheme `AlgebraicGeometry.Scheme.Bass` zero sections remain local.

Eight local same-path extensions remain, as described in the
[candidate guide](../Quillen/Aglib/README.md#extensions-of-native-leaves).
In particular, local matrix automorphisms retain the commutative-ring
hypothesis, the generic cokernel-pushout theorem retains `HasZeroMorphisms`,
and locally-perfect restriction remains distinct from native strict-perfect
restriction. Pi exactness helpers, the Plus quasi-isomorphism shift instance,
regular-local proofs and arbitrary-scheme Bass zero sections retain their
additional local interfaces. This entry records source/API correspondence;
compilation and native final checks are reported separately.

## Tensor construction checkpoint and terminal-chart aliases

The 2026-10-21 integration adds the tensor-generated construction, generic
weak-zero/grid interfaces and their tests. The incoming recovery package is
labelled 0.10.0; its archived raw-route modules were never enrolled in the
accepted `25387c65` library. The [archive guide](RESEARCH_ARCHIVE.md) records
that source boundary and the recovery layout.

`MWholeNerveTerminalChartComparisonClients` keeps its public import path and
all ten `client_terminal_chart_comparison_*` names as deprecated aliases.
New clients use `Quillen.PerfectComplexes.BassMWholeNerve.terminal_chart_comparison_*`
from `MWholeNerveTerminalChartComparison` directly. The original wrapper body
is preserved as a compatibility snapshot, with the same hypotheses and coordinates.

Historical imports and integration records live here; current mathematical
statements, hypotheses and interfaces remain at the linked source owners.
These notes introduce no new API break or release tag.

## Historical import owners

The earlier 0.5.0 refactor placed shared foundations below applications. Retired
imports are replaced directly, without duplicate implementations or legacy facades.

| Previous import | Current import | Current interface guide |
| --- | --- | --- |
| `Quillen.GTheory.FiniteModules.Basic` | `Aglib.Algebra.Category.ModuleCat.Finite` | [Source guide](../Quillen/GTheory/FiniteModules/README.md) |
| `Quillen.AlgebraicGeometry.Scheme.Regular.FiniteProjectiveResolution` | `Quillen.Aglib.Algebra.Homology.ModuleCat.FiniteProjectiveResolution` | [Source guide](../Quillen/Aglib/Algebra/Homology/ModuleCat/README.md) |
| `Quillen.AlgebraicGeometry.Scheme.Regular.LocalPrincipalDomain` | `Quillen.Aglib.RingTheory.RegularLocalRing.PrincipalDomain` | [Source guide](../Quillen/Aglib/RingTheory/RegularLocalRing/README.md) |
| `Quillen.Waldhausen.QuillenComparison.SpanNaturality` | `Quillen.CategoryTheory.QConstruction.SpanIsoNaturality` | [Source guide](../Quillen/CategoryTheory/QConstruction/README.md) |

The shared Q-span law is `CategoryTheory.ExactCategory.ExactStructure.qSpan_iso_naturality`.
The earlier relocations retained objects, maps, hypotheses and comparison boundaries.

## Standard comparison integration

The 0.7.0 integration adopted the standard comparison while retaining the
Q-construction, K-groups, exact-functor maps, grades and loop-degree shifts.
The comparison map and prescribed track changed. The
[current source guide](../Quillen/KTheory/Plus/StandardComparison.md) owns its
actual maps, formulas, component labels and naturality boundary.

The integration record described source integration rather than a published
tag, and recorded Lean 4.34.1 with unchanged dependency pins. Current setup and
pins remain under [CONTRIBUTING](../CONTRIBUTING.md#dependency-updates).

## Standard comparison client upgrades

Use `Quillen.KTheory.Plus` for the standard comparison and its exact equivalences,
naturality homotopies, positive comparisons and component labels. Replace a
definitional equality to the generic loop/fiber inverse with
`completionToOriginalQLoops_eq_reversal_fiberInverse`. When selecting a stage
for a K0 class, use that class with the standard stage label and remove the
former inversion compensation. Current client links remain in the source guide.

## Local Aglib candidates in 0.9.0

The 0.9.0 integration staged general algebraic geometry and its algebraic,
categorical and homological prerequisites under `Quillen.Aglib`. It reorganized
implementation ownership and split mixed sources, preserving native declaration
namespaces and chosen comparison maps. Application imports kept their Quillen
owners and consumed the lower candidate leaves. Q/K/G/S, Waldhausen, spectra
and specialized projective-line applications remained outside the general
candidate layer. No duplicate implementation or default forwarding module was
retained for moved source.

Current prefix/interface meaning is in the [candidate guide](../Quillen/Aglib/README.md);
authoring and admission follow [development policy](DEVELOPMENT.md#aglib-candidates).
