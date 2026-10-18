# Compatibility and integration history

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
