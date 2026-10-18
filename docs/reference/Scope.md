# Mathematical scope summary

This cross-family summary links the authoritative statements, exact premises
and open comparisons in the source guides. It does not replace those boundaries.

| Family | Coverage and boundary route |
| --- | --- |
| ExactCategories | [Q-construction](../../Quillen/CategoryTheory/QConstruction/README.md), [canonical K-theory](../../Quillen/KTheory/README.md), [K0 comparison](../../Quillen/KTheory/GrothendieckComparison/README.md) |
| Waldhausen | [Waldhausen theory](../../Quillen/Waldhausen/README.md) |
| Localization | [dévissage](../../Quillen/Devissage/README.md), [resolution](../../Quillen/Resolution/README.md), [Serre localization](../../Quillen/Localization/Serre/README.md), [finite-module G-theory](../../Quillen/GTheory/FiniteModules/README.md) |
| LowDegreeFieldSupport | [field comparisons](../../Quillen/KTheory/Field/README.md), [finite support](../../Quillen/KTheory/FiniteSupport/README.md), [Dedekind support](../../Quillen/GTheory/Dedekind/README.md), [scalar actions and normalization](../../Quillen/KTheory/LowDegreeScalarAction/README.md), [DVR generation](../../Quillen/GTheory/DVR/README.md) |
| PlusConstruction | [ring plus and original Q comparison](../../Quillen/KTheory/Plus/README.md), [standard map and sign](../../Quillen/KTheory/Plus/StandardComparison.md) |
| ClassicalCWPlus | [actual classical CW comparisons](../../Quillen/Topology/PlusConstruction/ClassicalCW.md), [constructed CW covers](../../Quillen/Topology/CWComplex/README.md) |
| HomotopyFoundations | [topological source families](../../Quillen/Topology/README.md) |
| SchemeKTheory | [scheme K/G-theory](../../Quillen/AlgebraicGeometry/Scheme/README.md), [projective-line geometry](../../Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/README.md) |
| PerfectComplexes | [perfect-complex K-theory](../../Quillen/AlgebraicGeometry/PerfectComplexes/README.md), [localization](../../Quillen/AlgebraicGeometry/PerfectComplexes/Localization.md), [coefficient Bass comparisons](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/BassComparison.md) |
| SpectraAndBass | [stable topology](../../Quillen/Topology/Prespectrum/README.md), [iterated S-spectrum](../../Quillen/Waldhausen/SConstruction/Iterated/README.md), [Bass constructions](../../Quillen/KTheory/Bass/README.md), [geometric comparisons](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/BassComparison.md) |

## Low-degree current status

The characteristic-zero original Milnor equivalences and same negative inverse
are native; [field scope](../../Quillen/KTheory/Field/README.md#current-boundary)
and [scalar/DVR normalization](../../Quillen/KTheory/LowDegreeScalarAction/README.md#same-negative-inverse-and-dvr-boundaries)
give their exact maps and conditions. Finite-field vanishing retains its separate
all-finite-field scope. Unit-pair generation still has its actual residue-section
premise. The closed residue-field normalization has its explicit characteristic-zero
premise; the raw/inverse DVR boundary formulas do not add that premise.

Q7's arithmetic generic-G1 injectivity premise remains explicit where used in
[Dedekind localization](../../Quillen/GTheory/Dedekind/README.md).
Infinite positive-characteristic Milnor equivalences, arbitrary-DVR local Milnor
presentations and broad R5 background integration are not claimed.

## Remaining comparisons

See [geometric comparison boundaries](../../Quillen/AlgebraicGeometry/PerfectComplexes/Development.md),
[stable topology](../../Quillen/Topology/Prespectrum/README.md),
[ring plus](../../Quillen/KTheory/Plus/README.md) and
[classical CW comparison](../../Quillen/Topology/PlusConstruction/ClassicalCW.md).
Degree-zero image statements, explicit small-model/coefficient universes and
conditional theorem-family inputs must remain attached to their interfaces.

## Verification

The code release at `69e542b4` has the principal's accepted mathematical and
native validation basis. This Markdown-only reorganization preserves code,
dependencies, examples and compatible build/audit evidence. Link checks measure
documentation consistency; they do not prove a missing mathematical comparison.

The published code validation at `69e542b4` also passed the complete
[code CI workflow](https://github.com/kangxyz/quillen-k-theory/actions/runs/39145674137),
including library/client validation and cache publication. This is operational
evidence for that code revision, not an additional mathematical premise.
