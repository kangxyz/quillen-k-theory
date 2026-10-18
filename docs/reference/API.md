# API index

Use [source-family guides](../../Quillen/README.md) for detailed imports,
declaration names, universes, hypotheses, canonical maps and client examples.
This file is an index; it does not maintain a second interface specification.

| Interface | Source authority |
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

## Migration and native ownership

General local candidates use `Quillen.Aglib` imports and native mathematical
declaration namespaces; see the [candidate policy](../../Quillen/Aglib/README.md).
Supplied upstream Aglib implementations are imported directly from their pinned
native leaves. Application adapters remain in Quillen; no duplicate source or
default compatibility wrapper is introduced by this documentation refactor.
The standard-sign compatibility route is
[StandardSignMigration](StandardSignMigration.md). Historical 0.5/0.7/0.9 source
integration notes identify migrations, not a new publication or verification event.

## Previous import routes

| Previous import | Current source owner |
| --- | --- |
| `Quillen.GTheory.FiniteModules.Basic` | `Aglib.Algebra.Category.ModuleCat.Finite` |
| `Quillen.AlgebraicGeometry.Scheme.Regular.FiniteProjectiveResolution` | [module-complex family](../../Quillen/Aglib/Algebra/Homology/ModuleCat/README.md) |
| `Quillen.AlgebraicGeometry.Scheme.Regular.LocalPrincipalDomain` | [regular-local family](../../Quillen/Aglib/RingTheory/RegularLocalRing/README.md) |
| `Quillen.Waldhausen.QuillenComparison.SpanNaturality` | [Q-construction family](../../Quillen/CategoryTheory/QConstruction/README.md) |
