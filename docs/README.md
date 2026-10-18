# Documentation and reading routes

The [source-family guides](../Quillen/README.md) own mathematical results,
focused imports and API/interfaces, with exact hypotheses, canonical maps and
remaining comparisons. This directory provides concise reading routes,
cross-family status summaries and global operational guidance. Lean declarations
specify the actual statements; documentation and green checks do not supply a
missing mathematical premise.

## Mathematical topics

- [ExactCategories](topics/ExactCategories.md): [Q-construction](../Quillen/CategoryTheory/QConstruction/README.md), [canonical K-theory](../Quillen/KTheory/README.md), [K0 comparison](../Quillen/KTheory/GrothendieckComparison/README.md).
- [Waldhausen](topics/Waldhausen.md): [Waldhausen theory](../Quillen/Waldhausen/README.md).
- [Localization](topics/Localization.md): [dévissage](../Quillen/Devissage/README.md), [resolution](../Quillen/Resolution/README.md), [Serre localization](../Quillen/Localization/Serre/README.md), [finite-module G-theory](../Quillen/GTheory/FiniteModules/README.md).
- [LowDegreeFieldSupport](topics/LowDegreeFieldSupport.md): [field comparisons](../Quillen/KTheory/Field/README.md), [finite support](../Quillen/KTheory/FiniteSupport/README.md), [Dedekind support](../Quillen/GTheory/Dedekind/README.md), [scalar actions and normalization](../Quillen/KTheory/LowDegreeScalarAction/README.md), [DVR generation](../Quillen/GTheory/DVR/README.md).
- [PlusConstruction](topics/PlusConstruction.md): [ring plus and original Q comparison](../Quillen/KTheory/Plus/README.md), [standard map and sign](../Quillen/KTheory/Plus/StandardComparison.md).
- [ClassicalCWPlus](topics/ClassicalCWPlus.md): [actual classical CW comparisons](../Quillen/Topology/PlusConstruction/ClassicalCW.md), [constructed CW covers](../Quillen/Topology/CWComplex/README.md).
- [HomotopyFoundations](topics/HomotopyFoundations.md): [topological source families](../Quillen/Topology/README.md).
- [SchemeKTheory](topics/SchemeKTheory.md): [scheme K/G-theory](../Quillen/AlgebraicGeometry/Scheme/README.md), [projective-line geometry](../Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/README.md).
- [PerfectComplexes](topics/PerfectComplexes.md): [perfect-complex K-theory](../Quillen/AlgebraicGeometry/PerfectComplexes/README.md), [localization](../Quillen/AlgebraicGeometry/PerfectComplexes/Localization.md), [coefficient Bass comparisons](../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/BassComparison.md).
- [SpectraAndBass](topics/SpectraAndBass.md): [stable topology](../Quillen/Topology/Prespectrum/README.md), [iterated S-spectrum](../Quillen/Waldhausen/SConstruction/Iterated/README.md), [Bass constructions](../Quillen/KTheory/Bass/README.md), [geometric comparisons](../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/BassComparison.md).

## Shared references and development

- [API index](reference/API.md): focused family entrypoints.
- [Scope summary](reference/Scope.md): coverage and explicit frontier routes.
- [Standard comparison compatibility](reference/StandardSignMigration.md).
- [Architecture](development/Architecture.md): source ownership and trust operations.
- [Performance](development/Performance.md): measured source/runtime evidence.
- [Low-degree status](development/LowDegreeFieldSupport.md).
- [Matsumoto status](development/MatsumotoCompletion.md).
- [TT localization route](development/TTLocalization.md) and [continuation](development/TTContinuationHandoff.md).
- [Contributing](../CONTRIBUTING.md): source changes, incremental checks and dependency policy.
