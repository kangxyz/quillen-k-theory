# Documentation

The topic guides explain the library's mathematical objects, principal results,
canonical maps, and retained assumptions. Each guide ends at its own comparison
boundary. The [API reference](reference/API.md) gives focused imports and public
names; [mathematical scope](reference/Scope.md) summarizes coverage across topics.
Lean declarations specify the actual statements and proof inputs.

## Mathematical topics

| Topic | Guide |
| --- | --- |
| Exact structures, Quillen's Q-construction, canonical K-maps, and classical K₀ | [Exact categories](topics/ExactCategories.md) |
| S-construction, additivity, approximation, cofinality, fibration, and Q/S comparisons | [Waldhausen theory](topics/Waldhausen.md) |
| Finite-filtration dévissage, finite admissible resolutions, Serre localization, and finite-module G-theory | [Dévissage, resolution, and localization](topics/Localization.md) |
| Vector bundles, coherent sheaves, scheme K/G maps, finite direct image, and derived sheaf geometry | [Scheme K/G-theory](topics/SchemeKTheory.md) |
| Strict and locally perfect complexes, support, relative localization, degree-zero image, and Mayer–Vietoris | [Perfect-complex localization](topics/PerfectComplexes.md) |
| Connective spectra, stable maps and fibers, Bass recursions, finite stages, and telescopes | [Spectra and Bass groups](topics/SpectraAndBass.md) |
| Independent ring-specific homological plus model, original Q comparison, components, and scalar extension | [Ring plus construction](topics/PlusConstruction.md) |

Start with the topic containing the objects you need. Follow its source links
for exact declarations and its client links for public use. For example, a
geometric localization question starts with perfect complexes, while a question
about identifying Bass cokernels with telescope groups starts with spectra and
Bass groups. General categorical and topological foundations remain in their
source owners and the focused import reference.

## Shared references and development

| Document | Responsibility |
| --- | --- |
| [API reference](reference/API.md) | Import paths, canonical namespaces and maps, universes, and client entrypoints |
| [Mathematical scope](reference/Scope.md) | Cross-topic coverage, retained hypotheses, degree conventions, and unproved comparisons |
| [Architecture](development/Architecture.md) | Mathematical source ownership, import direction, and trust-check implementation |
| [Typechecking performance](development/Performance.md) | Reproducible measurements and their source/runtime scope |
| [Contributing](../CONTRIBUTING.md) | Source and documentation changes, builds, checks, and dependency policy |

Topic guides develop results in context. The API reference locates interfaces;
the scope reference records their collective boundary. Architecture and
performance describe development facts and do not supply mathematical premises.
Proofs and hypotheses have their source owners under `Quillen/`; documentation
does not create a second implementation or a stronger theorem.
