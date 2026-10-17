# Aglib candidates

This directory holds maintained general-theory source developed in Quillen for
later inclusion in Aglib. Follow the [shared candidate policy](https://github.com/kangxyz/aglib/blob/main/doc/DEVELOPMENT.md#downstream-candidates-for-aglib).

Use `Quillen/Aglib/` as the source location and `Quillen.Aglib` as the temporary
module prefix. Mirror the intended Aglib mathematical path below it. Keep
native mathematical declaration namespaces, so migration normally changes
imports rather than the meaning or names of the interfaces. A package-root
`Aglib/` tree would shadow the upstream dependency and must not be used here.

Before adding a candidate, check existing Mathlib and Aglib APIs. Keep its
imports in Mathlib, Aglib, or explicitly designated general candidate leaves;
keep host applications and their adapters outside this subtree. Coordinate
one implementation owner across downstream libraries. Record the intended
upstream module, exact hypotheses and current consumer in the module docstring,
and describe interfaces and main results in each occupied family's README.

Candidates are enrolled and checked as ordinary Quillen production modules.
They are not scratch, a separate Lake library, or proof of upstream acceptance.
Once an accepted upstream revision is pinned, retarget the consumers and remove
the local implementation; avoid duplicate implementations and default legacy
facades.

Existing general-theory implementations are staged here before admission to
Aglib. Specialized applications remain in their mathematical host families and
import the focused candidate leaves. Mixed files separate their general
constructions from their curve, arithmetic or K-theory endpoints.

The candidate module prefix records the temporary implementation owner. Source
relocation preserves existing declaration names, objects, hypotheses and chosen
comparison maps; it does not by itself redesign the public mathematical API.
Future upstream admission selects canonical native namespaces and removes the
accepted local implementation together with its old imports.

## Mathematical interfaces and results

| Family | Interfaces and main results |
| --- | --- |
| [Module constructions](Algebra/Module/README.md) | Finite-projective retracts, finite defect parametrices, matrix presentations and balanced scalar extension |
| [Module complexes](Algebra/Homology/ModuleCat/README.md) | Ordinary complex, tensor, exactness and homology interfaces |
| [Exact-category filtrations](CategoryTheory/ExactCategory/Filtration/README.md) | Actual filtrations, factors and additive-invariant formulas under their conflation hypotheses |
| [Displayed colimits](CategoryTheory/Limits/README.md) | Lower-ideal gluing and pointwise pushout interchange |
| [Paths and homotopies](Topology/Path/README.md) | Whole path reconstruction, pointwise evaluation and exact homotopy pasting for coefficient Bass carriers |
| [Regular-local algebra](RingTheory/RegularLocalRing/README.md) | Local algebra and finite projective-dimension bounds with the original hypotheses |
| [Scheme module sheaves](AlgebraicGeometry/Modules/README.md) | Coherent/quasicoherent operations, ordinary and derived complexes, and intrinsic perfect-complex theory |
| [Polynomial/Laurent spectra](AlgebraicGeometry/Spec/PolynomialLaurent/README.md) | Canonical affine schemes, ring maps, coordinates, base-change squares and open immersions |

Public import entry: `Quillen.Aglib`. Prefer the focused leaves described in the
family guides for implementation dependencies. Existing public mathematical
namespaces are preserved; original Q/K/G/S, Waldhausen, spectrum and specialized
curve/projective-line constructions remain in their application owners.
