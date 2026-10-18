# Hom candidates

`Exact` transports equality of a homomorphism range with a kernel through commuting multiplicative equivalences of three groups. Only the original group hypotheses are used.

`CentralLifts` proves that a homomorphism lifting a surjection through a central
kernel contains the target commutator subgroup in its range. Perfectness of
that target gives surjectivity. The three group universes are independent;
the original Steinberg/fiber applications remain in `Quillen.KTheory.Field`.

These local general-theory candidates preserve the existing declaration namespaces, hypotheses and universes. Their K-theory applications remain in downstream modules.

- [`Exact.lean`](Exact.lean)
- [`KernelComparison.lean`](KernelComparison.lean)
- [`CentralLifts.lean`](CentralLifts.lean)

## Central kernel helpers

`CentralKernel.lean` supplies lift-independent commutators for a group
homomorphism with central kernel. Surjectivity is not required. Its `Doubling`
namespace supplies uniqueness and commutation arguments under the explicitly
stated simultaneous conjugation/squaring equations. The chain theorem also
takes the stated commutation of the first and output roots.

The native namespaces are `MonoidHom.CentralKernel` and
`MonoidHom.CentralKernel.Doubling`. The intended upstream owner is
`Aglib.Algebra.Group.Hom.CentralKernel`. The existing `CentralLifts` provider
remains the owner of its earlier public API; it is an import, not duplicated here.
The current consumers are `FiniteRootLifting` and `DetectorTransfer` in the
Matsumoto application family.

- [`CentralKernel.lean`](CentralKernel.lean)

## Imports

| Import | Interface |
| --- | --- |
| `Quillen.Aglib.Algebra.Group.Hom.CentralLifts` | Central-kernel lifting contains the target commutator subgroup; a perfect target gives surjectivity, in independent group universes |
