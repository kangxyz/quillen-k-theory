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
