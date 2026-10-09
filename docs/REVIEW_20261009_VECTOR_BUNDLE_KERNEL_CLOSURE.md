# Arbitrary-scheme vector-bundle kernel closure

2026-10-09. Lean 4.34.0; mathlib revision
`5ed2965256430c3649e86755f9576b54eca72435`.

## Checked scope

The two new modules are:

- `Quillen/Scheme/VectorBundle/AffineProjective.lean`
- `Quillen/Scheme/VectorBundle/KernelClosure.lean`

They prove the actual geometric exact-embedding prerequisite for
Gillet–Waldhausen on **every scheme**. The main instance is

```lean
instance finiteLocallyFree_kernelClosed (X : Scheme.{u}) :
  (sheafExactStructure X).IsKernelClosed (finiteLocallyFree X)
```

The predicate is the existing finite-local-basis definition, and the ambient
exact structure is that of all actual module sheaves. For a short exact
sequence whose middle and quotient are vector bundles, its actual kernel
term is finite locally free. `finiteLocallyFree_kernel` also applies this
to the actual categorical `kernel p` of an ambient epimorphism.

The exact-embedding condition is exposed directly:

```lean
theorem vectorBundle_deflation_of_ambient_epi {X : Scheme.{u}}
    {M N : FiniteLocallyFree X} (p : M ⟶ N) [Epi p.hom] :
    (vectorBundleExactStructure X).deflation p
```

The epi hypothesis concerns the underlying map in **all module sheaves**.
The conclusion is the existing inherited admissibility predicate, witnessed
by its actual categorical kernel and short exact sequence. No caller-supplied
kernel closure, local splitting, finite resolution, cycle membership,
K-equivalence, or related conclusion is assumed. There is no noetherianity,
regularity, quasi-compactness, resolution-property, or global sheaf-projectivity
hypothesis. Existing accepted regular/coherent sources were not changed.

## Proof inspection

On `Spec R` for an arbitrary commutative ring, finite local bases supply a
principal-open cover. Each localized module of global sections is free and
finite; its finite presentation descends along this actual cover, using
`Module.FinitePresentation.of_localizationSpan'`. The existing affine free
locus criterion then proves projectivity of the actual module of global
sections. The missing finite-presentation step is proved explicitly; the
older finite-generation theorem is not mistaken for finite presentation.

An actual affine sheaf short exact sequence has quasicoherent kernel,
by ambient quasicoherent finite-limit closure. The sequence is lifted to the
full quasicoherent subcategory, with exactness reflected through its actual
faithful inclusion, and mapped along the genuine tilde equivalence. The
quotient module is projective, so the actual module epimorphism has a
section. Its actual kernel is a direct summand of the finite projective
middle module and is consequently finite projective. The tilde counit
identifies its associated sheaf with the original sheaf kernel term.

On an arbitrary scheme, restriction to the canonical affine open cover
preserves the actual short exact sequence and finite local freeness of its
last two terms. The affine result followed by the existing affine-chart
locality theorem proves the original kernel term finite locally free.
All splitting and projectivity used here are on affine section modules;
no lift or splitting in the global sheaf category is asserted.

## Gillet–Waldhausen contract and remaining gap

Thomason–Trobaugh 1.11.3 requires a full faithful exact embedding into an
abelian category, extension closure, reflection of exact sequences, and
condition 1.11.3.1: ambient epimorphisms between embedded objects are
admissible. Example 1.11.4 includes vector bundles on arbitrary schemes.
Theorem 1.11.7 compares the exact category with its bounded-complex
quasi-isomorphism models, for both admissible and degreewise-split
cofibrations. The new theorem above discharges condition 1.11.3.1 for the
existing actual vector-bundle inclusion; extension closure and the
inherited exact-sequence characterization were already proved in
`VectorBundle/Exact.lean`. See the [original paper, printed pages 278–280](https://gwern.net/doc/math/1990-thomason.pdf#page=31).

This is an exact-embedding prerequisite, not a proof of the
Gillet–Waldhausen K-equivalence. The genuine Waldhausen additivity/fibration
comparison remains separate. Nor does this establish equality of strict
and locally-perfect K-theory.

The audit additionally checks direct specialization of the separately
proved generic `GilletWaldhausen.AcyclicCycles` and `AcyclicTruncation`
modules to the existing `strictPerfect X` predicate. For arbitrary `X`,
an actual acyclic strict-perfect complex has finite locally free actual
cycle objects; its canonical `truncLE` and actual truncation quotient stay
strict perfect and acyclic; the lifted actual truncation sequence is an
inherited conflation. These are consumer checks of the canonical existing
objects and maps, without changed definitions or extra geometric assumptions.

## Verification

Both source files passed focused `lean -j1` checks with no warnings and
produced importable oleans. All checks acquired
`/tmp/quillen-lean-slot-1.lock`. The pinned mathlib finite-presentation
locality module was compiled from its unchanged source because its cached
olean was initially absent.

The defining-origin audit includes every declaration in both new modules,
including private/generated constants, and recursively checks their axiom
dependencies. The only allowed axioms are `propext`, `Classical.choice`, and
`Quot.sound`. It also checks arbitrary-scheme and arbitrary-ring consumers
and the actual strict-perfect cycle/truncation specializations above.
The clean combined audit passed all **7 declarations** (2 affine and 5
kernel declarations) and every consumer, with no warnings or errors. Both
source hashes still matched after the audit.

This is the implementing worker's proof and verification report. A separate
independent review by the parent is requested; it is not represented as
already completed here.

Evidence:

- `logs/vector-bundle-affine-dependency.log`
- `logs/vector-bundle-affine-projective.log`
- `logs/vector-bundle-kernel-closure.log`
- `audits/VectorBundleKernelClosureAudit.lean`
- `logs/vector-bundle-kernel-20261009/origin-axioms-and-consumers.log`
- `logs/vector-bundle-kernel-20261009/sources.sha256`

Source SHA256:

```text
160ea5d3dc310a768b65e2d50bdf8c3502a6976be9296f0a0c112766b578dd2d  Quillen/Scheme/VectorBundle/AffineProjective.lean
5715df49856c0e41bad77267a81ac65944fc846ed230c348cb078cb47481033d  Quillen/Scheme/VectorBundle/KernelClosure.lean
d7f219a177e6ae169a07cbba855bb8e8871525e52673eb082bf24c77c3198847  .lake/packages/mathlib/Mathlib/RingTheory/LocalProperties/FinitePresentation.lean
```

Audit SHA256:

```text
f68fa72a8f0e3879f5a6372836571923579a0c0d10a47840a8cf334301950f67  logs/vector-bundle-kernel-20261009/sources.sha256
40057b15d3938cca11a5f0bec7ff9a1c2ba013ea64b4465a685f81103767fbe3  audits/VectorBundleKernelClosureAudit.lean
eeb132c517ec60476e537c37784c681a734a5baccc3600c0b37b7558a0e78445  logs/vector-bundle-kernel-20261009/origin-axioms-and-consumers.log
```

The post-audit source recheck is
`logs/vector-bundle-kernel-20261009/post-audit-hashes.log`.
