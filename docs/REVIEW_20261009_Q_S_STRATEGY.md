# Independent Q/S comparison strategy review

Date: 2026-10-09. This is a proof-strategy review and a checked supporting
algebra theorem, not acceptance of the still-unfinished Q/S homotopy
comparison.

## Strategy verdict

The proposed degreewise equivalence is mathematically valid for a genuine
exact category: the groupoid of exact `S_(2n+1)` rows maps, by the nested
central intervals, to the groupoid `Core (Fun([n], Q E))`. The target
morphisms must be invertible natural transformations. Both the actual
span-equivalence relation and the exact-category universal properties are
essential; objectwise numerical data would not suffice.

### Reconstruction of a row

For `n = 0`, a row is a one-step flag ending in its sole nonzero term. For
`n = 1`, a Q-arrow represented by `X ← P → Y` reconstructs the flag
`0 → ker(P → X) → P → Y`, with admissible inclusions and actual quotients.

Inductively, suppose the earlier chain is represented by a flag ending in
`X`, and append a span `X ← P → Y`. Pull its existing flag back along the
admissible epimorphism `P → X`. The pullback of its initial zero object is
the genuine kernel. Prefix the zero object and append `Y` using the
admissible monomorphism `P → Y`. This adds exactly two steps. Quotienting
the new inner flag by the kernel recovers the old row, and its outermost
Q-arrow is precisely the appended span.

This construction only requires pullbacks of admissible monomorphisms
against admissible epimorphisms, their exact-category base-change axioms,
and kernels/cokernels of admissible maps. It requires neither all finite
limits in the original category nor global balancedness or weak idempotent
completeness. After constructing the admissible flag, the row must retain
all its actual quotient objects, maps, and pushout squares.

### Full faithfulness

First, every Q-isomorphism comes uniquely from an original isomorphism;
this is now independently proved in `QConstruction/Core.lean` below.
Second, a commuting square of Q-arrows is an equality of span classes,
which gives an actual apex isomorphism after the endpoints are identified.
Because the right legs are monomorphisms, an apex map compatible with the
right leg is unique. The kernel and quotient universal properties then
extend this isomorphism uniquely through the reconstructed flag and every
quotient term.

Induction on the chain length therefore gives both fullness and
faithfulness. This also proves independence of representatives and chosen
kernels/quotients. A strict naturally selected inverse is unnecessary:
the central-interval functor is already natural in the simplex direction,
and degreewise equivalences suffice for the later bisimplicial argument.

## Checked algebra support

New source: `Quillen/CategoryTheory/QConstruction/Core.lean`.
All declarations are in `Quillen.ExactStructure`.

- `qSpan_isIso_legs`: every representative of an invertible Q-arrow has
  invertible left and right legs.
- `qSpan_eq_qIsoOfIso`: such a span equals the Q-arrow of the original
  isomorphism obtained by inverting its left leg and following its right leg.
- `qIsoOfIso_injective`, `exists_iso_of_qHom_isIso`, and
  `qIsoOfIso_bijective`: the precise uniqueness and existence statements.
- `qCoreFunctor`: the actual identity-on-objects core functor, with
  `Full`, `Faithful`, `EssSurj`, and `IsEquivalence` instances.
- `qCoreEquivalence` and `qCoreEquivalence_map`: the equivalence, whose
  action on arrows is definitionally the existing `qIsoOfIso`.

The leg proof chooses a representative for an inverse Q-arrow and uses
both inverse equations. The first identifies the composite span apex with
the identity apex. Its left pullback projection is therefore monic and is
also an admissible epimorphism. The exact-category
`isIso_of_deflation_of_mono` makes it invertible, so the original left leg
is invertible. The other inverse equation gives an explicit section of the
original right leg. That leg is monic by admissibility, so a split-epi/mono
argument makes it invertible. No claim that all mono-epis in an exact
category are invertible is made.

The simpler abelian proof already existed in
`Localization/Serre/LocalizationComma.lean`; the new source does not import
that theorem or its abelian hypothesis. It proves the exact-category version
directly and uses the existing canonical `qIsoOfIso` construction.

## Topology obligations still to discharge

There are two distinct diagram comparisons, neither implied by the core
lemma alone.

1. The currently constructed `comparisonMap` subdivides both the original
   S direction and the nerve direction, so an n-simplex has a vertical
   `(2n+1)`-chain. Degreewise row-groupoid equivalence instead gives the
   diagonal with vertical nerve degree `n`. Restriction along the natural
   upper-half map `[n] → [2n+1]` supplies a bridge to the latter model.
   Prove that bridge a weak equivalence using the nerve subdivision
   comparison, then check its composite is the existing `comparisonMap`.
   The author's `upperIndex` is precisely this natural selection.
2. Compare the diagonal of `n ↦ N Core(Fun([n], Q E))` with `N(Q E)`.
   The natural map uses the diagonal chain of a rectangular diagram:
   `i ↦ F(i,i)`. Naive evaluation at a terminal vertex is not strictly
   natural under arbitrary simplex maps and should not be silently used
   in its place.

A convenient proof of the second obligation views the bisimplicial set in
the other direction. For fixed vertical degree `k`, its horizontal row is
the nerve of the category of `k`-chains of isomorphisms in `Q E`, with
arbitrary natural transformations. The constant-chain functor from `Q E`
to this category is an equivalence: evaluation at any vertex is a
quasi-inverse because all transition arrows are invertible. These
constant-chain inclusions are strictly natural in `k`. A rowwise
weak-equivalence/diagonal theorem therefore proves their diagonal inclusion a
weak equivalence. Natural diagonal evaluation is a retraction of that
inclusion, and hence a weak equivalence as well.

Finally retain the existing chosen zero basepoint and identify the induced
pointed map, rather than concluding only that the two unpointed spaces have
some weak equivalence. The new core functor itself preserves the original
zero object exactly.

## Verification

The new source was elaborated directly by Lean 4.34.0 with arbitrary object
and morphism universes, using `lake env lean -j1` under
`/tmp/quillen-lean-slot-1.lock`. The previously uncached pinned mathlib
`CategoryTheory.Core` was first compiled with its proper package root; no
mathlib source changed.

`audits/QCoreIndependentAudit.lean` selects all declarations by their
exact defining module, including private/generated constants, and recursively
checks their axiom dependencies. It also compiles arbitrary-universe
consumers for bijectivity on isomorphisms, the core equivalence, and the
forward-arrow identity by `rfl`. The complete rerun passed all **16
module-origin declarations**, allowing only `propext`, `Classical.choice`,
and `Quot.sound`. Logs:

- `logs/quillen-comparison-core-independent.log`
- `logs/quillen-comparison-core-independent-axioms.log`

The first audit harness run required only an explicit `Nat` annotation on
its counter and `noncomputable section` for the example returning an
equivalence. That initial harness diagnostic is preserved as
`logs/quillen-comparison-core-independent-axioms-first.log`; no library
proof was changed for it.

No previously accepted regular-scheme source was modified. This support
module is separate from the accepted global regular K-to-G endpoint.
