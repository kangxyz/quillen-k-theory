# Genuine relative-row replacement of mixed chains

## Generic construction

`Fibration/RelativeRows/ChainReplacement.lean` starts with an original finite
chain all of whose arrows are coarse weak equivalences. Its arrows need not
be cofibrations. The objects form the full subcategory of the unchanged
`ComposableArrows` category with this actual arrow predicate.

The existing `FunctorialFactorization.finiteReplacement` produces the actual
replacement chain. Its arrows are fine cofibrations because the two given
cofibration classes agree; they remain coarse weak by the original natural
projection and coarse two-out-of-three. `replacementChainFunctor` retains
this exact chain and its original transformation maps.

`relativeReplacement` is the composition with the already-proved genuine
zero-augmented cofiber-completion functor. Thus its output is an actual
relative row, with genuine quotient pushouts and cofibration arrows.
`replacementInitialIso` identifies its original initial filtration with the
literal finite replacement through the original quotient-by-zero maps.

`relativeReplacementProjection` is the inverse of that original initial
isomorphism followed by the actual finite cylinder projection. It is an
actual natural transformation to the original chain. Its displayed
component formula is retained literally, and every component is coarse weak.
The structural `PreservesFineSquares` condition on the actual cylinder
middle functor ensures that pointwise fine transformations remain fine on
the entire completed relative row.

The construction requires coarse two-out-of-three and a genuine functorial
factorization. It does not require the extension axiom or fine saturation.
Fine-square preservation is needed only for the fine-map preservation lemma.
Neither the projection nor its naturality is advertised as fine weak.

## Actual inner complex rows

`RelativeRows/ComplexChainReplacement.lean` instantiates this construction
using the proved actual identity-cone factorization on genuine fine quotient
rows. Its Reedy row cofibration and fine-square preservation evidence comes
from the accepted exact joint-cylinder construction. It is not inferred from
componentwise cofibration evidence alone.

The hypotheses are the actual extension-closed, zero-containing, replete,
finite-product-closed full complex subcategory, with cone and shift closure
needed by the original joint-cylinder input. Original coarse projections
are quasi-isomorphisms at every original chain vertex and inner interval.
Fine transformations are original intervalwise isomorphisms. The actual
bounded-term and arbitrary-scheme instances use their proved cone/shift
closure, with no global term bound or kernel-closure assumption.

## Remaining comparison obligation

This is a genuine replacement construction with a coarse-only natural
projection. It does not supply a natural transformation in the fine-weak
chain category and does not imply a per-outer-degree fine-nerve equivalence.
The mixed-direction comparison and diagonal fibration remain separate proofs.

## Verification

Both focused source checks, all24 recursive defining origins (15 + 9), and
all17 actual-map/degree0/bounded/arbitrary-scheme consumers passed warning-free,
with only the standard three axioms. The frozen source manifest is
`logs/relative-rows-chain-replacement-sources.sha256`; the terminal fixed24 audit also passed in
`logs/relative-rows-chain-replacement-audit-final.log`. Independent review passed: fresh two-target rebuild, fixed24 defining
origins and17 consumers in the combined54-origin audit, with unchanged
source and prerequisite hashes. The driver is
`audits/RelativeRowsChainReplacementAudit.lean`; its consumers retain the
actual finite replacement, completion, projection factors, naturality, fine
preservation, degree0, inner row structure, and bounded/arbitrary-scheme use.
