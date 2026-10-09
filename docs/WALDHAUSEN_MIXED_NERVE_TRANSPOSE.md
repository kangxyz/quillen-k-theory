# Original mixed-nerve transposition

Source boundary: `Fibration/MixedNerves/FineChains`, `ChainCategories`,
`Transpose`, and `TransposeNerves`. All four focused source checks pass
warning-free. The source manifest is
`logs/mixed-nerves-transpose-sources.sha256`.

## Actual objects and maps

For a genuine nested pair `N` on `V`, `FineChain V k` is the full category
of original `k`-chains whose arrows are fine weak equivalences. It retains
all natural transformations. The pointwise original fine-cofibration and
coarse-weak predicates are imposed only afterward. In particular, the
coarse projection of a cylinder is not silently required to be fine weak.

The other direction reuses the accepted `CoarseWeakChain N n`,
`CofibrationWeakChain N n`, and `FineWeakChains N n`. The definitions of
`FineWeakCoarseChains`, `HorizontalChains`, and `HorizontalCofChains`
retain the original underlying arrows. Every ordinal restriction is
literal precomposition; identity/composition laws are proved.

`transposeCoarse` and `transposeCof` switch precisely the two original
indices. Their inverse operations are explicit and proved inverse.
The object at `(i,j)` is the original object at `(j,i)`; horizontal
and vertical arrows are the corresponding original components. The
cofibration version carries the original component cofibration proofs.

`coarseTransposeIso` and `cofTransposeIso` are natural isomorphisms
from the flipped original bisimplicial nerves to the horizontal nerves.
Both ordinal directions are retained. `transpose_inclusion` proves
the strict square for the literal original inclusion. The derived
`coarseDiagonalIso`, `cofDiagonalIso`, and `diagonal_inclusion` retain
that same square on diagonals.

## Scope

All four sources allow independent object and hom universes `u,v`;
the nerves live in `SSet.{max u v}`. Degree zero in either or both indices
is included. No extension axiom, saturation, cylinder data, realization
equivalence, or fiber conclusion is an input or consequence of this
presentation boundary. The cylinder and realized comparison are separate
sources. The original relative-inner-S/quotient-row identification is also
a separate obligation.

## Verification

`audits/MixedNervesTransposeAudit.lean` traverses declaration origins once,
recursively rejects every nonstandard axiom, and checks 30 actual-map,
universe, inverse, inclusion-square, and zero-degree consumers.
All 179 declaration origins (24+78+61+16) and all 30 consumers passed
warning-free, including the terminal fixed179 replay.
Evidence manifest: `logs/mixed-nerves-transpose-artifacts.sha256`.
The source manifest fingerprint is
`f79375442252a3b6cd7b53198990f695721d36990b63bc6f7d32431f1338c090`.
