# The fine Bass model and its localization theorem

`FineBassK.lean` is a naming and certification facade for existing constructions. In
`Quillen.PerfectComplexes.FineBassK`, `spectrumDiagram Q` (notation in prose:
K^B_fine(Q)) is exactly `boundedFlatCoefficientAmbientBassTelescopeFunctor Q`.
It is the actual section-model telescope with its original Laurent Bass seed,
not a spectrum reconstructed from a list of groups.

The subsequent [tensor construction](TensorBassConstruction.md) directly
identifies the Bass recipe and establishes the TT 7.4 interpretation. The
facade-alone boundary below records what these earlier declarations supply
without that additional construction argument.

## Certification

- `bassMap` is the actual `strictDiagramTelescopeSelfMap` for that original seed.
  `bassMap_isStableEquivalence` discharges finite-stage T1 internally using
  `modelDiagramIterateSpaceT1Space`. It requires no compactness assumption.
  `supportedBassMap_isStableEquivalence` gives the corresponding supported result.
- `connectiveComparison Q n` identifies the original connective perfect K groups
  with this telescope in every natural degree, including K_0. The underlying
  comparison preserves the original stage-zero inclusion.
- `negativeComparison Q i` identifies the original Bass negative groups with the
  same telescope in degree -i; the underlying comparison retains its Laurent
  quotient map. These group comparisons assume Q is quasi-compact and
  quasi-separated.

## Basic and auxiliary localization

Let f : P -> Q be an open immersion over Spec R. Assume P and Q are
quasi-compact and Q is quasi-separated. At every coefficient a : Under R,
`localization f a` proves that the specified supported model maps by a stable
equivalence to the homotopy fiber of the actual restriction map.
`supportForget`, `restriction`, and `localizationNull` are aliases of the original
maps and whole nullhomotopy; `localizationFiberMap` is their existing fiber lift.
The restriction target is the ambient fine model on P, as recorded by
`boundedFlatCoefficientFullOpenBassTelescopeFunctor_eq_ambient`.

For an additional quasi-compact open T of Q, `auxiliaryLocalization f T a`
proves the corresponding fiber statement for supports away from T, its union
with the removed open, and its restriction to P. `auxiliaryForget`,
`auxiliaryRestriction`, and `auxiliaryNull` again retain the original data.

Both conclusions are stable equivalences in every signed degree. They do not
assert levelwise homotopy equivalences. The focused regression tests the actual
fiber lifts, the K_0 inclusion comparison, and both Bass self-maps without an
external T1 or stability argument. The downstream client exposes signed-degree
isomorphisms for both localization sequences.

## Scope and dependency boundary

The localization proofs are the existing theorems in
`CoefficientFullOpenBassLocalization.lean` and
`CoefficientSupportedFullOpenBassLocalization.lean`; the connective and negative
comparisons come from `CoefficientBassConnectiveTelescopeComparison.lean` and
`CoefficientBassFineTelescopeComparison.lean`. Bass stability uses
`KTheory/Bass/StrictDiagramSelfMap.lean` and `ModelDiagramConnectivity.lean`.
No unfinished raw R2 associativity or chosen higher scalar filler is a premise
of this facade.

The basic and auxiliary localization theorems for this explicitly constructed
fine model are proved. This facade alone supplies Bass stability and group
comparisons. The later tensor construction adds the actual input, cone-generator
laws and uniform recursion needed to identify the recipe of TT §§6.3–6.4.

Agreement of connective and recursive negative groups, or the stable Bass
self-map above, does not by itself identify the construction and its
localization-diagram data. The tensor construction provides that additional
argument through the represented recipe and its actual arrows and whole nulls.

Direct construction identification and a natural stable comparison are valid
routes, each retaining the relevant arrows and whole nullhomotopy. For a
separately chosen comparison target, the existing
`homotopyFiberLift_homotopySquare_isStableEquivalence_iff` provides a transfer
criterion once those data are supplied; it does not construct them.

The unfinished raw R2 route concerns a separately fixed implementation
comparison. No further raw R2 construction is required for the fine-model
localization theorems stated here. The later tensor-generated construction
supplies a direct recipe-identification route to TT 7.4; comparison with the
separate raw implementation remains additional work.
