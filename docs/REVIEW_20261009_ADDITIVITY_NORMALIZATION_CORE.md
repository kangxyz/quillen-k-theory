# Independent review: additivity normalization core

Date: 2026-10-09. Result: **accepted for the frozen nine-source boundary**.

## Reviewed boundary

The nine frozen author-owned modules are listed in
`logs/additivity-normalization-independent-20261009/sources.sha256`.
This review covers the actual chosen-zero normalization of the mixed
bisimplicial deformation and its genuine fixed-zero mixed homotopy. It excludes
the separately authored normalized endpoint families/homotopies, the based
subdivision cancellation module, and final group-map assembly.

I read all nine sources completely, with the relevant existing structural
pushout, interval-arrow, coproduct-zero, canonical rebase, and mixed-cylinder
contracts. No production source was changed.

## Mathematical and Lean contract

### Actual normalization and genuine diagrams

`normalizedFunctor` replaces only the specified object's image and conjugates
all maps by the explicit objectwise isomorphisms, via `Functor.copyObj`.
`normalizationIso` is the actual natural isomorphism. This general construction
allows independent source and target object/hom universes; at a common universe
pair both functor and isomorphism agree **definitionally** with the existing
canonical `Quillen.rebaseFunctor` and `Quillen.rebaseFunctorIso`.

`simplex₂_of_iso` proves all original two-degree S-diagram conditions are
preserved: actual zero objects, actual cofibration arrows, actual quotient
pushout squares, and weak nerve arrows. Its pushout assertion is transported
by the displayed component isomorphisms and naturality squares. No replacement
predicate or realization equivalence is substituted for these conditions.

The normalized pushout functor is the original genuine pushout functor rebased
at the literal identity arrow of `V.zero`. Its isomorphism to `W.zero` is proved
from structural exactness and the actual pushout of zero objects. This handles
the possibly larger object universe of `Arrow C` honestly. The pushout functor
is not assumed globally Waldhausen-exact on an unspecified arrow-category
structure: the needed actual S-diagram preservation is proved directly.

### Actual mixed maps and common endpoint

The normalized interval and mixed diagrams use the same actual interval-arrow
functors and the same first/switched mixed ordinal maps as the original
deformation. Independent nerve restriction and all outer ordinal restrictions
commute strictly; this includes degeneracies and maps changing the selected
suffix. The resulting `normalizedMixedMap` is a genuine bisimplicial map.
Its zero and one restrictions are proved equal to the stated normalized identity
and separated-half maps.

The common pair-sum endpoint is the actual functor `(X,Y) ↦ H(X) ⨿ F(Y)`,
normalized only at `(V.zero,V.zero)`. The required zero isomorphism follows from
actual coproduct universal properties and exact preservation of zero objects.
The source pair diagram uses the two real subdivision restrictions. Independent
reindexing is strict, and the S-diagram conditions survive the actual
normalization isomorphism. Binary coproducts are an explicit hypothesis only
for this common sum layer.

All map-level S-set constructions use the common source/target universe pair
of the existing APIs. The internal functor/diagram normalization results retain
independent source and target universe pairs. There is no raw cross-universe
K-map identification.

### Genuine zero tracks

For a constant chosen-zero input diagram, every actual interval arrow is
literally `id` of `V.zero`; this remains true for every mixed cut. Therefore the
normalized pushout has actual value `W.zero` at every point. Zero uniqueness
then identifies the full diagram, including every map, with the chosen constant
zero diagram. The corresponding exact zero statements for identity, separated,
canonical rebased middle, and normalized common-sum maps are theorems.

`mixedEndpointHomotopy` is the explicit minimum-cut contraction, restricted
through the actual one section and followed by the actual deformation map.
Its endpoints are derived from the proved contraction endpoint identities and
one-section/projection identity. `normalizedMixedEndpointHomotopy` retains this
same underlying cylinder and has exactly the horizontal-endpoint-followed-by-
normalized-identity map and the normalized-separated map as endpoints.

`normalizedMixedEndpointHomotopy_fixed_zero` evaluates that real cylinder on
the subdivided constant-zero vertex. Every intermediate input arrow is still
the literal zero identity, so the same normalization equality proves the whole
simplicial track is constant. `normalizedMixedRealizationHomotopy_fixed_zero`
then applies the existing actual realization fixed-vertex theorem for every
`t : unitInterval`.

No fixed-track equation, desired homotopy, K-equivalence, or additivity conclusion
is assumed. Structural exactness and the actual relative-cofibration predicate
are the ordinary inputs for the deformation. The zero-track result is proved
for the actual constructed maps.

## Limits

This boundary supplies the actual normalized mixed deformation and its fixed
zero track. The two endpoint identifications, based subdivision cancellation,
final based additivity, products of K-maps, and Gillet–Waldhausen/fibration
theorems are outside these nine files. The generic normalization's input
isomorphism is a genuine object isomorphism; in the deformation application it
is constructed from the proved zero-object property, not from K-theory data.

## Frozen source manifest

Manifest: `logs/additivity-normalization-independent-20261009/sources.sha256`

Manifest SHA-256:
`de951ae6b368e96a126ff4e83b4726058b3ff9e6f727d94680db409c905ea792`

- `DiagramIso.lean`: `20390f2e8a6912a3abda230b0e07bdb13c8726d4c46193f0563a688979b28916`
- `NormalizeFunctor.lean`: `c1c37e5831dd887607f220d9a618b3ec7e2931fde6e871a1ffa703a2b51b7813`
- `NormalizedPushout.lean`: `8f59cc6590c190c69b6499008c5bad2a658d26e849abcae2f5b07cb14c7d1955`
- `NormalizedMixedDiagrams.lean`: `4400d477ef9a483a38eb2073d5637aff2ea40e17f5f138652d6c73e90a5b6d8d`
- `NormalizedDeformationMap.lean`: `63052b7c9cc42337c85f6328e9721a784cd1150bd48cfd7d5662299f095faea0`
- `NormalizedSumMap.lean`: `95bc4edc29fae474366d9ed053f3919b722a4fdccf0288069fbf87a435dc2995`
- `NormalizedZeroMaps.lean`: `67b98992c15a7c832be7e3aa2915049b3e4df303be401e35d8ab95d3271acf4b`
- `MixedEndpointHomotopy.lean`: `02e3387e6bbe62a07bd557d0452e1599b8dfffe87c079df69c1f75d7bea783c4`
- `NormalizedMixedHomotopy.lean`: `623b81c5ae860c41470b4405eb9e079274cf08b5b1f66451efce419f2c57db9b`

## Independent checking and evidence

All nine selected modules were rebuilt from the frozen sources into a new
isolated namespace under `logs/additivity-normalization-independent-20261009/olean`.
The reviewed artifacts are fresh regular files; unchanged dependencies are
linked. `lean --deps` confirms that the final module selects both fresh direct
dependencies. No live Lake build or replacement of production oleans was used.
Compilation used Lean 4.34.0, `-j1`, and the shared slot1 lock, with acquisition
logged. All nine source checks are warning-free.

`audits/AdditivityNormalizationIndependentAudit.lean` runs a fixed **77-origin**
audit including every private/generated declaration defined by the nine
modules. Recursive `collectAxioms` permits only `propext`, `Classical.choice`,
and `Quot.sound`. All 77 pass in the final audit, and no implementation source
contains a new axiom or `sorry`.

The independent consumers retain separate source/target object and hom
universes for generic normalization and interval-diagram preservation. At the
common universe pair they check canonical normalization equality by `rfl`,
actual zero/one mixed-map identities, the literal minimum-cut cylinder formula,
the precise simplicial homotopy endpoints, the exact normalized common sum,
and the actual realized fixed-zero point for every time.

The initial added consumer used `normalizedSumMap_zero`'s positional exactness
arguments in the wrong order; this was a consumer-only correction. The final
fixed77 audit and every consumer pass warning-free. No production repair was
necessary. All nine source hashes match before and after the run.

Evidence directory: `logs/additivity-normalization-independent-20261009/`

- `check.log`: ordered fresh nine-source rebuild
- `audit-final.log`: final fixed77 recursive origin audit and all consumers
- `audit.log`: preserved initial audit/consumer diagnostic
- `deps.log`: selected fresh dependency paths
- `hashes-before.log`, `hashes-after.log`: frozen source rechecks
- `artifacts.sha256`: exact independent audit, report, logs, and nine fresh oleans
