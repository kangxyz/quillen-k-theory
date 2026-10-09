# Independent review: ordinary ambient relative cylinder cofibrations

Accepted 2026-10-09 06:31 UTC after complete semantic inspection, fresh isolated
rebuild, fixed-count recursive axiom audit, exact-map/minimal-hypothesis
consumers, and matching pre/post source and inspected-dependency hashes.

## Accepted mathematical scope

`Quillen/Waldhausen/Cylinder/AmbientRelative.lean` proves that the actual relative
joint-endpoint map is monic when only the map on sources is monic. The proof
uses the two original joint-endpoint conflations and the accepted actual
relative-pushout inflation theorem. Their quotient map is precisely the shift
of the source map, hence monic by the actual shift equivalence. Uniqueness of
pushouts transports the canonical comparison to the displayed relative map.
No degreewise splitting or condition on the map of targets is used.

The previously proved actual relative cokernel universal property then gives
the original short exact sequence, whose quotient is exactly the shifted actual
source cokernel. For an inherited full complex subcategory, admissibility of
the source map places its actual cokernel in the object predicate, and shift
closure places the displayed quotient there. This proves the original relative
map is an ordinary inherited cofibration. Arbitrary quotient closure is not
assumed, and a monic ambient source alone is not incorrectly promoted to
inherited admissibility.

The ambient pushout hypothesis is usable from the ordinary inherited pushout:
the independent consumer derives its ambient universal property using the
already proved joint cofibration and inherited pushout-preservation theorem.
Thus this result covers the ordinary ambient-cofibration model as intended.
It supplies structural cylinder data, not a fibration or K-equivalence theorem.

## Independent checks

The source rebuilt warning-free into an isolated artifact overlay excluding
its live source-origin artifacts. The audit resolves the fresh actual olean.
`audits/CylinderAmbientRelativeIndependentAudit.lean` checks exactly four
source-origin declarations, including the generated private declaration, with
recursive axiom collection. Only `propext`, `Classical.choice`, and `Quot.sound`
are allowed.

Consumers retain independent object/hom universes and no source splitting or
target monicity hypothesis. They check the original actual relative map, its
short exact sequence, the exact shifted-cokernel object and projection, and
ordinary inherited cofibrations from an ordinary inherited pushout. The final
audit is warning-free. No defect was found and no frozen source or live olean
was modified.

## Evidence

- Frozen manifest: `logs/cylinder-ambient-relative-sources.sha256`
- Independent source/audit/import-resolution/hash evidence:
  `logs/cylinder-ambient-relative-independent-20261009/`
- Independent audit: `audits/CylinderAmbientRelativeIndependentAudit.lean`
