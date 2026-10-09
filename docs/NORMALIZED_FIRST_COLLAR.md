# Actual first-pushout endpoint collar

Checked 2026-10-09. Source: `Quillen/CategoryTheory/TheoremB/NormalizedFirstCollar.lean`.

For the unchanged `NormalizedOpenGluing.Data.first_isPushout`, a continuous
bridge height equal to one on the original left attaching map extends by one
on the unchanged end. For every cutoff below one its upper collar is open.
Open restriction, with the actual coordinate maps, proves that this collar is
the pushout of the bridge collar and the old end.

A supplied genuine local strong deformation retraction of that bridge collar
therefore extends to a genuine local SDR of the old end inside the first
attachment. Its complete homotopy preserves the original displayed base
whenever the bridge deformation does. No whole-bridge deformation, injective
attachment, or preservation of arbitrary pullbacks is assumed.

The source also proves the actual complement-fiber fact: if `firstBase x` is
outside the overlap `V`, then `x` lies in the endpoint collar. Consequently the
collar and the original bridge base-chart cover the first attachment, including
empty overlaps. This supports full boundary-track control; it is not yet the
finite lifting theorem for `firstEnd` or a weak-equivalence assertion about
`firstProjection`.

## Validation

- Warning-free direct source compilation: `logs/normalized-first-collar-check4.log`.
- Frozen source: `logs/normalized-first-collar-sources.sha256`.
- Recursive all-origin audit: exactly 51 defining constants, only `propext`,
  `Classical.choice`, `Quot.sound`.
- All 12 arbitrary-universe consumers pass, including original inclusion/base
  maps, the full deformation equation and the empty-overlap case.
- Audit: `audits/NormalizedFirstCollarAudit.lean`.
- Terminal fixed-count replay: `logs/cubical-controlled-chart-lifting-check1.log`,
  exit 0 at 14:40:38 UTC. The preceding command also checked the separate
  controlled-chart source; it is not part of this one-source origin count.
- Earlier consumer-only and provisional-count failures remain in their logs;
  no production source changed after the successful source check.

Independent review is tracked separately.
