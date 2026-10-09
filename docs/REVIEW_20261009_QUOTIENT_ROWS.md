# Independent review: quotient rows and pointwise arrows

Frozen source manifest: `logs/quotient-rows-sources.sha256`, digest
`80df46547bb8de6634f5c6bcfa88ef979afff41f54843c7d6a9fbdc05710a6db`.

Date: 2026-10-09. Result: **accepted for the frozen eight-source structural boundary**.
No implementation source was changed.

The eight-source boundary is Rows/PointwisePushouts, Basic, RelativePushout,
Pushouts, Structure, Reindex, GridBridge, plus ArrowCategory/Structure.

The full row category retains every natural transformation between original
interval diagrams satisfying diagonal-zero, horizontal-cofibration, and actual
quotient-pushout conditions. Its weak class is pointwise. Its cofibration class
tests every actual horizontal interval-arrow square in the independently
accepted Reedy extension category. The degenerate triple `(i,j,j)` supplies the
component cofibration, including diagonal components. A component cofibration
conclusion is therefore genuinely derived rather than encoded separately.

Only actual Waldhausen pushouts are used. Evaluation-wise colimits of the one
span give functor-category pushouts with their actual component universal
properties; no ambient cocompleteness hypothesis is added. In the new pointwise
pushout arrow, its arrow map is not assumed a cofibration. An actual cobase change
of the original Reedy relative comparison proves this. The quotient condition
for the new row uses the previously proved displayed pushout-interchange
universal property. Zero rows stay zero by an actual pushout leg isomorphism.

The new row pushout has the full-subcategory universal property by full faithful
inclusion. Every other displayed pushout along a row cofibration is pointwise by
comparison with this constructed pushout. Gluing, exact evaluation, and exact
horizontal-arrow restriction then use those actual component squares. Every
ordinal map is allowed in reindexing; all-triples tests reindex literally,
including degeneracies and maps not preserving the initial or final vertex.
Identity/composition and chosen-zero equations are strict. GridBridge identifies
the exact original IsSimplex₂ predicate with these row conditions and the
unchanged vertical weak condition; its independent restriction identity is rfl.

The standalone arrow category instead uses all arrows and componentwise
cofibrations/weak maps. Its component pushouts give the actual arrow pushout, and
any displayed arrow pushout along a componentwise cofibration is proved
pointwise by comparison. Source/target evaluations are genuinely exact.

All statements retain independent object/hom universes and assume only the
actual Waldhausen structure. No exact category, additive or abelian structure,
saturation, extension axiom, cylinder, rowwise equivalence, fibration conclusion,
or realization/K comparison is assumed or established in this boundary.


## Independent verification

All eight frozen sources were rebuilt in manifest order into an isolated overlay.
The actual extension-category dependencies use freshly built artifacts from the
preceding independent core6 review; other unchanged dependencies are linked.
No production artifact was replaced. The checks used Lean 4.34.0, `-j1`, and the
shared slot1 lock with acquisition logging.

`audits/QuotientRowsIndependentAudit.lean` enumerates every defining-module origin,
including private/generated declarations, and recursively runs `collectAxioms`.
The final **fixed96** run passed, allowing only `propext`, `Classical.choice`, and
`Quot.sound`. The eight origin counts are 4, 36, 1, 4, 11, 15, 5 and 20 in source
manifest order. The initial run and the count-frozen final run both passed all
independent consumers without warnings.

Consumers preserve independent category universes; the generic functor-category
pushout consumer additionally uses independent index object/hom universes.
They check actual cofibration/weak predicates, every component cofibration,
genuine exact evaluation/horizontal-arrow restriction, arbitrary displayed
pointwise pushouts, literal reindexing maps and strict identity/composition/zero
equalities, exact agreement with the original IsSimplex₂ predicate, and the
standalone entire-arrow structure. An extra consumer derives the new pushout
arrow's cofibration without assuming it. Another checks pointwise pushout
existence with no arbitrary cocompleteness input. All source hashes matched
before, after the initial audit, and after the fixed-count final run.

## Evidence

Directory: `logs/quotient-rows-independent-20261009/`.
- `sources.sha256`: the exact frozen eight-source manifest and source hashes
- `check.log`: ordered, warning-free fresh source checks
- `deps.log`: selected fresh import resolutions
- `audit.log`, `audit-final.log`: initial and fixed96 recursive audits/consumers
- `hashes-before.log`, `hashes-after.log`, `hashes-final.log`: source rechecks
- `artifacts.sha256`: report, audit, script, logs and fresh artifact hashes

The acquisition and first full-check exit are in
`logs/quotient-rows-independent-session.log`; the final audit records its own
acquisition timestamp. The final source manifest remains
`80df46547bb8de6634f5c6bcfa88ef979afff41f54843c7d6a9fbdc05710a6db`.
