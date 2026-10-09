# Actual relative quotient-row categories

## Frozen structural boundary

Five modules are frozen in `logs/relative-rows-sources.sha256`:

- `SConstruction/Rows/PostcomposeDetection`
- `Fibration/RelativeRows/{Index,Structure,Reindex,Tail}`

They compile without warnings. `audits/RelativeRowsAudit.lean` recursively checks exactly **76 declaration origins** (2+18+28+11+17), permitting only the standard `propext`, `Classical.choice`, and `Quot.sound` axioms, together with **27 consumers** of original maps, genuine exactness, displayed pushouts, chosen zeros, and strict ordinal identities. Final evidence is `logs/relative-rows-audit-final.log`.

## Actual construction

For `N : NestedWeakEquivalences V`, `RelativeRows.Obj N n` is the full subcategory of the original quotient rows on `[n+1]` whose actual tail quotients `A[i+1,j+1]` are coarse-acyclic. Morphisms are all original natural transformations. Cofibrations are inherited actual all-triples Reedy cofibrations; weak equivalences retain the fine pointwise class.

The inherited zero is the original constant chosen-zero row. Actual pointwise pushouts preserve coarse acyclicity by coarse gluing and the explicitly shared cofibration class. Every arbitrary inherited pushout along a cofibration is proved to be the original ambient-row pushout by comparison with the constructed pushout. Thus `waldhausenStructure` and `forget_exact` require no saturation, extension axiom, cylinder, or assumed row exactness.

`addInitial` is literally `[n] ↦ [n+1]`, fixing the added vertex0 and sending `i+1` to `α(i)+1`. Every original ordinal map has a genuinely exact `reindex N α`, with strict identity, composition, and chosen-zero formulas.

`tailFunctor N n` lifts the original tail diagram into the actual coarse-acyclic category with its inherited fine structure. It is genuinely exact and strictly natural in every outer ordinal map. Cofibration reflection is proved through the actual mapped relative pushouts, using `Rows.PostcomposeDetection`, rather than assumed for functor categories.

`first N n` is the original evaluation `A[0,1]`. It is exact degreewise and is deliberately not asserted to be outer-natural. The genuinely exact `firstTail N n` targets the actual product category `C × Sₙ(Cʷ)`. Its second projection is exactly the original tail functor, and its first projection is exactly this original evaluation.

## Scope and remaining obligations

The structural construction allows independent object and hom universes of the ambient category. It does not assert a cross-universe realization map or an arbitrary product-of-realizations equivalence.

The actual constant split-fiber inclusion, relative-additivity realization equivalence, common-cylinder mixed comparison, and the global connected-row diagonal homotopy-fiber theorem are subsequent proof obligations. In particular, exact rows and degreewise splitting data by themselves are not a homotopy-fiber theorem.
