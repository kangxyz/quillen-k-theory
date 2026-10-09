# Genuine quotient-row and pointwise-arrow Waldhausen structures

## Delivered boundary

Eight new modules, frozen by `logs/quotient-rows-sources.sha256`:

- `SConstruction/Rows/PointwisePushouts`
- `SConstruction/Rows/Basic`
- `SConstruction/Rows/RelativePushout`
- `SConstruction/Rows/Pushouts`
- `SConstruction/Rows/Structure`
- `SConstruction/Rows/Reindex`
- `SConstruction/Rows/GridBridge`
- `ArrowCategory/Structure`

Paths are under `Quillen/Waldhausen/`. The source-manifest SHA-256 is
`80df46547bb8de6634f5c6bcfa88ef979afff41f54843c7d6a9fbdc05710a6db`.

## Exact categorical contract

For arbitrary `C : Type u`, `[Category.{v} C]`, and `W : Structure C`,
`QuotientRows.Obj W n` is the full subcategory of the original
`Interval n ⥤ C` consisting of actual S-construction quotient grids. Its
objects have zero diagonal, cofibration horizontal arrows, and genuine
quotient pushout squares. Every natural transformation is a morphism.

`QuotientRows.waldhausenStructure W n` is a proved Waldhausen structure:

- weak equivalences are exactly pointwise `W.weq`;
- cofibrations satisfy the actual source-plus-relative-target condition
  on every horizontal arrow `F[i,j] → F[i,k]`, for every `i ≤ j ≤ k`;
- `cof_app` derives every component cofibration by the degenerate test
  `j = k`, including diagonal quotient objects;
- the chosen zero is the literal constant row on `W.zero`;
- pushouts along these cofibrations exist and all displayed such row
  pushouts are genuine pointwise pushouts;
- the quotient condition on the constructed row follows by actual
  displayed pushout interchange;
- gluing is derived by evaluation and the ambient gluing axiom.

The construction assumes neither global pushouts nor any additive/exact
structure. The auxiliary functor-category pushout lemmas also allow an
arbitrary index category with independent object and hom universes.

`evaluation_exact` is exact at every quotient object. `horizontalArrow_exact`
is exact into the genuine Reedy cofibration-arrow category.
`reindex_exact W α` is exact for every ordinal map `α : m ⟶ n`, without
endpoint-preservation assumptions. Restriction is actual interval
precomposition, preserves the chosen zero literally, and satisfies strict
identity/composition equalities.

`QuotientRows.isSimplex₂_iff` identifies the existing `IsSimplex₂` predicate with
these actual row predicates and the unchanged nerve-direction weak
condition. `gridRestriction_reindex` is the exact independent-grid
restriction equality. This is a predicate and indexing bridge, not a
new realization or fiber comparison.

## Entire arrow category adapter

`ArrowCategory.waldhausenStructure W` is defined on **all** `Arrow C`.
Both its cofibrations and weak equivalences are componentwise. Source
and target are genuinely exact (`source_exact`, `target_exact`).

Actual component pushouts construct arrow pushouts. Conversely, any
arrow pushout along a componentwise cofibration is pointwise, by the
unique isomorphism to the constructed pushout. This is the interface
needed for the concrete joint-cylinder functor. It is separate from
the Reedy structure on the full subcategory of cofibration arrows.

## Verification

All eight source modules have warning-free direct Lean checks. The own
audit `audits/QuotientRowsAudit.lean` recursively checks every declaration
origin in all eight modules against only `propext`, `Classical.choice`,
and `Quot.sound`. It also checks actual map/class/zero/relative-pushout
consumers, arbitrary object/hom universes, all ordinal restrictions, the
old-grid predicate identification, and the entire-arrow adapter.

The fixed audit covers **96 declaration origins** (respectively
4, 36, 1, 4, 11, 15, 5, and 20 in the module order above) and **25 exact
consumer examples**. The final log is `logs/quotient-rows-audit.log`. No `sorry`, new axioms, row exactness assumptions,
or homotopy-theoretic conclusions occur in the source boundary.

## Remaining fibration obligations

This proves the generic row structure and reindexing prerequisite.
The actual relative subcategories of rows, their cylinder/replacement
comparison, and the relative-realization homotopy-fiber theorem remain
separate obligations. Rowwise equivalences alone do not provide the
homotopy-fiber conclusion.
